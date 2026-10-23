"""Auction Room: a live, play-money player auction for 5-10 managers and a projector.

One file. Run:  streamlit run auction_app.py

THREE VIEWS (same app, chosen by the web address)
  ?view=screen   Projector display (read-only, refreshes every second)
  ?view=bid      Manager bidding console (team + PIN login), works on phone or laptop
  ?view=admin    Organiser console (needs ADMIN_PIN), hidden: no link on the home page to it except a small one

SECRETS (Streamlit Cloud -> Settings -> Secrets)
  ADMIN_PIN     = "choose-a-strong-password"       (required for the organiser view)
  SUPABASE_URL  = "https://xxxx.supabase.co"       (optional: saves the auction so a restart cannot lose it)
  SUPABASE_KEY  = "sb_secret_..."                  (optional: the SECRET key, same as the trading game)

OPTIONAL SUPABASE TABLE (run once in the Supabase SQL editor)
  create table if not exists auction_state (
    id text primary key,
    data jsonb not null,
    updated_at timestamptz default now()
  );
  alter table auction_state enable row level security;

RECOMMENDED .streamlit/config.toml (dark theme, makes every widget match the design)
  [theme]
  base = "dark"
  primaryColor = "#D4AF37"
  backgroundColor = "#0B1220"
  secondaryBackgroundColor = "#111A2E"
  textColor = "#E6EAF2"

HOW BIDDING WORKS
  * Money is whole LAKHS (100 lakh = 1 Cr). Shown as Rs 50 L or Rs 1.25 Cr.
  * The organiser brings one player up. Any manager may bid at any time (no turns, no clock),
    but each bid must beat the current one by at least the minimum step. The first bid may equal the base price.
  * A manager can WITHDRAW from a player. When every other manager has withdrawn (or cannot afford
    to top the bid), the player is sold automatically to the highest bidder. If nobody bids, the player goes unsold.
  * Squad rule: a manager must keep a reserve for every empty squad slot, so nobody can spend everything early.
  * Every action runs under one lock, so two managers pressing at the same instant can never corrupt the result.
  * The organiser can call "going once / twice", sell, mark unsold, undo the last bid or the last sale, pause, and back up.
"""
from __future__ import annotations

import copy
import csv
import hashlib
import hmac
import html
import io
import json
import logging
import random
import re
import secrets
import threading
import time
from datetime import datetime, timezone
from zoneinfo import ZoneInfo

import requests
import streamlit as st

st.set_page_config(page_title="Auction Room", page_icon="🔨", layout="wide", initial_sidebar_state="collapsed")
log = logging.getLogger("auction")

# --------------------------------------------------------------------------- settings
EVENT_ID = "main"                  # one auction = one row in the optional database table
IST = ZoneInfo("Asia/Kolkata")
REFRESH_SCREEN = 1.0               # seconds between projector refreshes
REFRESH_BID = 1.5                  # seconds between manager-console refreshes
REFRESH_ADMIN = 2.0
MAX_PIN_TRIES, LOCK_SECONDS = 5, 60
DEFAULTS = {
    "title": "Franchise Owners' Auction",
    "subtitle": "Season 1 · Live Player Auction",
    "purse": 10000,        # lakhs per manager (10000 L = Rs 100 Cr)
    "max_squad": 8,        # players each team may buy
    "step": 25,            # minimum raise, in lakhs
    "reserve": 20,         # lakhs that must stay reserved for each still-empty squad slot
}


# --------------------------------------------------------------------------- small helpers
def e(x) -> str:
    """HTML-escape (also stops Streamlit treating $ as maths)."""
    return html.escape(str(x), quote=True).replace("$", "&#36;")


def money(a) -> str:
    a = int(a)
    if a >= 100:
        return "₹" + f"{a / 100:,.2f}".rstrip("0").rstrip(".") + " Cr"
    return f"₹{a} L"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def clock(ts: str) -> str:
    try:
        return datetime.fromisoformat(ts).astimezone(IST).strftime("%H:%M:%S")
    except Exception:
        return ""


def _secret(name: str) -> str:
    try:
        return str(st.secrets.get(name, "") or "").strip().strip("\"'").strip()
    except Exception:
        return ""


def _hash(pin: str, salt: str) -> str:
    return hashlib.pbkdf2_hmac("sha256", pin.encode(), bytes.fromhex(salt), 60_000).hex()


# --------------------------------------------------------------------------- state + storage
def new_state() -> dict:
    return {"settings": dict(DEFAULTS), "managers": {}, "players": [], "current": None, "last_result": None,
            "sales": [], "log": [], "paused": False, "rev": 0}


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.save_lock = threading.Lock()
        self.state = new_state()
        self.fails: dict[str, list] = {}
        self.admin_fail = [0, 0.0]
        self.sb: tuple[str, str] | None = None
        self.save_msg = "Memory only: scores vanish if the app restarts (add Supabase secrets to persist)."


def _headers(key: str) -> dict:
    h = {"apikey": key, "Content-Type": "application/json"}
    if not key.startswith("sb_"):
        h["Authorization"] = f"Bearer {key}"
    return h


@st.cache_resource
def store() -> Store:
    S = Store()
    url, key = _secret("SUPABASE_URL").rstrip("/"), _secret("SUPABASE_KEY")
    if url.endswith("/rest/v1"):
        url = url[: -len("/rest/v1")]
    if url.startswith("https://") and key:
        S.sb = (url, key)
        try:
            r = requests.get(f"{url}/rest/v1/auction_state", headers=_headers(key),
                             params={"id": f"eq.{EVENT_ID}", "select": "data"}, timeout=10)
            r.raise_for_status()
            rows = r.json()
            if rows and isinstance(rows[0].get("data"), dict) and "managers" in rows[0]["data"]:
                S.state = {**new_state(), **rows[0]["data"]}
            S.save_msg = "Saved to Supabase after every action."
        except Exception as exc:
            S.save_msg = f"Supabase configured but not reachable ({type(exc).__name__}). Running from memory."
    return S


def _save_worker(S: Store) -> None:
    with S.save_lock:   # the last writer always writes the newest state
        with S.lock:
            data = json.loads(json.dumps(S.state))
        try:
            url, key = S.sb
            h = _headers(key)
            h["Prefer"] = "resolution=merge-duplicates,return=minimal"
            r = requests.post(f"{url}/rest/v1/auction_state", headers=h, params={"on_conflict": "id"},
                              json={"id": EVENT_ID, "data": data, "updated_at": now_iso()}, timeout=10)
            r.raise_for_status()
            S.save_msg = f"Saved to Supabase at {datetime.now(IST):%H:%M:%S}."
        except Exception as exc:
            S.save_msg = f"SAVE FAILED ({type(exc).__name__}). The auction continues from memory; export a backup."
            log.warning("save failed: %s", exc)


def act(S: Store, fn, *args):
    """Run one state change under the lock, then save in the background. Returns (ok, message)."""
    with S.lock:
        ok, msg = fn(S.state, *args)
        if ok:
            S.state["rev"] += 1
    if ok and S.sb:
        threading.Thread(target=_save_worker, args=(S,), daemon=True).start()
    return ok, msg


def snap(S: Store) -> dict:
    with S.lock:
        return copy.deepcopy(S.state)


# --------------------------------------------------------------------------- auction rules (pure functions on the state dict)
def _log(s: dict, text: str) -> None:
    s["log"].append({"t": now_iso(), "text": text})
    del s["log"][:-300]


def player_of(s: dict, pid: str) -> dict | None:
    return next((p for p in s["players"] if p["id"] == pid), None)


def min_next(s: dict) -> int:
    cur = s["current"]
    base = player_of(s, cur["pid"])["base"]
    return cur["bid"] + s["settings"]["step"] if cur["bid"] else base


def reserve_after(s: dict, m: dict) -> int:
    """Lakhs a manager must keep back for the squad slots that would still be empty after buying one more player."""
    slots = s["settings"]["max_squad"] - len(m["squad"]) - 1
    return max(0, slots) * s["settings"]["reserve"]


def max_bid(s: dict, m: dict) -> int:
    return m["purse"] - reserve_after(s, m)


def challengers(s: dict) -> list[dict]:
    """Managers who could still raise the current bid."""
    cur = s["current"]
    need = min_next(s)
    return [m for m in s["managers"].values()
            if m["id"] != cur["leader"] and m["id"] not in cur["out"]
            and len(m["squad"]) < s["settings"]["max_squad"] and max_bid(s, m) >= need]


def _finish_sale(s: dict) -> str:
    cur = s["current"]
    p = player_of(s, cur["pid"])
    m = s["managers"][cur["leader"]]
    price = cur["bid"]
    m["purse"] -= price
    m["squad"].append({"pid": p["id"], "name": p["name"], "price": price})
    p.update(status="sold", sold_to=m["id"], price=price)
    s["sales"].append({"pid": p["id"], "mid": m["id"], "price": price, "t": now_iso(), "snapshot": copy.deepcopy(cur)})
    s["last_result"] = {"kind": "sold", "player": p["name"], "origin": p["origin"], "role": p["role"], "base": p["base"],
                        "team": m["team"], "manager": m["name"], "price": price, "t": now_iso()}
    s["current"] = None
    _log(s, f"SOLD {p['name']} to {m['team']} for {money(price)}")
    return f"{p['name']} sold to {m['team']} for {money(price)}."


def _finish_unsold(s: dict) -> str:
    cur = s["current"]
    p = player_of(s, cur["pid"])
    p["status"] = "unsold"
    s["last_result"] = {"kind": "unsold", "player": p["name"], "origin": p["origin"], "role": p["role"],
                        "base": p["base"], "t": now_iso()}
    s["current"] = None
    _log(s, f"UNSOLD {p['name']}")
    return f"{p['name']} went unsold."


def _auto(s: dict) -> str | None:
    cur = s["current"]
    if not cur or s["paused"] or challengers(s):
        return None
    return _finish_sale(s) if cur["bid"] else _finish_unsold(s)


def f_bid(s, mid, amount):
    cur = s["current"]
    m = s["managers"].get(mid)
    if not m:
        return False, "Unknown manager."
    if not cur:
        return False, "No player is up for auction right now."
    if s["paused"]:
        return False, "Bidding is paused by the organiser."
    if mid in cur["out"]:
        return False, "You have withdrawn from this player."
    if len(m["squad"]) >= s["settings"]["max_squad"]:
        return False, "Your squad is full."
    if cur["leader"] == mid:
        return False, "You already hold the highest bid."
    try:
        amount = int(amount)
    except (TypeError, ValueError):
        return False, "Enter a whole number of lakhs."
    need = min_next(s)
    if amount < need:
        return False, f"Too late or too low: the minimum bid is now {money(need)}."
    cap = max_bid(s, m)
    if amount > cap:
        return False, (f"Your limit for this bid is {money(cap)} (purse {money(m['purse'])}, "
                       f"{money(reserve_after(s, m))} reserved for your remaining squad slots).")
    cur["bid"], cur["leader"], cur["call"] = amount, mid, 0
    cur["history"].append({"t": now_iso(), "mid": mid, "amt": amount})
    _log(s, f"BID {m['team']} {money(amount)} on {player_of(s, cur['pid'])['name']}")
    result = _auto(s)
    return True, (f"Bid accepted. {result}" if result else f"Bid of {money(amount)} accepted. You lead.")


def f_out(s, mid):
    cur = s["current"]
    if not cur:
        return False, "No player is up for auction."
    if cur["leader"] == mid:
        return False, "You hold the highest bid, so you cannot withdraw."
    if mid in cur["out"]:
        return False, "You have already withdrawn."
    cur["out"].append(mid)
    _log(s, f"OUT {s['managers'][mid]['team']}")
    result = _auto(s)
    return True, (f"You withdrew. {result}" if result else "You have withdrawn from this player.")


def f_bring(s, pid=None):
    if s["current"]:
        return False, "Finish the current player first."
    pend = [p for p in s["players"] if p["status"] == "pending"]
    p = player_of(s, pid) if pid else (pend[0] if pend else None)
    if not p or p["status"] != "pending":
        return False, "No player left in the queue."
    if not s["managers"]:
        return False, "Add managers first."
    p["status"] = "live"
    s["current"] = {"pid": p["id"], "bid": None, "leader": None, "out": [], "history": [], "call": 0, "opened": now_iso()}
    s["last_result"] = None
    _log(s, f"UP {p['name']}")
    return True, f"{p['name']} is up for auction."


def f_call(s, n):
    cur = s["current"]
    if not cur or not cur["bid"]:
        return False, "There is no bid to call on."
    cur["call"] = n
    return True, "Going once..." if n == 1 else "Going twice..."


def f_sold(s):
    cur = s["current"]
    if not cur or not cur["bid"]:
        return False, "There is no bid to sell on."
    return True, _finish_sale(s)


def f_unsold(s):
    cur = s["current"]
    if not cur:
        return False, "No player is up."
    if cur["bid"]:
        return False, "This player has a bid. Undo the bids first, or use Sold."
    return True, _finish_unsold(s)


def f_undo_bid(s):
    cur = s["current"]
    if not cur or not cur["history"]:
        return False, "No bid to undo."
    cur["history"].pop()
    last = cur["history"][-1] if cur["history"] else None
    cur["bid"], cur["leader"], cur["call"] = (last["amt"], last["mid"], 0) if last else (None, None, 0)
    _log(s, "UNDO last bid")
    return True, "Last bid removed."


def f_undo_sale(s):
    if s["current"]:
        return False, "Finish the current player before undoing a sale."
    if not s["sales"]:
        return False, "No sale to undo."
    sale = s["sales"].pop()
    m, p = s["managers"][sale["mid"]], player_of(s, sale["pid"])
    m["purse"] += sale["price"]
    m["squad"] = [x for x in m["squad"] if x["pid"] != sale["pid"]]
    p.update(status="live", sold_to=None, price=None)
    s["current"], s["last_result"] = sale["snapshot"], None
    _log(s, f"UNDO sale of {p['name']}")
    return True, f"Sale reversed. {p['name']} is live again with the previous bid."


def f_clear_out(s):
    if not s["current"]:
        return False, "No player is up."
    s["current"]["out"] = []
    return True, "All managers are back in for this player."


def f_pause(s, flag):
    s["paused"] = bool(flag)
    _log(s, "PAUSED" if flag else "RESUMED")
    return True, "Bidding paused." if flag else "Bidding resumed."


def f_requeue(s):
    n = 0
    for p in s["players"]:
        if p["status"] == "unsold":
            p["status"] = "pending"
            n += 1
    return (True, f"{n} unsold player(s) back in the queue.") if n else (False, "No unsold players.")


def f_shuffle(s):
    idx = [i for i, p in enumerate(s["players"]) if p["status"] == "pending"]
    items = [s["players"][i] for i in idx]
    random.shuffle(items)
    for i, p in zip(idx, items):
        s["players"][i] = p
    return True, "Queue shuffled."


def f_reset(s):
    cfg = s["settings"]
    for m in s["managers"].values():
        m["purse"], m["squad"] = cfg["purse"], []
    for p in s["players"]:
        p.update(status="pending", sold_to=None, price=None)
    s.update(current=None, last_result=None, sales=[], paused=False)
    _log(s, "AUCTION RESET")
    return True, "Auction reset. All purses restored and all players back in the queue."


def f_settings(s, new):
    s["settings"].update(new)
    if not s["sales"]:
        for m in s["managers"].values():
            m["purse"] = s["settings"]["purse"]
    return True, "Settings saved." + ("" if not s["sales"] else " (Purses unchanged because sales have already happened.)")


def f_add_managers(s, text, replace):
    if s["sales"] or s["current"]:
        return False, "Managers can only be changed before the first player is brought up or sold."
    rows, errs = [], []
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        parts = [x.strip() for x in re.split(r"[,\t]", line)]
        if len(parts) != 3 or not parts[0] or not parts[1] or not re.fullmatch(r"\d{4,8}", parts[2]):
            errs.append(f"Line {n}: use  Team, Manager, PIN  (PIN = 4 to 8 digits)")
        else:
            rows.append(parts)
    if errs:
        return False, " | ".join(errs[:4])
    if not rows:
        return False, "Nothing to add."
    existing = {} if replace else dict(s["managers"])
    teams = {m["team"].lower() for m in existing.values()}
    for t, _, _ in rows:
        if t.lower() in teams:
            return False, f"Duplicate team name: {t}"
        teams.add(t.lower())
    n0 = max([int(k[1:]) for k in existing] or [0])
    for i, (team, name, pin) in enumerate(rows, 1):
        salt = secrets.token_hex(8)
        existing[f"m{n0 + i}"] = {"id": f"m{n0 + i}", "team": team, "name": name, "salt": salt, "pin_hash": _hash(pin, salt),
                                  "purse": s["settings"]["purse"], "squad": []}
    s["managers"] = existing
    return True, f"{len(rows)} manager(s) saved."


def f_add_players(s, text, replace):
    if replace and (s["sales"] or s["current"]):
        return False, "Players can only be replaced before the first player is brought up or sold."
    text = text.strip()
    if not text:
        return False, "Nothing to add."
    dialect = csv.excel_tab if "\t" in text.splitlines()[0] else csv.excel
    reader = csv.DictReader(io.StringIO(text), dialect=dialect)
    pick = lambda row, keys: next((str(v).strip() for k, v in row.items()
                                   if k and k.strip().lower().replace(" ", "_") in keys and v), "")
    rows, errs = [], []
    for n, row in enumerate(reader, 2):
        name = pick(row, {"name", "player", "player_name"})
        base_txt = next((str(v) for k, v in row.items() if k and k.strip().lower().startswith("base") and v), "")
        try:
            base = int(float(re.sub(r"[^\d.]", "", base_txt)))
        except ValueError:
            base = 0
        if not name or base < 1:
            errs.append(f"Row {n}: needs a name and a base_price (in lakhs, e.g. 50)")
            continue
        rows.append({"name": name, "origin": pick(row, {"origin", "from", "city", "hometown", "location", "state"}),
                     "role": pick(row, {"role", "category", "position"}), "base": base})
    if errs:
        return False, " | ".join(errs[:4])
    if not rows:
        return False, "No valid rows found. The first line must be a header: name, origin, role, base_price"
    players = [] if replace else list(s["players"])
    n0 = max([int(p["id"][1:]) for p in players] or [0])
    for i, r in enumerate(rows, 1):
        players.append({"id": f"p{n0 + i}", **r, "status": "pending", "sold_to": None, "price": None})
    s["players"] = players
    return True, f"{len(rows)} player(s) added. Queue now has {sum(p['status'] == 'pending' for p in players)}."


DEMO_PLAYERS = """name,origin,role,base_price
Aarav Sharma,Delhi,Batter,100
Rohan Iyer,Chennai,All-rounder,75
Vikram Singh,Jaipur,Bowler,50
Karthik Menon,Kochi,Wicketkeeper,60
Ishaan Verma,Lucknow,Batter,80
Dev Patel,Ahmedabad,All-rounder,90
Siddharth Rao,Bengaluru,Bowler,40
Aditya Nair,Thiruvananthapuram,Batter,55
Manav Kapoor,Chandigarh,Bowler,65
Yash Deshmukh,Pune,All-rounder,70
Harsh Vardhan,Patna,Wicketkeeper,45
Neel Banerjee,Kolkata,Batter,85
Tanmay Joshi,Indore,Bowler,35
Pranav Reddy,Hyderabad,All-rounder,95
Rahul Choudhary,Jodhpur,Batter,30
Arnav Gupta,Mumbai,Bowler,60"""
DEMO_MANAGERS = "\n".join(f"{t}, {m}, {pin}" for t, m, pin in [
    ("Apex Capital", "Manager One", "1111"), ("Meridian Ventures", "Manager Two", "2222"),
    ("Northwind Holdings", "Manager Three", "3333"), ("Sterling Partners", "Manager Four", "4444"),
    ("Vertex Group", "Manager Five", "5555"), ("Zenith Equity", "Manager Six", "6666")])


def f_demo(s):
    if s["sales"] or s["current"]:
        return False, "Reset the auction first; demo data replaces everything."
    s["managers"], s["players"] = {}, []
    ok1, m1 = f_add_managers(s, DEMO_MANAGERS, True)
    ok2, m2 = f_add_players(s, DEMO_PLAYERS, True)
    return ok1 and ok2, f"Demo loaded. Manager PINs are 1111, 2222 ... 6666. ({m1} {m2})"


def f_restore(s, data):
    if not isinstance(data, dict) or "managers" not in data or "players" not in data:
        return False, "That file is not an auction backup."
    s.clear()
    s.update({**new_state(), **data})
    return True, "Backup restored."


def verify_manager(S: Store, mid: str, pin: str) -> tuple[bool, str]:
    fails = S.fails.setdefault(mid, [0, 0.0])
    if time.time() < fails[1]:
        return False, f"Too many wrong PINs. Try again in {int(fails[1] - time.time()) + 1} seconds."
    with S.lock:
        m = S.state["managers"].get(mid)
        ok = bool(m) and hmac.compare_digest(_hash(pin.strip(), m["salt"]), m["pin_hash"])
    if ok:
        fails[0] = 0
        return True, ""
    fails[0] += 1
    if fails[0] >= MAX_PIN_TRIES:
        fails[0], fails[1] = 0, time.time() + LOCK_SECONDS
        return False, f"Too many wrong PINs. Locked for {LOCK_SECONDS} seconds."
    return False, "Wrong PIN."


# --------------------------------------------------------------------------- design
CSS = """<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');
#MainMenu, footer, header[data-testid="stHeader"], [data-testid="stToolbar"], [data-testid="stDecoration"]{display:none!important}
.stApp{background:radial-gradient(1200px 600px at 10% -10%,#16254A 0%,#0B1220 55%)!important;font-family:'Inter',sans-serif}
.block-container{padding-top:1.1rem!important;max-width:1600px}
.stApp [data-testid="stMarkdownContainer"] p,.stApp [data-testid="stWidgetLabel"] p,.stApp label p,.stApp h1,.stApp h2,.stApp h3,.stApp h4{color:#E6EAF2}
.stApp [data-testid="stCaptionContainer"]{color:#8A96AD}
.stApp input,.stApp textarea{background:#0F1830!important;color:#E6EAF2!important;border-color:#2A3A5E!important}
.stApp .stButton>button,.stApp .stDownloadButton>button,.stApp [data-testid="stFormSubmitButton"]>button{background:#16213C;color:#E6EAF2;border:1px solid #2A3A5E;border-radius:10px;font-weight:600;padding:.55rem 1rem}
.stApp .stButton>button:hover{border-color:#D4AF37;color:#fff}
.stApp .stButton>button[kind="primary"],.stApp [data-testid="stFormSubmitButton"]>button[kind="primaryFormSubmit"]{background:linear-gradient(180deg,#E6C25A,#C9A227);color:#14110A;border:0;font-weight:800}
.stApp .stButton>button:disabled{opacity:.35}
.stApp [data-baseweb="tab-list"]{gap:6px}
.stApp [data-testid="stExpander"]{border:1px solid #1F2D4D;border-radius:12px;background:#0F1830}
.au{font-family:'Inter',sans-serif;color:#E6EAF2}
.au *{box-sizing:border-box}
.au-top{display:flex;justify-content:space-between;align-items:center;gap:12px;padding:14px 24px;border-radius:16px;background:linear-gradient(90deg,#0F1B38,#15264F);border:1px solid #22325A;margin-bottom:16px}
.au-brand{font-weight:800;font-size:1.3rem;letter-spacing:.03em;color:#F3F5FA}
.au-brand b{color:#D4AF37}
.au-sub{font-size:.72rem;color:#8A96AD;letter-spacing:.16em;text-transform:uppercase;margin-top:2px}
.au-pill{display:inline-block;padding:6px 14px;border-radius:999px;font-size:.72rem;font-weight:800;letter-spacing:.16em;margin-left:8px}
.au-live{background:rgba(52,211,153,.12);color:#34D399;border:1px solid rgba(52,211,153,.45)}
.au-live:before{content:"";display:inline-block;width:8px;height:8px;border-radius:50%;background:#34D399;margin-right:8px;animation:aupulse 1.2s infinite}
.au-paused{background:rgba(251,191,36,.12);color:#FBBF24;border:1px solid rgba(251,191,36,.45)}
.au-idle{background:rgba(138,150,173,.12);color:#A9B4CB;border:1px solid rgba(138,150,173,.35)}
@keyframes aupulse{0%{opacity:1}50%{opacity:.25}100%{opacity:1}}
@keyframes auglow{0%{box-shadow:0 0 0 rgba(212,175,55,0)}50%{box-shadow:0 0 46px rgba(212,175,55,.35)}100%{box-shadow:0 0 0 rgba(212,175,55,0)}}
.au-card{background:#101A31;border:1px solid #1F2D4D;border-radius:18px;padding:24px 28px;margin-bottom:16px}
.au-hero{background:radial-gradient(900px 320px at 0% 0%,#1A2B55 0%,#101A31 60%)}
.au-kicker{font-size:.74rem;font-weight:700;letter-spacing:.22em;color:#D4AF37;text-transform:uppercase}
.au-tag{display:inline-block;margin-top:14px;padding:5px 12px;border-radius:8px;background:rgba(212,175,55,.12);border:1px solid rgba(212,175,55,.4);color:#E6C25A;font-size:.74rem;font-weight:700;letter-spacing:.14em;text-transform:uppercase}
.au-pname{font-size:3.5rem;font-weight:800;line-height:1.05;margin-top:10px;color:#F6F8FC}
.au-meta{font-size:1.2rem;color:#A9B4CB;margin-top:8px}
.au-grid{display:grid;grid-template-columns:1fr 1.3fr 1.3fr;gap:20px;margin-top:26px;padding-top:22px;border-top:1px solid #22325A}
.au-lbl{font-size:.68rem;letter-spacing:.16em;color:#8A96AD;text-transform:uppercase;font-weight:600}
.au-val{font-size:1.7rem;font-weight:700;margin-top:4px;font-variant-numeric:tabular-nums;color:#F6F8FC}
.au-bid{font-size:3.3rem;font-weight:800;line-height:1.05;margin-top:2px;color:#E6C25A;font-variant-numeric:tabular-nums}
.au-lead{font-size:1.6rem;font-weight:700;margin-top:4px;color:#F6F8FC}
.au-small{font-size:.95rem;color:#8A96AD;margin-top:2px}
.au-muted{color:#6F7C96}
.au-call{margin-top:20px;padding:14px;text-align:center;font-weight:800;font-size:1.3rem;letter-spacing:.34em;border-radius:12px;background:rgba(248,113,113,.12);color:#F87171;border:1px solid rgba(248,113,113,.45)}
.au-compact .au-pname{font-size:2.2rem}.au-compact .au-bid{font-size:2.2rem}.au-compact .au-meta{font-size:1rem}
.au-compact .au-val,.au-compact .au-lead{font-size:1.25rem}.au-compact.au-card{padding:18px 20px}
.au-compact .au-grid{margin-top:16px;padding-top:14px;gap:12px}
.au-sec{font-size:.72rem;font-weight:700;letter-spacing:.2em;color:#8A96AD;text-transform:uppercase;margin:2px 0 12px}
.au-tbl{width:100%;border-collapse:collapse}
.au-tbl th{text-align:left;font-size:.66rem;letter-spacing:.16em;color:#6F7C96;text-transform:uppercase;font-weight:600;padding:6px 8px;border-bottom:1px solid #22325A}
.au-tbl td{padding:11px 8px;border-bottom:1px solid #18253F;font-size:.98rem;vertical-align:middle;font-variant-numeric:tabular-nums;color:#E6EAF2}
.au-tbl th.r,.au-tbl td.r{text-align:right}
.au-tbl tr.lead td{background:rgba(212,175,55,.07)}
.au-tbl .tm{font-weight:700}.au-tbl .mg{font-size:.8rem;color:#8A96AD}
.au-bar{height:5px;border-radius:3px;background:#1B2845;margin-top:6px;overflow:hidden}
.au-bar i{display:block;height:100%;background:linear-gradient(90deg,#C9A227,#E6C25A)}
.au-chip{display:inline-block;padding:3px 10px;border-radius:999px;font-size:.66rem;font-weight:800;letter-spacing:.12em}
.au-c-lead{background:#D4AF37;color:#14110A}.au-c-in{background:rgba(52,211,153,.14);color:#34D399}
.au-c-out{background:rgba(248,113,113,.14);color:#F87171}.au-c-full{background:rgba(138,150,173,.16);color:#A9B4CB}
.au-sold{text-align:center;padding:48px 28px;animation:auglow 2.4s infinite;border-color:#6B5A1E;background:radial-gradient(800px 300px at 50% 0%,#2A2410 0%,#101A31 70%)}
.au-stamp{font-size:1.1rem;font-weight:800;letter-spacing:.5em;color:#D4AF37}
.au-big{font-size:4.2rem;font-weight:800;color:#F6F8FC;line-height:1.05;margin-top:14px}
.au-price{font-size:3rem;font-weight:800;color:#E6C25A;margin-top:14px}
.au-stats{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-bottom:14px}
.au-stat{background:#101A31;border:1px solid #1F2D4D;border-radius:14px;padding:14px 16px}
.au-stat .au-val{font-size:1.35rem}
.au-note{padding:12px 16px;border-radius:12px;font-weight:600;margin:8px 0}
.au-n-ok{background:rgba(52,211,153,.1);border:1px solid rgba(52,211,153,.4);color:#34D399}
.au-n-warn{background:rgba(251,191,36,.1);border:1px solid rgba(251,191,36,.4);color:#FBBF24}
.au-n-bad{background:rgba(248,113,113,.1);border:1px solid rgba(248,113,113,.4);color:#F87171}
.au-foot{display:flex;gap:28px;flex-wrap:wrap;justify-content:center;color:#8A96AD;font-size:.85rem;letter-spacing:.06em;margin-top:6px}
.au-foot b{color:#E6EAF2}
.au-home{display:grid;grid-template-columns:repeat(3,1fr);gap:18px;margin-top:10px}
.au-home a{display:block;text-decoration:none;background:#101A31;border:1px solid #1F2D4D;border-radius:18px;padding:26px;color:#E6EAF2;transition:all .15s}
.au-home a:hover{border-color:#D4AF37;transform:translateY(-3px)}
.au-home .h{font-size:1.25rem;font-weight:800;margin-bottom:6px;color:#F6F8FC}
.au-home .d{color:#8A96AD;font-size:.95rem;line-height:1.45}
@media(max-width:900px){.au-pname{font-size:2.1rem}.au-bid{font-size:2.2rem}.au-grid{grid-template-columns:1fr 1fr}.au-stats{grid-template-columns:1fr 1fr}.au-home{grid-template-columns:1fr}.au-big{font-size:2.4rem}.au-price{font-size:2rem}}
</style>"""


def inject() -> None:
    st.markdown(CSS, unsafe_allow_html=True)


def html_block(markup: str) -> None:
    st.markdown(markup.replace("\n", ""), unsafe_allow_html=True)


def topbar(s: dict, right: str = "") -> None:
    cfg = s["settings"]
    if s["paused"]:
        pill = '<span class="au-pill au-paused">PAUSED</span>'
    elif s["current"]:
        pill = '<span class="au-pill au-live">LIVE</span>'
    else:
        pill = '<span class="au-pill au-idle">STANDBY</span>'
    html_block(f'<div class="au"><div class="au-top"><div><div class="au-brand">{e(cfg["title"])}</div>'
               f'<div class="au-sub">{e(cfg["subtitle"])}</div></div><div>{right}{pill}</div></div></div>')


def hero_html(s: dict, compact: bool = False) -> str:
    cur = s["current"]
    p = player_of(s, cur["pid"])
    lot = [x["id"] for x in s["players"]].index(p["id"]) + 1
    leader = s["managers"].get(cur["leader"]) if cur["leader"] else None
    bid = (f'<div class="au-bid">{money(cur["bid"])}</div>' if cur["bid"]
           else '<div class="au-bid au-muted" style="font-size:2rem">No bids yet</div>')
    lead = (f'<div class="au-lead">{e(leader["team"])}</div><div class="au-small">{e(leader["name"])}</div>' if leader
            else '<div class="au-lead au-muted">Awaiting opening bid</div>')
    call = {1: "GOING ONCE", 2: "GOING TWICE"}.get(cur["call"], "")
    call_html = f'<div class="au-call">{call}</div>' if call else ""
    origin = f'<div class="au-meta">From {e(p["origin"])}</div>' if p["origin"] else ""
    tag = f'<div class="au-tag">{e(p["role"])}</div>' if p["role"] else ""
    return (f'<div class="au au-card au-hero{" au-compact" if compact else ""}"><div class="au-kicker">Now on the block · '
            f'Lot {lot} of {len(s["players"])}</div>{tag}<div class="au-pname">{e(p["name"])}</div>{origin}'
            f'<div class="au-grid"><div><div class="au-lbl">Base price</div><div class="au-val">{money(p["base"])}</div></div>'
            f'<div><div class="au-lbl">Current bid</div>{bid}</div><div><div class="au-lbl">Leading</div>{lead}</div></div>'
            f'{call_html}</div>')


def history_html(s: dict, n: int = 6) -> str:
    cur = s["current"]
    if not cur or not cur["history"]:
        return ""
    rows = "".join(f'<tr><td>{clock(h["t"])}</td><td class="tm">{e(s["managers"][h["mid"]]["team"])}</td>'
                   f'<td class="r">{money(h["amt"])}</td></tr>' for h in reversed(cur["history"][-n:]))
    return (f'<div class="au au-card"><div class="au-sec">Bid history</div><table class="au-tbl"><thead><tr><th>Time</th>'
            f'<th>Team</th><th class="r">Bid</th></tr></thead><tbody>{rows}</tbody></table></div>')


def idle_html(s: dict) -> str:
    lr = s["last_result"]
    if lr and lr["kind"] == "sold":
        body = (f'<div class="au au-card au-sold"><div class="au-stamp">SOLD</div><div class="au-big">{e(lr["player"])}</div>'
                f'<div class="au-meta">{e(lr["role"])}{" · " if lr["role"] and lr["origin"] else ""}{e(lr["origin"])}</div>'
                f'<div class="au-price">{money(lr["price"])}</div>'
                f'<div class="au-lead" style="margin-top:12px">{e(lr["team"])}</div><div class="au-small">{e(lr["manager"])}</div></div>')
    elif lr:
        body = (f'<div class="au au-card" style="text-align:center;padding:48px"><div class="au-stamp" style="color:#8A96AD">UNSOLD</div>'
                f'<div class="au-big" style="color:#A9B4CB">{e(lr["player"])}</div>'
                f'<div class="au-meta">Base price {money(lr["base"])} · no takers</div></div>')
    else:
        started = any(p["status"] != "pending" for p in s["players"])
        msg = "Next lot coming up" if started else "The auction will begin shortly"
        body = (f'<div class="au au-card" style="text-align:center;padding:60px"><div class="au-stamp">{msg.upper()}</div>'
                f'<div class="au-meta" style="margin-top:14px">{len(s["managers"])} managers · {len(s["players"])} players</div></div>')
    nxt = [p for p in s["players"] if p["status"] == "pending"][:3]
    if nxt:
        rows = "".join(f'<tr><td class="tm">{e(p["name"])}</td><td>{e(p["role"])}</td><td>{e(p["origin"])}</td>'
                       f'<td class="r">{money(p["base"])}</td></tr>' for p in nxt)
        body += (f'<div class="au au-card"><div class="au-sec">Up next</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>')
    return body


def board_html(s: dict) -> str:
    cur, cfg = s["current"], s["settings"]
    rows = ""
    for m in s["managers"].values():
        full = len(m["squad"]) >= cfg["max_squad"]
        chip, cls = "", ""
        if cur:
            if m["id"] == cur["leader"]:
                chip, cls = '<span class="au-chip au-c-lead">LEADING</span>', "lead"
            elif m["id"] in cur["out"]:
                chip = '<span class="au-chip au-c-out">OUT</span>'
            elif full:
                chip = '<span class="au-chip au-c-full">FULL</span>'
            elif max_bid(s, m) < min_next(s):
                chip = '<span class="au-chip au-c-full">LIMIT</span>'
            else:
                chip = '<span class="au-chip au-c-in">IN</span>'
        elif full:
            chip = '<span class="au-chip au-c-full">FULL</span>'
        pct = max(0, min(100, m["purse"] / max(1, cfg["purse"]) * 100))
        rows += (f'<tr class="{cls}"><td><div class="tm">{e(m["team"])}</div><div class="mg">{e(m["name"])}</div></td>'
                 f'<td class="r">{money(m["purse"])}<div class="au-bar"><i style="width:{pct:.0f}%"></i></div></td>'
                 f'<td class="r">{len(m["squad"])}/{cfg["max_squad"]}</td><td class="r">{chip}</td></tr>')
    return (f'<div class="au au-card"><div class="au-sec">Team purses</div><table class="au-tbl"><thead><tr><th>Team</th>'
            f'<th class="r">Purse left</th><th class="r">Squad</th><th class="r">Status</th></tr></thead><tbody>{rows}</tbody></table></div>')


def recent_html(s: dict, n: int = 5) -> str:
    sold = [x for x in reversed(s["sales"])][:n]
    if not sold:
        return ""
    rows = ""
    for x in sold:
        p, m = player_of(s, x["pid"]), s["managers"][x["mid"]]
        rows += (f'<tr><td class="tm">{e(p["name"])}</td><td>{e(m["team"])}</td><td class="r">{money(x["price"])}</td></tr>')
    return f'<div class="au au-card"><div class="au-sec">Recently sold</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>'


def footer_html(s: dict) -> str:
    pl = s["players"]
    sold = sum(p["status"] == "sold" for p in pl)
    uns = sum(p["status"] == "unsold" for p in pl)
    pend = sum(p["status"] in ("pending", "live") for p in pl)
    spent = sum(x["price"] for x in s["sales"])
    return (f'<div class="au au-foot"><span>Sold <b>{sold}</b></span><span>Unsold <b>{uns}</b></span>'
            f'<span>Remaining <b>{pend}</b></span><span>Total spent <b>{money(spent)}</b></span></div>')


def flash_show() -> None:
    f = st.session_state.get("au_flash")
    if f and time.time() - f[2] < 7:
        html_block(f'<div class="au"><div class="au-note {"au-n-ok" if f[0] else "au-n-bad"}">{e(f[1])}</div></div>')


def flash_set(res) -> None:
    st.session_state["au_flash"] = (res[0], res[1], time.time())


# --------------------------------------------------------------------------- views
def view_home() -> None:
    S = store()
    s = snap(S)
    topbar(s)
    html_block('<div class="au"><div class="au-home">'
               '<a href="?view=screen" target="_self"><div class="h">Projector screen</div><div class="d">The live display for the room: '
               'current player, bids, team purses and results. Open full screen on the projector.</div></a>'
               '<a href="?view=bid" target="_self"><div class="h">Manager console</div><div class="d">Managers sign in with their '
               'team and PIN to bid or withdraw, from a laptop or phone.</div></a>'
               '<a href="?view=admin" target="_self"><div class="h">Organiser</div><div class="d">Set up teams and players, '
               'bring each player up, call the sale, undo and back up. Password protected.</div></a></div></div>')


@st.fragment(run_every=REFRESH_SCREEN)
def screen_live(S: Store) -> None:
    s = snap(S)
    topbar(s)
    left, right = st.columns([1.65, 1], gap="large")
    with left:
        if s["current"]:
            html_block(hero_html(s) + history_html(s))
        else:
            html_block(idle_html(s))
    with right:
        html_block(board_html(s) + recent_html(s))
    html_block(footer_html(s))


def view_screen() -> None:
    screen_live(store())


@st.fragment(run_every=REFRESH_BID)
def bid_console(S: Store, mid: str) -> None:
    ss = st.session_state
    s = snap(S)
    m = s["managers"].get(mid)
    if not m:
        ss.pop("au_mid", None)
        st.rerun()
        return
    cfg, cur = s["settings"], s["current"]
    topbar(s, f'<span class="au-small" style="margin-right:6px">{e(m["team"])} · {e(m["name"])}</span>')
    flash_show()
    cap = max_bid(s, m)
    html_block(f'<div class="au"><div class="au-stats">'
               f'<div class="au-stat"><div class="au-lbl">Purse left</div><div class="au-val">{money(m["purse"])}</div></div>'
               f'<div class="au-stat"><div class="au-lbl">Max bid now</div><div class="au-val">{money(max(cap, 0))}</div></div>'
               f'<div class="au-stat"><div class="au-lbl">Squad</div><div class="au-val">{len(m["squad"])}/{cfg["max_squad"]}</div></div>'
               f'<div class="au-stat"><div class="au-lbl">Min step</div><div class="au-val">{money(cfg["step"])}</div></div></div></div>')
    if not cur:
        html_block(idle_html(s))
    else:
        html_block(hero_html(s, compact=True))
        pid, need = cur["pid"], min_next(s)
        notes = []
        if s["paused"]:
            notes.append(("warn", "Bidding is paused by the organiser."))
        if cur["leader"] == mid:
            notes.append(("ok", "You hold the highest bid. Waiting for other managers."))
        if mid in cur["out"]:
            notes.append(("bad", "You have withdrawn from this player."))
        if len(m["squad"]) >= cfg["max_squad"]:
            notes.append(("warn", "Your squad is full."))
        for kind, text in notes:
            html_block(f'<div class="au"><div class="au-note au-n-{kind}">{e(text)}</div></div>')
        can = (not s["paused"] and cur["leader"] != mid and mid not in cur["out"] and len(m["squad"]) < cfg["max_squad"])
        if can:
            st.markdown("**Place a bid**")
            amounts = [need, need + cfg["step"], need + 2 * cfg["step"], need + 4 * cfg["step"]]
            cols = st.columns(4)
            for i, (col, a) in enumerate(zip(cols, amounts)):
                if col.button(money(a), key=f"q{pid}_{a}", type="primary" if i == 0 else "secondary",
                              disabled=a > cap, use_container_width=True):
                    flash_set(act(S, f_bid, mid, a))
                    st.rerun(scope="fragment")
            with st.expander("Custom amount"):
                with st.form(f"cust_{pid}", border=False):
                    amt = st.number_input("Your bid in lakhs (100 lakh = 1 Cr)", min_value=0, step=cfg["step"], value=need, format="%d")
                    if st.form_submit_button("Place custom bid", type="primary"):
                        flash_set(act(S, f_bid, mid, amt))
                        st.rerun(scope="fragment")
            ckey = f"au_conf_{pid}"
            if ss.get(ckey):
                st.markdown('<div class="au"><div class="au-note au-n-warn">Withdraw from this player? You cannot re-enter unless the organiser lets you back in.</div></div>',
                            unsafe_allow_html=True)
                c1, c2 = st.columns(2)
                if c1.button("Yes, withdraw", key=f"y{pid}", use_container_width=True):
                    ss[ckey] = False
                    flash_set(act(S, f_out, mid))
                    st.rerun(scope="fragment")
                if c2.button("Cancel", key=f"n{pid}", use_container_width=True):
                    ss[ckey] = False
                    st.rerun(scope="fragment")
            elif st.button("Withdraw from this player", key=f"w{pid}", use_container_width=True):
                ss[ckey] = True
                st.rerun(scope="fragment")
        html_block(history_html(s, 4))
    if m["squad"]:
        rows = "".join(f'<tr><td class="tm">{e(x["name"])}</td><td class="r">{money(x["price"])}</td></tr>' for x in m["squad"])
        html_block(f'<div class="au au-card"><div class="au-sec">Your squad</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>')


def view_bid() -> None:
    S, ss = store(), st.session_state
    s = snap(S)
    mid = ss.get("au_mid")
    if mid and mid in s["managers"]:
        bid_console(S, mid)
        if st.button("Log out", key="au_logout"):
            ss.pop("au_mid", None)
            st.rerun()
        return
    topbar(s)
    if not s["managers"]:
        st.info("The organiser has not added any teams yet.")
        return
    _, mid_col, _ = st.columns([1, 1.2, 1])
    with mid_col:
        with st.form("au_login"):
            teams = {m["id"]: f'{m["team"]} ({m["name"]})' for m in s["managers"].values()}
            pick = st.selectbox("Your team", list(teams), format_func=lambda k: teams[k])
            pin = st.text_input("PIN", type="password", max_chars=8)
            if st.form_submit_button("Enter auction room", type="primary"):
                ok, err = verify_manager(S, pick, pin)
                if ok:
                    ss["au_mid"] = pick
                    st.rerun()
                st.error(err)


@st.fragment(run_every=REFRESH_ADMIN)
def admin_live(S: Store) -> None:
    s = snap(S)
    cur = s["current"]
    flash_show()
    if cur:
        html_block(hero_html(s, compact=True))
        c = st.columns(4)
        if c[0].button("Going once", use_container_width=True, disabled=not cur["bid"]):
            flash_set(act(S, f_call, 1)); st.rerun(scope="fragment")
        if c[1].button("Going twice", use_container_width=True, disabled=not cur["bid"]):
            flash_set(act(S, f_call, 2)); st.rerun(scope="fragment")
        if c[2].button("SOLD", type="primary", use_container_width=True, disabled=not cur["bid"]):
            flash_set(act(S, f_sold)); st.rerun(scope="fragment")
        if c[3].button("Mark unsold", use_container_width=True, disabled=bool(cur["bid"])):
            flash_set(act(S, f_unsold)); st.rerun(scope="fragment")
        c = st.columns(3)
        if c[0].button("Undo last bid", use_container_width=True, disabled=not cur["history"]):
            flash_set(act(S, f_undo_bid)); st.rerun(scope="fragment")
        if c[1].button("Let everyone back in", use_container_width=True, disabled=not cur["out"]):
            flash_set(act(S, f_clear_out)); st.rerun(scope="fragment")
        if c[2].button("Resume bidding" if s["paused"] else "Pause bidding", use_container_width=True):
            flash_set(act(S, f_pause, not s["paused"])); st.rerun(scope="fragment")
        html_block(history_html(s, 5))
    else:
        html_block(idle_html(s))
        pend = [p for p in s["players"] if p["status"] == "pending"]
        opts = {"": "Next in queue (automatic)", **{p["id"]: f'{p["name"]} · {money(p["base"])}' for p in pend}}
        pick = st.selectbox("Bring up", list(opts), format_func=lambda k: opts[k], key="adm_pick")
        c = st.columns(3)
        if c[0].button("Bring up player", type="primary", use_container_width=True, disabled=not pend):
            flash_set(act(S, f_bring, pick or None)); st.rerun(scope="fragment")
        if c[1].button("Shuffle queue", use_container_width=True, disabled=len(pend) < 2):
            flash_set(act(S, f_shuffle)); st.rerun(scope="fragment")
        if c[2].button("Re-queue unsold", use_container_width=True):
            flash_set(act(S, f_requeue)); st.rerun(scope="fragment")
    st.divider()
    c = st.columns(2)
    if c[0].button("Undo last sale", use_container_width=True, disabled=bool(cur) or not s["sales"]):
        flash_set(act(S, f_undo_sale)); st.rerun(scope="fragment")
    c[1].caption(S.save_msg)
    html_block(board_html(s))


def view_admin() -> None:
    S, ss = store(), st.session_state
    pin = _secret("ADMIN_PIN")
    s = snap(S)
    topbar(s, '<span class="au-small" style="margin-right:6px">Organiser</span>')
    if not pin:
        st.error("ADMIN_PIN is not set. Add it in the app's Secrets (Streamlit Cloud: Settings, Secrets).")
        return
    if not ss.get("au_admin"):
        _, col, _ = st.columns([1, 1.2, 1])
        with col, st.form("au_admin_login"):
            pw = st.text_input("Organiser password", type="password")
            if st.form_submit_button("Sign in", type="primary"):
                fail = S.admin_fail
                if time.time() < fail[1]:
                    st.error("Too many wrong attempts. Wait a minute.")
                elif hmac.compare_digest(pw.encode(), pin.encode()):
                    fail[0] = 0
                    ss["au_admin"] = True
                    st.rerun()
                else:
                    fail[0] += 1
                    if fail[0] >= 5:
                        fail[0], fail[1] = 0, time.time() + 60
                    st.error("Wrong password.")
        return
    live_tab, setup_tab, result_tab = st.tabs(["Live control", "Setup", "Results & backup"])
    with live_tab:
        admin_live(S)
    with setup_tab:
        cfg = s["settings"]
        locked = bool(s["sales"] or s["current"])
        st.markdown("#### Auction settings")
        with st.form("au_settings"):
            c = st.columns(2)
            title = c[0].text_input("Title", cfg["title"])
            sub = c[1].text_input("Subtitle", cfg["subtitle"])
            c = st.columns(4)
            purse = c[0].number_input("Purse per team (lakhs)", 100, 1_000_000, cfg["purse"], 100)
            squad = c[1].number_input("Max squad size", 1, 50, cfg["max_squad"])
            step = c[2].number_input("Minimum bid step (lakhs)", 1, 10_000, cfg["step"])
            res = c[3].number_input("Reserve per empty slot (lakhs)", 0, 10_000, cfg["reserve"])
            if st.form_submit_button("Save settings", type="primary"):
                flash_set(act(S, f_settings, {"title": title, "subtitle": sub, "purse": int(purse), "max_squad": int(squad),
                                              "step": int(step), "reserve": int(res)}))
                st.rerun()
        flash_show()
        st.caption("Money is in lakhs: 100 lakh = 1 Cr. Purse 10000 = Rs 100 Cr. Changing the purse after sales have started does not change existing purses.")
        st.markdown("#### Managers (teams)")
        if s["managers"]:
            html_block('<div class="au au-card"><table class="au-tbl"><thead><tr><th>Team</th><th>Manager</th><th class="r">Purse</th></tr></thead><tbody>'
                       + "".join(f'<tr><td class="tm">{e(m["team"])}</td><td>{e(m["name"])}</td><td class="r">{money(m["purse"])}</td></tr>'
                                 for m in s["managers"].values()) + "</tbody></table></div>")
        with st.form("au_mgr"):
            txt = st.text_area("One manager per line:  Team name, Manager name, PIN (4 to 8 digits)", height=120,
                               placeholder="Apex Capital, Ravi Kumar, 4821")
            rep = st.checkbox("Replace all existing managers", disabled=locked)
            if st.form_submit_button("Save managers", type="primary"):
                flash_set(act(S, f_add_managers, txt, rep))
                st.rerun()
        st.markdown("#### Players")
        pend = sum(p["status"] == "pending" for p in s["players"])
        st.caption(f"{len(s['players'])} players loaded, {pend} waiting. Columns: name, origin, role, base_price (lakhs).")
        up = st.file_uploader("Upload CSV", type=["csv", "txt"], key="au_csv")
        txt = st.text_area("...or paste rows (with the header line)", height=120, placeholder="name,origin,role,base_price\nAarav Sharma,Delhi,Batter,100")
        rep = st.checkbox("Replace all existing players", disabled=locked, key="au_prep")
        c = st.columns(3)
        if c[0].button("Add players", type="primary", use_container_width=True):
            data = up.getvalue().decode("utf-8-sig", errors="ignore") if up else txt
            flash_set(act(S, f_add_players, data, rep))
            st.rerun()
        c[1].download_button("CSV template", "name,origin,role,base_price\nAarav Sharma,Delhi,Batter,100\n", "players_template.csv",
                             use_container_width=True)
        if c[2].button("Load demo data", use_container_width=True, disabled=locked):
            flash_set(act(S, f_demo))
            st.rerun()
        st.markdown("#### Danger zone")
        sure = st.checkbox("I understand this resets all purses, squads and sales", key="au_sure")
        if st.button("Reset auction", disabled=not sure):
            flash_set(act(S, f_reset))
            st.rerun()
        if st.button("Sign out of organiser"):
            ss.pop("au_admin", None)
            st.rerun()
    with result_tab:
        st.markdown("#### Squads")
        for m in s["managers"].values():
            spent = sum(x["price"] for x in m["squad"])
            rows = "".join(f'<tr><td>{e(x["name"])}</td><td class="r">{money(x["price"])}</td></tr>' for x in m["squad"]) or \
                '<tr><td class="au-muted">No players yet</td><td></td></tr>'
            html_block(f'<div class="au au-card"><div class="au-sec">{e(m["team"])} · {e(m["name"])} · spent {money(spent)} · left {money(m["purse"])}</div>'
                       f'<table class="au-tbl"><tbody>{rows}</tbody></table></div>')
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["lot", "player", "origin", "role", "base_lakhs", "team", "manager", "price_lakhs"])
        for i, x in enumerate(s["sales"], 1):
            p, m = player_of(s, x["pid"]), s["managers"][x["mid"]]
            w.writerow([i, p["name"], p["origin"], p["role"], p["base"], m["team"], m["name"], x["price"]])
        c = st.columns(2)
        c[0].download_button("Download sales (CSV)", buf.getvalue(), "auction_sales.csv", use_container_width=True)
        c[1].download_button("Download full backup (JSON)", json.dumps(s, indent=1), "auction_backup.json", use_container_width=True)
        up = st.file_uploader("Restore from a backup file", type=["json"], key="au_restore")
        if up and st.button("Restore this backup"):
            try:
                flash_set(act(S, f_restore, json.loads(up.getvalue().decode("utf-8"))))
            except ValueError:
                flash_set((False, "That file is not valid JSON.", 0))
            st.rerun()
        with st.expander("Activity log"):
            for entry in reversed(s["log"][-60:]):
                st.text(f'{clock(entry["t"])}  {entry["text"]}')


def main() -> None:
    inject()
    view = str(st.query_params.get("view", "") or "").lower()
    {"screen": view_screen, "bid": view_bid, "admin": view_admin}.get(view, view_home)()


main()
