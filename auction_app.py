"""Intellics Auction Room v2: a live, play-money player auction (5-10 managers + projector).

Run:  streamlit run auction_app.py

VIEWS (same app, chosen by the web address)
  ?view=screen   Projector display (read-only, no login, shows no secrets)
  ?view=bid      Manager console (team + PIN login)
  ?view=admin    Organiser control room (ADMIN_PIN secret)

ARCHITECTURE (read this once)
  * PostgreSQL (Supabase) is the ONLY source of truth. The app keeps no authoritative state in memory.
  * Every change is: read latest state + revision -> apply the rule function -> validate all invariants ->
    call the database function auction_commit(expected_rev, new_state, idempotency_key).
    The database locks the row, rejects the commit if the revision moved (another change won), and refuses
    a repeated idempotency key (so a network retry can never charge a team or sell a player twice).
    On a revision conflict the app re-reads the newest state and re-applies the SAME rule function, so a late bid
    is simply re-validated against reality (accepted if still legal, rejected with a clear reason if not).
  * Nothing is shown as accepted until the database confirms the commit.
  * If Supabase is configured but unreachable the app goes read-only. It never falls back to memory.
  * With NO Supabase secrets the app runs in a clearly labelled DEMO mode (memory only, lost on restart).
  * Roles are enforced in apply_action() on the server: every mutation is checked against the latest state
    (manager exists, session token still current). Browsers never send a manager id; it comes from the
    server-side Streamlit session.
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
from functools import lru_cache
from pathlib import Path
import random
import re
import secrets
import threading
import time
import uuid
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone

import requests

try:
    import streamlit as st
except ImportError:  # lets the rule engine be unit-tested without Streamlit installed
    from unittest import mock

    st = mock.MagicMock()

try:
    from zoneinfo import ZoneInfo

    IST = ZoneInfo("Asia/Kolkata")
except Exception:  # pragma: no cover
    IST = timezone(timedelta(hours=5, minutes=30))

log = logging.getLogger("auction")

# --------------------------------------------------------------------------- constants
EVENT_ID = "main"
SCHEMA = 2
POLL_SCREEN, POLL_BID, POLL_ADMIN = 1.5, 1.5, 2.0
STORE_MIN_INTERVAL = 0.6          # at most ~2 database revision checks per second per server process
MANAGER_SESSION_SECONDS = 8 * 3600
ADMIN_IDLE_SECONDS, ADMIN_MAX_SECONDS = 90 * 60, 12 * 3600
PIN_MAX_FAILS, PIN_LOCK_SECONDS = 5, 120
ADMIN_MAX_FAILS, ADMIN_LOCK_SECONDS = 5, 300
PBKDF2_ITER = 200_000
MAX_STATE_BYTES = 1_500_000
MAX_UPLOAD_BYTES = 1_000_000
MAX_PLAYERS, MAX_MANAGERS = 500, 30
MAX_CONFLICT_RETRIES = 10
COMMIT_RETRIES, COMMIT_BACKOFF = 3, 0.5
STATUSES = {"pending", "live", "sold", "unsold"}
STATIC_DIR = Path(__file__).resolve().parent / "static"
IMG_EXTS = (".png", ".jpg", ".jpeg", ".webp")
DEFAULTS = {"title": "Intellics Auction Room", "subtitle": "Live Player Auction", "purse": 10000,
            "max_squad": 8, "step": 25, "reserve": 20}


# --------------------------------------------------------------------------- helpers
def e(x) -> str:
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


def secret(name: str) -> str:
    try:
        return str(st.secrets.get(name, "") or "").strip().strip("\"'").strip()
    except Exception:
        return ""


# --------------------------------------------------------------------------- events and images
EVENT_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,23}$")
DEFAULT_EVENTS = {"main": "Cricket", "football": "Football"}      # id -> label. "main" is the original auction (cricket).
ACTIVE_CFG = "_config"                                              # database row that remembers which event is active
_CFG_LOCK = threading.Lock()
_CFG: dict = {"backend": None, "made": False}
_ACTIVE: dict = {"t": 0.0, "v": EVENT_ID}


def event_labels() -> dict:
    """Events the admin can switch between. Default: Cricket (id main) and Football.
    Override with a secret, e.g.  EVENTS = "main:Cricket,football:Football,basketball:Basketball"."""
    out = {}
    for part in secret("EVENTS").split(","):
        k, _, v = part.partition(":")
        k = k.strip().lower()
        if EVENT_RE.match(k) and k != ACTIVE_CFG:
            out[k] = v.strip() or k.title()
    return out or dict(DEFAULT_EVENTS)


def config_backend():
    with _CFG_LOCK:
        if not _CFG["made"]:
            _CFG["backend"], _ = make_backend(ACTIVE_CFG)
            _CFG["made"] = True
        return _CFG["backend"]


def active_event() -> str:
    """The event every screen (projector, managers, organiser) is currently showing. Read through a 2-second cache."""
    now = time.time()
    with _CFG_LOCK:
        if now - _ACTIVE["t"] < 2.0:
            return _ACTIVE["v"]
    val, be = None, config_backend()
    if be is not None:
        try:
            state, _ = be.get_state()
            if state is None:
                be.init_state({**new_state(), "active": EVENT_ID})
                state, _ = be.get_state()
            val = (state or {}).get("active")
        except BackendError:
            val = None                                   # database blip: keep showing the last known event
    with _CFG_LOCK:
        if val in event_labels():
            _ACTIVE["v"] = val
        _ACTIVE["t"] = now
        return _ACTIVE["v"]


def current_event() -> str:
    return active_event()


def switch_event(target: str, current_backend) -> tuple[bool, str]:
    """Organiser action: make `target` the active event for everyone. Refused while a player is on the block."""
    labels = event_labels()
    if target not in labels:
        return False, "Unknown event."
    be = config_backend()
    if be is None:
        return False, "Event switching is unavailable (database not configured)."
    try:
        if current_backend is not None:
            state, _ = current_backend.get_state()
            if state and state.get("current"):
                return False, "A player is on the block. Finish the current lot before switching events."
        for _ in range(3):
            cfg, rev = be.get_state()
            if cfg is None:
                be.init_state({**new_state(), "active": EVENT_ID})
                cfg, rev = be.get_state()
            out = be.commit(rev, {**cfg, "active": target}, uuid.uuid4().hex, "admin", f"active event -> {target}")
            if out.get("status") == "committed":
                with _CFG_LOCK:
                    _ACTIVE.update(t=time.time(), v=target)
                return True, f"Now running the {labels[target]} auction. Projector and manager screens follow."
        return False, "Could not switch right now. Please try again."
    except BackendError as exc:
        return False, f"Database unavailable ({exc}). Nothing was changed."


def slug(x) -> str:
    return re.sub(r"[^a-z0-9]+", "-", str(x).lower()).strip("-")[:60]


@lru_cache(maxsize=4096)
def static_img(kind: str, name: str) -> str:
    """URL of static/<kind>/<slug(name)>.png|jpg|jpeg|webp if that file exists, else ''. kind '' = static/ itself."""
    sl = slug(name)
    if sl:
        for ext in IMG_EXTS:
            if ((STATIC_DIR / kind) if kind else STATIC_DIR).joinpath(sl + ext).is_file():
                return f"/app/static/{kind + '/' if kind else ''}{sl}{ext}"
    return ""


def clean_text(x, maxlen: int) -> str:
    return re.sub(r"\s+", " ", re.sub(r"[\x00-\x1f\x7f]", " ", str(x or ""))).strip()[:maxlen]


def csv_safe(v) -> str:
    """Stop spreadsheet formula injection in exported CSV."""
    v = str(v)
    return "'" + v if v[:1] in ("=", "+", "-", "@", "\t", "\r") else v


def parse_amount(x) -> int | None:
    if isinstance(x, bool):
        return None
    if isinstance(x, float) and x.is_integer():
        x = int(x)
    if isinstance(x, str) and re.fullmatch(r"\d{1,9}", x.strip()):
        x = int(x.strip())
    if isinstance(x, int) and 0 < x <= 1_000_000_000:
        return x
    return None


# --------------------------------------------------------------------------- PIN hashing
def hash_pin(pin: str, iterations: int = PBKDF2_ITER) -> str:
    salt = secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac("sha256", pin.encode(), bytes.fromhex(salt), iterations).hex()
    return f"pbkdf2_sha256${iterations}${salt}${h}"


def check_pin(pin: str, stored) -> bool:
    try:
        algo, it, salt, h = str(stored).split("$")
        if algo != "pbkdf2_sha256":
            return False
        calc = hashlib.pbkdf2_hmac("sha256", str(pin).encode(), bytes.fromhex(salt), int(it)).hex()
        return hmac.compare_digest(calc, h)
    except Exception:
        return False


def new_session_token() -> str:
    return secrets.token_hex(12)


def admin_password_problem(pw: str) -> str:
    if not pw:
        return "ADMIN_PIN is not set. Add it in the app's Secrets."
    if len(pw) < 12:
        return "ADMIN_PIN is too short. Use at least 12 characters (a passphrase is fine)."
    return ""


# --------------------------------------------------------------------------- state model
def new_state() -> dict:
    return {"schema": SCHEMA, "settings": dict(DEFAULTS), "managers": {}, "players": [], "current": None,
            "last_result": None, "sales": [], "log": [], "paused": False, "rev": 0}


def migrate_state(raw: dict) -> dict:
    """Upgrade a state from the original app (or fill gaps) without changing its meaning."""
    s = copy.deepcopy(raw)
    base = new_state()
    for k, v in base.items():
        s.setdefault(k, v)
    s["settings"] = {**DEFAULTS, **(s["settings"] if isinstance(s["settings"], dict) else {})}
    s["schema"] = SCHEMA
    for mid, m in (s["managers"].items() if isinstance(s["managers"], dict) else []):
        if isinstance(m, dict):
            if "salt" in m and "$" not in str(m.get("pin_hash", "")):   # legacy 60k-iteration hash
                m["pin_hash"] = f"pbkdf2_sha256$60000${m['salt']}${m['pin_hash']}"
            m.pop("salt", None)
            m.setdefault("session_ver", "0")
            m.setdefault("pin_hash", None)
    return s


def public_state(s: dict) -> dict:
    """Copy safe for the projector and manager screens: no hashes, no session tokens, no sale snapshots."""
    p = copy.deepcopy(s)
    for m in p["managers"].values():
        m.pop("pin_hash", None)
        m.pop("session_ver", None)
    for x in p["sales"]:
        x.pop("snapshot", None)
    return p


def clean_settings(raw: dict) -> tuple[dict, list[str]]:
    errs, out = [], {}
    for k, lo, hi, label in (("purse", 100, 1_000_000, "Purse"), ("max_squad", 1, 50, "Max squad"),
                             ("step", 1, 10_000, "Bid step"), ("reserve", 0, 10_000, "Reserve")):
        v = raw.get(k)
        if isinstance(v, float) and v.is_integer():
            v = int(v)
        if isinstance(v, bool) or not isinstance(v, int):
            errs.append(f"{label} must be a whole number.")
        elif not lo <= v <= hi:
            errs.append(f"{label} must be between {lo} and {hi}.")
        else:
            out[k] = v
    for k, req in (("title", True), ("subtitle", False)):
        v = raw.get(k, "")
        if not isinstance(v, str) or len(v) > 80 or (req and not v.strip()):
            errs.append(f"{k.title()} must be text of at most 80 characters.")
        else:
            out[k] = clean_text(v, 80)
    if not errs and (out["max_squad"] - 1) * out["reserve"] >= out["purse"]:
        errs.append("Reserve x (squad size - 1) must be below the purse, or nobody could ever bid.")
    return out, errs


def validate_state(s) -> list[str]:
    """Every invariant of the auction. An empty list means the state is consistent."""
    errs: list[str] = []
    if not isinstance(s, dict):
        return ["State is not an object."]
    for k in ("settings", "managers", "players", "sales", "log"):
        if k not in s:
            errs.append(f"Missing section: {k}")
    if errs:
        return errs
    if not isinstance(s["settings"], dict) or not isinstance(s["managers"], dict) or not isinstance(s["players"], list) \
            or not isinstance(s["sales"], list) or not isinstance(s["log"], list):
        return ["A section has the wrong type."]
    cfg, cfg_errs = clean_settings(s["settings"])
    if cfg_errs:
        return ["Settings invalid: " + cfg_errs[0]]
    if len(s["managers"]) > MAX_MANAGERS or len(s["players"]) > MAX_PLAYERS:
        return ["Too many managers or players."]
    if not isinstance(s.get("paused", False), bool):
        errs.append("paused must be true/false.")
    pm: dict[str, dict] = {}
    for p in s["players"]:
        if not isinstance(p, dict) or not isinstance(p.get("id"), str) or p["id"] in pm:
            errs.append("A player is malformed or duplicated.")
            continue
        pm[p["id"]] = p
        if p.get("status") not in STATUSES:
            errs.append(f"Player {p['id']} has invalid status.")
        if not isinstance(p.get("name"), str) or not p["name"].strip():
            errs.append(f"Player {p['id']} has no name.")
        if not isinstance(p.get("base"), int) or isinstance(p["base"], bool) or p["base"] < 1:
            errs.append(f"Player {p['id']} has an invalid base price.")
        if p.get("status") == "sold":
            if p.get("sold_to") not in s["managers"] or not isinstance(p.get("price"), int) or p["price"] < 1:
                errs.append(f"Sold player {p['id']} has no valid buyer/price.")
        elif p.get("sold_to") is not None or p.get("price") is not None:
            errs.append(f"Unsold player {p['id']} still has a buyer or price.")
    seen_in_squads: set[str] = set()
    for mid, m in s["managers"].items():
        if not isinstance(m, dict) or m.get("id") != mid or not isinstance(m.get("squad"), list):
            errs.append(f"Manager {mid} is malformed.")
            continue
        if not isinstance(m.get("team"), str) or not m["team"].strip() or not isinstance(m.get("name"), str):
            errs.append(f"Manager {mid} needs a team and name.")
        spent = 0
        for x in m["squad"]:
            pid = x.get("pid") if isinstance(x, dict) else None
            p = pm.get(pid)
            if not p or p.get("status") != "sold" or p.get("sold_to") != mid or p.get("price") != x.get("price"):
                errs.append(f"Squad entry {pid} of {mid} disagrees with the player list.")
                continue
            if pid in seen_in_squads:
                errs.append(f"Player {pid} is in more than one squad.")
            seen_in_squads.add(pid)
            spent += x["price"]
        if len(m["squad"]) > cfg["max_squad"]:
            errs.append(f"{mid} exceeds the squad limit.")
        if not isinstance(m.get("purse"), int) or isinstance(m["purse"], bool) or m["purse"] < 0:
            errs.append(f"{mid} has an invalid or negative purse.")
        elif m["purse"] != cfg["purse"] - spent:
            errs.append(f"{mid} purse does not equal initial purse minus purchases.")
    sold_ids = {pid for pid, p in pm.items() if p.get("status") == "sold"}
    if sold_ids != seen_in_squads:
        errs.append("Sold players and squads do not match.")
    sale_pids = []
    for x in s["sales"]:
        p = pm.get(x.get("pid")) if isinstance(x, dict) else None
        if not p or p.get("status") != "sold" or p.get("sold_to") != x.get("mid") or p.get("price") != x.get("price"):
            errs.append("A sale record disagrees with the player list.")
        else:
            sale_pids.append(x["pid"])
    if len(sale_pids) != len(set(sale_pids)) or set(sale_pids) != sold_ids:
        errs.append("Sales log does not match sold players.")
    cur = s.get("current")
    live = [pid for pid, p in pm.items() if p.get("status") == "live"]
    if cur is None:
        if live:
            errs.append("A player is live but nobody is on the block.")
    else:
        if not isinstance(cur, dict) or live != [cur.get("pid")]:
            errs.append("The current player and live status disagree.")
        else:
            hist = cur.get("history", [])
            if hist:
                last = hist[-1]
                if cur.get("leader") != last.get("mid") or cur.get("bid") != last.get("amt"):
                    errs.append("Leader and bid history disagree.")
                if any(h.get("mid") not in s["managers"] for h in hist):
                    errs.append("Bid history references an unknown manager.")
                amts = [h.get("amt") for h in hist]
                if any(not isinstance(a, int) for a in amts) or amts != sorted(set(amts)) or amts[0] < pm[cur["pid"]]["base"]:
                    errs.append("Bid history is not strictly increasing from the base price.")
            elif cur.get("leader") is not None or cur.get("bid") is not None:
                errs.append("Bid without history.")
            if cur.get("leader") is not None and cur["leader"] in cur.get("out", []):
                errs.append("The leader is marked as withdrawn.")
            if any(o not in s["managers"] for o in cur.get("out", [])):
                errs.append("Withdrawn list references an unknown manager.")
            if cur.get("call", 0) not in (0, 1, 2) or (cur.get("call") and cur.get("bid") is None):
                errs.append("Invalid going-once/twice call.")
    return errs


# --------------------------------------------------------------------------- auction rules (pure functions)
def _log(s: dict, text: str) -> None:
    s["log"].append({"t": now_iso(), "text": text})
    del s["log"][:-300]


def player_of(s: dict, pid: str) -> dict | None:
    return next((p for p in s["players"] if p["id"] == pid), None)


def min_next(s: dict) -> int:
    cur = s["current"]
    return cur["bid"] + s["settings"]["step"] if cur["bid"] is not None else player_of(s, cur["pid"])["base"]


def reserve_after(s: dict, m: dict) -> int:
    return max(0, s["settings"]["max_squad"] - len(m["squad"]) - 1) * s["settings"]["reserve"]


def max_bid(s: dict, m: dict) -> int:
    return m["purse"] - reserve_after(s, m)


def challengers(s: dict) -> list[dict]:
    cur, need = s["current"], min_next(s)
    return [m for m in s["managers"].values()
            if m["id"] != cur["leader"] and m["id"] not in cur["out"]
            and len(m["squad"]) < s["settings"]["max_squad"] and max_bid(s, m) >= need]


def _finish_sale(s: dict) -> str:
    cur = s["current"]
    p, m, price = player_of(s, cur["pid"]), s["managers"][cur["leader"]], cur["bid"]
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
    """No eligible challenger left: sell to the highest bidder, or mark unsold if nobody bid."""
    cur = s["current"]
    if not cur or s["paused"] or challengers(s):
        return None
    return _finish_sale(s) if cur["bid"] is not None else _finish_unsold(s)


def f_bid(s, actor, a):
    mid, cur = actor["id"], s["current"]
    m = s["managers"][mid]
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
    amount = parse_amount(a.get("amount"))
    if amount is None:
        return False, "Enter a whole number of lakhs."
    need = min_next(s)
    if amount < need:
        return False, f"Too late or too low: the minimum bid is now {money(need)}."
    cap = max_bid(s, m)
    if amount > cap:
        return False, (f"Your limit for this bid is {money(max(cap, 0))} (purse {money(m['purse'])}, "
                       f"{money(reserve_after(s, m))} reserved for your remaining squad slots).")
    cur["bid"], cur["leader"], cur["call"] = amount, mid, 0
    cur["history"].append({"t": now_iso(), "mid": mid, "amt": amount})
    _log(s, f"BID {m['team']} {money(amount)} on {player_of(s, cur['pid'])['name']}")
    res = _auto(s)
    return True, (f"Bid accepted. {res}" if res else f"Bid of {money(amount)} accepted. You lead.")


def f_out(s, actor, a):
    mid, cur = actor["id"], s["current"]
    if not cur:
        return False, "No player is up for auction."
    if s["paused"]:
        return False, "Bidding is paused by the organiser."
    if cur["leader"] == mid:
        return False, "You hold the highest bid, so you cannot withdraw."
    if mid in cur["out"]:
        return False, "You have already withdrawn."
    cur["out"].append(mid)
    _log(s, f"OUT {s['managers'][mid]['team']}")
    res = _auto(s)
    return True, (f"You withdrew. {res}" if res else "You have withdrawn from this player.")


def f_bring(s, actor, a):
    if s["current"]:
        return False, "Finish the current player first."
    if not s["managers"]:
        return False, "Add managers first."
    pid = a.get("pid")
    pend = [p for p in s["players"] if p["status"] == "pending"]
    p = player_of(s, pid) if pid else (pend[0] if pend else None)
    if not p or p["status"] != "pending":
        return False, "No player left in the queue."
    p["status"] = "live"
    s["current"] = {"pid": p["id"], "bid": None, "leader": None, "out": [], "history": [], "call": 0, "opened": now_iso()}
    s["last_result"] = None
    _log(s, f"UP {p['name']}")
    return True, f"{p['name']} is up for auction."


def f_call(s, actor, a):
    cur, n = s["current"], a.get("n")
    if n not in (1, 2):
        return False, "Call must be going once or going twice."
    if not cur or cur["bid"] is None:
        return False, "There is no bid to call on."
    cur["call"] = n
    return True, "Going once..." if n == 1 else "Going twice..."


def f_sold(s, actor, a):
    cur = s["current"]
    if not cur or cur["bid"] is None:
        return False, "There is no bid to sell on."
    return True, _finish_sale(s)


def f_unsold(s, actor, a):
    cur = s["current"]
    if not cur:
        return False, "No player is up."
    if cur["bid"] is not None:
        return False, "This player has a bid. Undo the bids first, or use Sold."
    return True, _finish_unsold(s)


def f_undo_bid(s, actor, a):
    cur = s["current"]
    if not cur or not cur["history"]:
        return False, "No bid to undo."
    cur["history"].pop()
    last = cur["history"][-1] if cur["history"] else None
    cur["bid"], cur["leader"], cur["call"] = (last["amt"], last["mid"], 0) if last else (None, None, 0)
    _log(s, "UNDO last bid")
    return True, "Last bid removed."


def f_undo_sale(s, actor, a):
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


def f_clear_out(s, actor, a):
    if not s["current"]:
        return False, "No player is up."
    s["current"]["out"] = []
    _log(s, "Withdrawn managers allowed back in")
    return True, "All managers are back in for this player."


def f_pause(s, actor, a):
    flag = bool(a.get("flag"))
    s["paused"] = flag
    _log(s, "PAUSED" if flag else "RESUMED")
    return True, "Bidding paused." if flag else "Bidding resumed."


def f_requeue(s, actor, a):
    n = 0
    for p in s["players"]:
        if p["status"] == "unsold":
            p["status"] = "pending"
            n += 1
    return (True, f"{n} unsold player(s) back in the queue.") if n else (False, "No unsold players.")


def f_shuffle(s, actor, a):
    idx = [i for i, p in enumerate(s["players"]) if p["status"] == "pending"]
    items = [s["players"][i] for i in idx]
    random.shuffle(items)
    for i, p in zip(idx, items):
        s["players"][i] = p
    return True, "Queue shuffled."


def f_reset(s, actor, a):
    if a.get("confirm") != "RESET":
        return False, "Type RESET to confirm."
    for m in s["managers"].values():
        m["purse"], m["squad"] = s["settings"]["purse"], []
    for p in s["players"]:
        p.update(status="pending", sold_to=None, price=None)
    s.update(current=None, last_result=None, sales=[], paused=False)
    _log(s, "AUCTION RESET")
    return True, "Auction reset. All purses restored and all players back in the queue."


def f_settings(s, actor, a):
    new, errs = clean_settings(a.get("settings", {}))
    if errs:
        return False, " ".join(errs[:3])
    old = s["settings"]
    rules = ("purse", "max_squad", "step", "reserve")
    if s["current"] and any(new[k] != old[k] for k in rules):
        return False, "Bidding rules cannot change while a player is on the block. Finish or mark the lot first."
    if s["sales"] and new["purse"] != old["purse"]:
        return False, "The purse cannot change after sales have happened. Reset the auction first."
    biggest = max([len(m["squad"]) for m in s["managers"].values()] or [0])
    if new["max_squad"] < biggest:
        return False, f"Max squad cannot be below {biggest}: a team already has that many players."
    s["settings"] = new
    if not s["sales"]:
        for m in s["managers"].values():
            m["purse"] = new["purse"]
    _log(s, "Settings changed")
    return True, "Settings saved."


def parse_manager_lines(text: str):
    rows, errs = [], []
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        parts = [clean_text(x, 60) for x in re.split(r"[,\t]", line)]
        if len(parts) != 3 or not parts[0] or not parts[1] or not re.fullmatch(r"\d{4,8}", parts[2]):
            errs.append(f"Line {n}: use  Team, Manager, PIN  (PIN = 4 to 8 digits)")
        else:
            rows.append(parts)
    return rows, errs


def f_add_managers(s, actor, a):
    if s["sales"] or s["current"]:
        return False, "Managers can only be changed before the first player is brought up or sold."
    rows, errs = parse_manager_lines(str(a.get("text", "")))
    if errs:
        return False, " | ".join(errs[:4])
    if not rows:
        return False, "Nothing to add."
    existing = {} if a.get("replace") else dict(s["managers"])
    if len(existing) + len(rows) > MAX_MANAGERS:
        return False, f"At most {MAX_MANAGERS} managers."
    teams = {m["team"].lower() for m in existing.values()}
    for t, _, _ in rows:
        if t.lower() in teams:
            return False, f"Duplicate team name: {t}"
        teams.add(t.lower())
    n0 = max([int(k[1:]) for k in existing] or [0])
    for i, (team, name, pin) in enumerate(rows, 1):
        existing[f"m{n0 + i}"] = {"id": f"m{n0 + i}", "team": team, "name": name, "pin_hash": hash_pin(pin),
                                  "session_ver": new_session_token(), "purse": s["settings"]["purse"], "squad": []}
    s["managers"] = existing
    _log(s, f"{len(rows)} manager(s) saved")
    return True, f"{len(rows)} manager(s) saved."


def f_reset_pin(s, actor, a):
    m, pin = s["managers"].get(a.get("mid")), str(a.get("pin", ""))
    if not m:
        return False, "Unknown manager."
    if not re.fullmatch(r"\d{4,8}", pin):
        return False, "PIN must be 4 to 8 digits."
    m["pin_hash"], m["session_ver"] = hash_pin(pin), new_session_token()   # new token signs the manager out everywhere
    _log(s, f"PIN reset for {m['team']}")
    return True, f"PIN updated for {m['team']}. Any open session for that team is signed out."


BASE_RE = re.compile(r"^\s*(?:₹|rs\.?)?\s*(\d{1,7})(?:\.0+)?\s*(?:l|lakh|lakhs)?\s*$", re.I)


def parse_players_csv(text: str):
    """Strict CSV parse. Returns (rows, errors). Never guesses at malformed numbers."""
    text = (text or "").lstrip("\ufeff").strip()
    if not text:
        return [], ["Nothing to add."]
    if len(text.encode("utf-8", "ignore")) > MAX_UPLOAD_BYTES:
        return [], ["File is too large."]
    first = text.splitlines()[0]
    try:
        reader = csv.DictReader(io.StringIO(text), dialect=csv.excel_tab if "\t" in first else csv.excel)
        heads = {(h or "").strip().lower().replace(" ", "_"): h for h in (reader.fieldnames or [])}
        name_h = next((heads[k] for k in ("name", "player", "player_name") if k in heads), None)
        base_h = next((h for k, h in heads.items() if k.startswith("base")), None)
        if not name_h or not base_h:
            return [], ["The first line must be a header containing: name, base_price (origin and role are optional)."]
        pick = lambda row, keys: clean_text(next((row[heads[k]] for k in keys if k in heads and row.get(heads[k])), ""), 60)
        rows, errs = [], []
        for n, row in enumerate(reader, 2):
            if None in row or any(v is None for v in row.values()):
                errs.append(f"Row {n}: wrong number of columns.")
                continue
            name = clean_text(row[name_h], 60)
            mt = BASE_RE.match(row[base_h] or "")
            if not name or not mt or int(mt.group(1)) < 1:
                errs.append(f"Row {n}: needs a name and a whole-number base_price in lakhs (e.g. 50).")
                continue
            rows.append({"name": name, "origin": pick(row, ("origin", "from", "city", "hometown", "location", "state")),
                         "role": pick(row, ("role", "category", "position")), "base": int(mt.group(1))})
            if len(rows) > MAX_PLAYERS:
                return [], [f"At most {MAX_PLAYERS} players."]
    except csv.Error as exc:
        return [], [f"Could not read the CSV ({exc})."]
    return rows, errs


def f_add_players(s, actor, a):
    replace = bool(a.get("replace"))
    if replace and (s["sales"] or s["current"]):
        return False, "Players can only be replaced before the first player is brought up or sold."
    rows, errs = parse_players_csv(str(a.get("text", "")))
    if errs:
        return False, " | ".join(errs[:4])
    if not rows:
        return False, "No valid rows found."
    players = [] if replace else list(s["players"])
    keys = {(p["name"].lower(), p["origin"].lower()) for p in players}
    for r in rows:
        k = (r["name"].lower(), r["origin"].lower())
        if k in keys:
            return False, f"Duplicate player: {r['name']} ({r['origin'] or 'no origin'}). Nothing was added."
        keys.add(k)
    if len(players) + len(rows) > MAX_PLAYERS:
        return False, f"At most {MAX_PLAYERS} players."
    n0 = max([int(p["id"][1:]) for p in players] or [0])
    for i, r in enumerate(rows, 1):
        players.append({"id": f"p{n0 + i}", **r, "status": "pending", "sold_to": None, "price": None})
    s["players"] = players
    _log(s, f"{len(rows)} player(s) added")
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
Neel Banerjee,Kolkata,Batter,85"""


def f_demo(s, actor, a):
    if s["sales"] or s["current"]:
        return False, "Reset the auction first; demo data replaces everything."
    s["managers"], s["players"] = {}, []
    pins = a.get("manager_text", "")
    ok1, m1 = f_add_managers(s, actor, {"text": pins, "replace": True})
    ok2, m2 = f_add_players(s, actor, {"text": DEMO_PLAYERS, "replace": True})
    return ok1 and ok2, f"Demo loaded. {m1} {m2}"


def make_backup(s: dict) -> dict:
    """Backup file content: no PIN hashes or session tokens (managers get new PINs after a restore)."""
    st_ = copy.deepcopy(s)
    for m in st_["managers"].values():
        m.pop("pin_hash", None)
        m.pop("session_ver", None)
    canon = json.dumps(st_, sort_keys=True, separators=(",", ":"))
    return {"format": "auction-backup", "version": 1, "exported_at": now_iso(),
            "checksum": hashlib.sha256(canon.encode()).hexdigest(), "state": st_}


def parse_backup(raw: bytes) -> tuple[dict | None, str]:
    """Validate a backup file. Returns (state, "") or (None, reason). Checksums catch corruption, not forgery."""
    if len(raw) > MAX_STATE_BYTES:
        return None, "File is too large to be an auction backup."
    try:
        data = json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return None, "That file is not valid JSON."
    if not isinstance(data, dict):
        return None, "That file is not an auction backup."
    note = ""
    if data.get("format") == "auction-backup":
        st_ = data.get("state")
        if data.get("version") != 1 or not isinstance(st_, dict):
            return None, "Unsupported backup version."
        canon = json.dumps(st_, sort_keys=True, separators=(",", ":"))
        if not hmac.compare_digest(hashlib.sha256(canon.encode()).hexdigest(), str(data.get("checksum", ""))):
            return None, "The backup is corrupted or was edited (checksum mismatch)."
    elif "managers" in data and "players" in data:
        st_, note = data, "Old-format backup accepted."
    else:
        return None, "That file is not an auction backup."
    cand = migrate_state(st_)
    errs = validate_state(cand)
    if errs:
        return None, "Backup failed validation: " + " | ".join(errs[:3])
    return cand, note


def f_restore(s, actor, a):
    if a.get("confirm") != "RESTORE":
        return False, "Type RESTORE to confirm."
    cand = migrate_state(a.get("state") or {})
    errs = validate_state(cand)
    if errs:
        return False, "Backup failed validation: " + errs[0]
    old = dict(s.get("managers", {}))
    for mid, m in cand["managers"].items():
        keep = old.get(mid)
        m["pin_hash"] = keep.get("pin_hash") if keep and keep.get("team") == m["team"] else None
        m["session_ver"] = new_session_token()           # everyone signs in again after a restore
    rev = s.get("rev", 0)
    s.clear()
    s.update(cand)
    s["rev"] = rev
    _log(s, "BACKUP RESTORED")
    missing = sum(1 for m in s["managers"].values() if not m["pin_hash"])
    return True, "Backup restored." + (f" {missing} manager(s) need a new PIN (Setup tab)." if missing else "")


# --------------------------------------------------------------------------- authorisation + dispatch
ACTIONS = {
    "bid": ("manager", f_bid), "withdraw": ("manager", f_out),
    "bring": ("admin", f_bring), "call": ("admin", f_call), "sold": ("admin", f_sold), "unsold": ("admin", f_unsold),
    "undo_bid": ("admin", f_undo_bid), "undo_sale": ("admin", f_undo_sale), "clear_out": ("admin", f_clear_out),
    "pause": ("admin", f_pause), "requeue": ("admin", f_requeue), "shuffle": ("admin", f_shuffle),
    "reset": ("admin", f_reset), "settings": ("admin", f_settings), "add_managers": ("admin", f_add_managers),
    "reset_pin": ("admin", f_reset_pin), "add_players": ("admin", f_add_players), "demo": ("admin", f_demo),
    "restore": ("admin", f_restore),
}


def authorise(s: dict, actor, role: str) -> tuple[bool, str]:
    if not isinstance(actor, dict) or actor.get("role") != role:
        return False, "Not authorised for this action."
    if role == "manager":
        m = s["managers"].get(actor.get("id"))
        if not m:
            return False, "Your team no longer exists. Please sign in again."
        if not hmac.compare_digest(str(m.get("session_ver")).encode(), str(actor.get("ver")).encode()):
            return False, "Your session is no longer valid. Please sign in again."
    return True, ""


def apply_action(s: dict, action: str, actor, args: dict) -> tuple[bool, str]:
    spec = ACTIONS.get(action)
    if not spec:
        return False, "Unknown action."
    role, fn = spec
    ok, why = authorise(s, actor, role)
    if not ok:
        return False, why
    try:
        return fn(s, actor, args or {})
    except Exception:
        log.exception("rule function failed: %s", action)
        return False, "Unexpected error. Nothing was changed."


# --------------------------------------------------------------------------- backends
class BackendError(Exception):
    def __init__(self, msg: str, unknown: bool = False):
        super().__init__(msg)
        self.unknown = unknown      # True = we cannot tell whether a write reached the database


class MemoryBackend:
    """Process-local stand-in with the same atomic semantics. DEMO and TESTS only: not persistent."""
    persistent = False

    def __init__(self, state: dict | None = None):
        self._lock = threading.RLock()
        self.state, self.rev = (copy.deepcopy(state) if state else new_state()), 0
        self.ops: dict[str, dict] = {}
        self.auth: dict[str, list] = {}

    def get_state(self):
        with self._lock:
            return migrate_state(self.state), self.rev

    def get_rev(self):
        with self._lock:
            return self.rev

    def init_state(self, state):
        return False

    def commit(self, expected_rev, new_state_, idem, actor_label, message):
        with self._lock:
            if idem in self.ops:
                return {"status": "duplicate", "rev": self.ops[idem]["rev"], "message": self.ops[idem]["message"]}
            if expected_rev != self.rev:
                return {"status": "conflict", "rev": self.rev}
            if not isinstance(new_state_, dict) or "managers" not in new_state_ or "players" not in new_state_:
                raise BackendError("refused: malformed state")
            self.rev += 1
            self.state = copy.deepcopy(new_state_)
            self.state["rev"] = self.rev
            self.ops[idem] = {"rev": self.rev, "message": message}
            return {"status": "committed", "rev": self.rev}

    def auth_check(self, key):
        with self._lock:
            until = self.auth.get(key, [0, 0.0])[1]
            return (True, int(until - time.time()) + 1) if until > time.time() else (False, 0)

    def auth_record(self, key, ok, max_fails, lock_seconds):
        with self._lock:
            rec = self.auth.setdefault(key, [0, 0.0])
            if ok:
                self.auth.pop(key, None)
                return False, 0
            rec[0] += 1
            if rec[0] >= max_fails:
                rec[0], rec[1] = 0, time.time() + lock_seconds
                return True, lock_seconds
            return False, 0


class SupabaseBackend:
    """Talks to the SQL functions in supabase_migration.sql through PostgREST. Needs the server-side secret key."""
    persistent = True

    def __init__(self, url: str, key: str, event: str = EVENT_ID, timeout: float = 8.0):
        self.url, self.event, self.timeout = url, event, timeout
        self.headers = {"apikey": key, "Content-Type": "application/json"}
        if not key.startswith("sb_"):
            self.headers["Authorization"] = f"Bearer {key}"
        self.http = requests.Session()

    def _rpc(self, fn: str, payload: dict):
        try:
            r = self.http.post(f"{self.url}/rest/v1/rpc/{fn}", headers=self.headers, json=payload, timeout=self.timeout)
        except (requests.Timeout, requests.ConnectionError) as exc:
            raise BackendError(f"network problem ({type(exc).__name__})", unknown=True) from None
        except requests.RequestException as exc:
            raise BackendError(f"request failed ({type(exc).__name__})", unknown=True) from None
        if r.status_code >= 500:
            raise BackendError(f"database error {r.status_code}", unknown=True)
        if r.status_code in (401, 403):
            raise BackendError("database refused the key (use the secret/service key, and run the SQL migration)")
        if r.status_code >= 400:
            raise BackendError(f"database rejected the request ({r.status_code}); has the SQL migration been run?")
        try:
            return r.json()
        except ValueError:
            raise BackendError("database returned an unreadable reply", unknown=True) from None

    def get_state(self):
        row = self._rpc("auction_get", {"p_event": self.event})
        if not row:
            return None, 0
        st_ = migrate_state(row["data"])
        st_["rev"] = int(row["rev"])
        return st_, int(row["rev"])

    def get_rev(self):
        v = self._rpc("auction_rev", {"p_event": self.event})
        return None if v is None else int(v)

    def init_state(self, state):
        return bool(self._rpc("auction_init", {"p_event": self.event, "p_data": state}))

    def commit(self, expected_rev, new_state_, idem, actor_label, message):
        out = self._rpc("auction_commit", {"p_event": self.event, "p_expected_rev": expected_rev, "p_new": new_state_,
                                           "p_idem": idem, "p_actor": actor_label, "p_message": message})
        if not isinstance(out, dict) or "status" not in out:
            raise BackendError("unexpected reply to commit", unknown=True)
        return out

    def auth_check(self, key):
        o = self._rpc("auction_auth_check", {"p_key": key})
        return bool(o.get("locked")), int(o.get("seconds", 0))

    def auth_record(self, key, ok, max_fails, lock_seconds):
        o = self._rpc("auction_auth_record", {"p_key": key, "p_ok": ok, "p_max": max_fails, "p_lock": lock_seconds})
        return bool(o.get("locked")), int(o.get("seconds", 0))


# --------------------------------------------------------------------------- transaction pathway
@dataclass
class Result:
    ok: bool
    message: str
    status: str = "committed"     # committed | duplicate | rejected | stale | unavailable | unknown | conflict
    rev: int = 0


def run_action(backend, action: str, actor, args: dict | None = None, expected_rev: int | None = None,
               idem_key: str | None = None) -> Result:
    """The single pathway for every state change. Authoritative read -> rules -> invariants -> atomic commit."""
    args, idem_key = args or {}, idem_key or uuid.uuid4().hex
    label = (actor or {}).get("role", "?") + (":" + str(actor.get("id")) if (actor or {}).get("id") else "")
    try:
        for _ in range(MAX_CONFLICT_RETRIES):
            state, rev = backend.get_state()
            if state is None:
                return Result(False, "The auction has not been initialised yet.", "unavailable")
            if expected_rev is not None and rev != expected_rev:
                return Result(False, "The screen was out of date (something changed a moment ago). It has refreshed; "
                                     "check and try again.", "stale", rev)
            if action != "restore":
                bad = validate_state(state)
                if bad:
                    return Result(False, "Stored auction data failed its consistency check, so changes are disabled: "
                                         + bad[0], "unavailable", rev)
            new = copy.deepcopy(state)
            ok, msg = apply_action(new, action, actor, args)
            if not ok:
                return Result(False, msg, "rejected", rev)
            bad = validate_state(new)
            if bad:
                log.error("action %s refused by invariants: %s", action, bad)
                return Result(False, "Refused: this would break an auction rule (" + bad[0] + ").", "rejected", rev)
            if len(json.dumps(new)) > MAX_STATE_BYTES:
                return Result(False, "Refused: auction data would become too large.", "rejected", rev)
            out = _commit_retrying(backend, rev, new, idem_key, label, msg)
            if out["status"] == "committed":
                return Result(True, msg, "committed", out["rev"])
            if out["status"] == "duplicate":
                return Result(True, out.get("message") or msg, "duplicate", out.get("rev", 0))
            if out["status"] == "conflict":
                time.sleep(random.uniform(0, 0.04))        # someone else committed first: re-read and re-validate
                continue
            return Result(False, "The database could not accept the change (" + str(out["status"]) + ").", "unavailable")
        return Result(False, "Too many changes at the same moment. Nothing was saved; please try again.", "conflict")
    except BackendError as exc:
        if exc.unknown and getattr(exc, "after_write", False):
            return Result(False, "Could not confirm whether this was saved (" + str(exc) + "). Refresh and check "
                                 "before repeating it.", "unknown")
        return Result(False, f"Database unavailable ({exc}). Nothing was saved.", "unavailable")


def _commit_retrying(backend, rev, new, idem, label, msg) -> dict:
    """Retry only with the SAME idempotency key, so a lost reply can never apply the change twice."""
    last: BackendError | None = None
    for attempt in range(COMMIT_RETRIES):
        try:
            return backend.commit(rev, new, idem, label, msg)
        except BackendError as exc:
            if not exc.unknown:
                raise
            last = exc
            time.sleep(COMMIT_BACKOFF * (attempt + 1))
    assert last is not None
    last.after_write = True
    raise last


def verify_login(backend, key: str, ok_fn, max_fails: int, lock_seconds: int) -> tuple[bool, str]:
    """Rate-limited credential check; the counter lives in the database so it holds across app instances."""
    try:
        locked, secs = backend.auth_check(key)
        if locked:
            return False, f"Too many wrong attempts. Try again in {secs} seconds."
        ok = bool(ok_fn())
        locked, secs = backend.auth_record(key, ok, max_fails, lock_seconds)
    except BackendError:
        return False, "Database unavailable, so sign-in is paused. Check the connection."
    if ok:
        return True, ""
    return False, (f"Wrong credentials. Locked for {secs} seconds." if locked else "Wrong PIN or password.")


# --------------------------------------------------------------------------- shared read cache for display
@dataclass
class Snap:
    view: dict | None
    rev: int
    ok: bool
    error: str
    synced: float
    persistent: bool
    invalid: bool = False


class Store:
    """Display cache. It is NEVER used for decisions; every mutation re-reads the database."""

    def __init__(self, backend, config_error: str = ""):
        self.backend, self.persistent = backend, bool(backend and backend.persistent)
        self._view, self._rev, self._ok, self._invalid = None, -1, False, False
        self._error = config_error or "Connecting..."
        self._checked = self._synced = 0.0
        self._refresh = threading.Lock()

    def invalidate(self):
        self._checked = 0.0

    def read(self) -> Snap:
        if self.backend is not None and time.time() - self._checked >= STORE_MIN_INTERVAL \
                and self._refresh.acquire(blocking=False):
            try:
                self._refresh_now()
            finally:
                self._refresh.release()
        return Snap(self._view, self._rev, self._ok, self._error, self._synced, self.persistent, self._invalid)

    def _refresh_now(self):
        try:
            if self._view is None and not self._invalid or self.backend.get_rev() != self._rev:
                state, rev = self.backend.get_state()
                if state is None:                           # confirmed: no row exists yet. Insert-if-absent, never overwrite.
                    self.backend.init_state(new_state())
                    state, rev = self.backend.get_state()
                    if state is None:
                        raise BackendError("could not create the auction record")
                bad = validate_state(state)
                if bad:
                    self._view, self._ok, self._invalid, self._rev = None, False, True, rev
                    self._error = "Saved auction data failed its consistency check: " + bad[0]
                else:
                    self._view, self._rev, self._invalid = public_state(state), rev, False
            if not self._invalid:
                self._ok, self._error, self._synced = True, "", time.time()
        except BackendError as exc:
            self._ok, self._error = False, f"Database unavailable ({exc})"
        self._checked = time.time()


def make_backend(event: str = EVENT_ID):
    url, key = secret("SUPABASE_URL").rstrip("/"), secret("SUPABASE_KEY")
    if url.endswith("/rest/v1"):
        url = url[: -len("/rest/v1")]
    if not url and not key:
        return MemoryBackend(), ""
    if not (url.startswith("https://") and key):
        return None, "SUPABASE_URL / SUPABASE_KEY are set but look wrong. The auction is disabled until they are fixed."
    return SupabaseBackend(url, key, event), ""


@st.cache_resource
def get_store(event: str = EVENT_ID) -> Store:
    if not event:
        return Store(None, "This event link is not recognised. Check the web address (the ?event= part).")
    backend, err = make_backend(event)
    return Store(backend, err)


# --------------------------------------------------------------------------- sessions (server-side Streamlit session)
def manager_session(sn: Snap):
    """Return the manager actor if the signed-in session is still valid, else None. Identity is never taken from the browser."""
    sess = st.session_state.get("au_mgr")
    if not sess:
        return None
    m = sn.view["managers"].get(sess["id"]) if sn.view else None
    if sess.get("event") != current_event():           # the organiser switched events: sign in again
        st.session_state.pop("au_mgr", None)
        return None
    if time.time() > sess["exp"]:
        st.session_state.pop("au_mgr", None)
        return None
    return {"role": "manager", "id": sess["id"], "ver": sess["ver"]}


def admin_actor(touch: bool = False):
    a = st.session_state.get("au_admin")
    now = time.time()
    if not a:
        return None
    if now - a["t0"] > ADMIN_MAX_SECONDS or now - a["last"] > ADMIN_IDLE_SECONDS:
        st.session_state.pop("au_admin", None)
        return None
    if touch:
        a["last"] = now
    return {"role": "admin"}


def flash_set(res: Result) -> None:
    icon = "✔" if res.ok else ("⚠" if res.status == "unknown" else "✖")
    suffix = " (saved)" if res.ok else ""
    st.session_state["au_flash"] = (res.ok, f"{icon} {res.message}{suffix}", time.time())


def do(S: Store, actor, action: str, args=None, expected_rev=None) -> Result:
    """UI entry point for any mutation: debounce, run on the authoritative pathway, refresh the cache, show the outcome."""
    sig = (action, json.dumps(args or {}, sort_keys=True, default=str), expected_rev)
    last = st.session_state.get("au_last")
    if last and last[0] == sig and time.time() - last[1] < 1.2:
        return Result(False, "Already submitted: waiting for the first request.", "rejected")
    st.session_state["au_last"] = (sig, time.time())
    if actor is None:
        res = Result(False, "Your session has expired. Please sign in again.", "rejected")
    elif S.backend is None:
        res = Result(False, "The database is not configured correctly.", "unavailable")
    else:
        res = run_action(S.backend, action, actor, args, expected_rev)
    S.invalidate()
    flash_set(res)
    return res


# --------------------------------------------------------------------------- design
CSS = """<style>
#MainMenu,footer,header[data-testid="stHeader"],[data-testid="stToolbar"],[data-testid="stDecoration"]{display:none!important}
:root{--bg:#050816;--panel:#0B1230;--line:#1E2A5A;--cy:#22D3EE;--vi:#8B5CF6;--mg:#E879F9;--tx:#EAF0FF;--mu:#9AA7CC;--ok:#34D399;--wn:#FBBF24;--bad:#F87171}
.stApp{background:radial-gradient(1000px 560px at 10% -10%,#1B1750 0%,transparent 60%),radial-gradient(900px 500px at 100% 0%,#07324A 0%,transparent 55%),var(--bg)!important;font-family:system-ui,-apple-system,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
.block-container{padding-top:1rem!important;max-width:1700px}
.stApp [data-testid="stMarkdownContainer"] p,.stApp [data-testid="stWidgetLabel"] p,.stApp label p,.stApp h1,.stApp h2,.stApp h3,.stApp h4{color:var(--tx)}
.stApp [data-testid="stCaptionContainer"]{color:var(--mu)}
.stApp input,.stApp textarea{background:#0A1028!important;color:var(--tx)!important;border-color:var(--line)!important}
.stApp .stButton>button,.stApp .stDownloadButton>button,.stApp [data-testid="stFormSubmitButton"]>button{background:#101A40;color:var(--tx);border:1px solid var(--line);border-radius:10px;font-weight:700;padding:.6rem 1rem;min-height:2.8rem}
.stApp .stButton>button:hover{border-color:var(--cy);color:#fff;box-shadow:0 0 14px rgba(34,211,238,.35)}
.stApp .stButton>button[kind="primary"],.stApp [data-testid="stFormSubmitButton"]>button[kind="primaryFormSubmit"]{background:linear-gradient(90deg,#0891B2,#7C3AED);color:#fff;border:0}
.stApp .stButton>button:disabled{opacity:.35}
.stApp button:focus-visible,.stApp input:focus-visible{outline:3px solid var(--cy)!important;outline-offset:2px}
.stApp [data-testid="stExpander"]{border:1px solid var(--line);border-radius:12px;background:#0A1028}
.au{color:var(--tx)}.au *{box-sizing:border-box}
.au-top{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;padding:14px 22px;border-radius:16px;background:linear-gradient(90deg,#0B1536,#17195A);border:1px solid var(--line);margin-bottom:14px;box-shadow:0 0 24px rgba(139,92,246,.18)}
.au-brand{font-weight:800;font-size:clamp(1.2rem,2vw,2rem);letter-spacing:.04em;color:#fff}
.au-sub{font-size:clamp(.75rem,1vw,1rem);color:var(--mu);letter-spacing:.16em;text-transform:uppercase;margin-top:2px}
.au-pill{display:inline-block;padding:6px 14px;border-radius:999px;font-size:.8rem;font-weight:800;letter-spacing:.16em;margin-left:8px}
.au-live{background:rgba(52,211,153,.12);color:var(--ok);border:1px solid rgba(52,211,153,.5)}
.au-paused{background:rgba(251,191,36,.12);color:var(--wn);border:1px solid rgba(251,191,36,.5)}
.au-idle{background:rgba(154,167,204,.12);color:var(--mu);border:1px solid rgba(154,167,204,.4)}
.au-conn{display:inline-block;font-size:.78rem;font-weight:700;letter-spacing:.06em;padding:6px 10px;border-radius:8px;margin-left:8px}
.au-c-ok{color:var(--ok);background:rgba(52,211,153,.08)}.au-c-warn{color:var(--wn);background:rgba(251,191,36,.12)}.au-c-bad{color:#fff;background:#B91C1C}
.au-card{background:var(--panel);border:1px solid var(--line);border-radius:18px;padding:22px 26px;margin-bottom:14px}
.au-hero{border-color:#3B3A9A;box-shadow:0 0 30px rgba(34,211,238,.14);background:radial-gradient(900px 320px at 0% 0%,#1B1E63 0%,var(--panel) 62%)}
.au-kicker{font-size:.85rem;font-weight:800;letter-spacing:.22em;color:var(--cy);text-transform:uppercase}
.au-tag{display:inline-block;margin-top:12px;padding:5px 12px;border-radius:8px;background:rgba(139,92,246,.18);border:1px solid rgba(139,92,246,.6);color:#D8C8FF;font-size:.85rem;font-weight:700;letter-spacing:.12em;text-transform:uppercase}
.au-pname{font-size:clamp(2.2rem,4.6vw,5rem);font-weight:800;line-height:1.05;margin-top:10px;color:#fff;text-shadow:0 0 22px rgba(34,211,238,.35)}
.au-meta{font-size:clamp(1rem,1.7vw,1.9rem);color:var(--mu);margin-top:8px}
.au-grid{display:grid;grid-template-columns:1fr 1.3fr 1.3fr;gap:20px;margin-top:22px;padding-top:18px;border-top:1px solid var(--line)}
.au-lbl{font-size:clamp(.7rem,.9vw,.95rem);letter-spacing:.16em;color:var(--mu);text-transform:uppercase;font-weight:700}
.au-val{font-size:clamp(1.3rem,2.2vw,2.4rem);font-weight:700;margin-top:4px;font-variant-numeric:tabular-nums;color:#fff}
.au-bid{font-size:clamp(2.2rem,4.8vw,5.2rem);font-weight:800;line-height:1.05;margin-top:2px;color:var(--cy);font-variant-numeric:tabular-nums;text-shadow:0 0 20px rgba(34,211,238,.55);animation-duration:.7s;animation-timing-function:ease-out}
.au-lead{font-size:clamp(1.3rem,2.4vw,2.6rem);font-weight:800;margin-top:4px;color:#fff}
.au-small{font-size:clamp(.85rem,1.1vw,1.1rem);color:var(--mu);margin-top:2px}.au-muted{color:#7380A8}
.au-call{margin-top:18px;padding:14px;text-align:center;font-weight:800;font-size:clamp(1.2rem,2.4vw,2.4rem);letter-spacing:.3em;border-radius:12px;background:rgba(232,121,249,.12);color:var(--mg);border:1px solid rgba(232,121,249,.55)}
.au-compact .au-pname{font-size:clamp(1.8rem,3vw,2.8rem)}.au-compact .au-bid{font-size:clamp(1.8rem,3vw,2.8rem)}
.au-sec{font-size:.8rem;font-weight:800;letter-spacing:.2em;color:var(--cy);text-transform:uppercase;margin:2px 0 12px}
.au-tbl{width:100%;border-collapse:collapse}
.au-tbl th{text-align:left;font-size:.72rem;letter-spacing:.14em;color:var(--mu);text-transform:uppercase;padding:6px 8px;border-bottom:1px solid var(--line)}
.au-tbl td{padding:10px 8px;border-bottom:1px solid #141E45;font-size:clamp(.95rem,1.3vw,1.4rem);vertical-align:middle;font-variant-numeric:tabular-nums}
.au-tbl .r{text-align:right}.au-tbl tr.lead td{background:rgba(34,211,238,.08)}.au-tbl .tm{font-weight:800}.au-tbl .mg{font-size:.8rem;color:var(--mu)}
.au-bar{height:5px;border-radius:3px;background:#17214A;margin-top:6px;overflow:hidden}.au-bar i{display:block;height:100%;background:linear-gradient(90deg,var(--vi),var(--cy))}
.au-chip{display:inline-block;padding:3px 10px;border-radius:999px;font-size:.72rem;font-weight:800;letter-spacing:.1em}
.au-k-lead{background:var(--cy);color:#04121A}.au-k-in{background:rgba(52,211,153,.15);color:var(--ok)}.au-k-out{background:rgba(248,113,113,.15);color:var(--bad)}.au-k-full{background:rgba(154,167,204,.18);color:var(--mu)}
.au-sold{text-align:center;padding:44px 24px;border-color:#7C3AED;background:radial-gradient(800px 300px at 50% 0%,#2A1668 0%,var(--panel) 70%);animation:auglow 3s ease-in-out infinite alternate}
.au-stamp{font-size:clamp(1.2rem,2.2vw,2.4rem);font-weight:800;letter-spacing:.5em;color:var(--mg)}
.au-big{font-size:clamp(2.4rem,5vw,5.4rem);font-weight:800;color:#fff;line-height:1.05;margin-top:12px}
.au-price{font-size:clamp(2rem,4vw,4.2rem);font-weight:800;color:var(--cy);margin-top:12px;text-shadow:0 0 20px rgba(34,211,238,.5)}
.au-stats{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-bottom:12px}
.au-stat{background:var(--panel);border:1px solid var(--line);border-radius:14px;padding:12px 16px}.au-stat .au-val{font-size:1.4rem}
.au-note{padding:12px 16px;border-radius:12px;font-weight:700;margin:8px 0}
.au-n-ok{background:rgba(52,211,153,.1);border:1px solid rgba(52,211,153,.5);color:var(--ok)}
.au-n-warn{background:rgba(251,191,36,.1);border:1px solid rgba(251,191,36,.5);color:var(--wn)}
.au-n-bad{background:rgba(248,113,113,.12);border:1px solid rgba(248,113,113,.55);color:var(--bad)}
.au-banner{padding:14px 18px;border-radius:12px;font-weight:800;margin-bottom:12px;text-align:center;letter-spacing:.04em}
.au-foot{display:flex;gap:28px;flex-wrap:wrap;justify-content:center;color:var(--mu);font-size:clamp(.85rem,1.1vw,1.1rem);margin-top:6px}.au-foot b{color:#fff}
.au-home{display:grid;grid-template-columns:repeat(3,1fr);gap:18px;margin-top:10px}
.au-home a{display:block;text-decoration:none;background:var(--panel);border:1px solid var(--line);border-radius:18px;padding:26px;color:var(--tx)}
.au-home a:hover,.au-home a:focus-visible{border-color:var(--cy);box-shadow:0 0 20px rgba(34,211,238,.3)}
.au-home .h{font-size:1.25rem;font-weight:800;margin-bottom:6px}.au-home .d{color:var(--mu);line-height:1.45}
@keyframes bump0{0%{transform:scale(1)}40%{transform:scale(1.06)}100%{transform:scale(1)}}
@keyframes bump1{0%{transform:scale(1)}40%{transform:scale(1.06)}100%{transform:scale(1)}}
@keyframes auglow{from{box-shadow:0 0 10px rgba(139,92,246,.2)}to{box-shadow:0 0 48px rgba(139,92,246,.55)}}
@media(max-width:900px){.au-grid{grid-template-columns:1fr 1fr}.au-stats{grid-template-columns:1fr 1fr}.au-home{grid-template-columns:1fr}}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}
/* Reference-inspired charcoal auction room theme */
:root{--bg:#171717;--panel:#232323;--line:#343434;--cy:#e7e7e7;--vi:#3b82f6;--mg:#d1d5db;--tx:#f5f5f5;--mu:#a8a8a8;--ok:#35d66f;--wn:#fbbf24;--bad:#ff6868}
.stApp{background:#202020!important;font-family:Inter,system-ui,-apple-system,"Segoe UI",sans-serif!important}
.block-container{max-width:1500px;padding-top:.7rem!important}
.au-top{background:#262626;border:1px solid #2e2e2e;border-radius:5px;box-shadow:none;padding:13px 20px;margin-bottom:16px}
.au-brand{font-size:clamp(1.05rem,1.5vw,1.4rem);letter-spacing:0;color:#fff}
.au-sub{letter-spacing:.1em;font-size:.72rem}
.au-card{background:#232323;border:1px solid #2d2d2d;border-radius:10px;padding:16px;margin-bottom:14px;box-shadow:0 7px 20px rgba(0,0,0,.16)}
.au-hero{background:#232323;border-color:#303030;box-shadow:none}
.au-kicker{color:#aaa;letter-spacing:.12em}
.au-tag{background:#333;border-color:#4a4a4a;color:#ddd}
.au-pname{font-size:clamp(1.7rem,3vw,3rem);text-shadow:none}
.au-grid{gap:12px;margin-top:16px;padding-top:14px;border-color:#3b3b3b}
.au-lbl{letter-spacing:.08em}
.au-val{font-size:clamp(1.1rem,1.8vw,1.8rem)}
.au-bid{color:#f4f4f4;text-shadow:none;font-size:clamp(1.8rem,3vw,3.4rem)}
.au-lead{font-size:clamp(1rem,1.7vw,1.6rem)}
.au-call{background:#292929;color:#f0f0f0;border-color:#555;letter-spacing:.18em}
.au-sec{color:#eee;letter-spacing:.12em}
.au-tbl th{border-color:#444}.au-tbl td{border-color:#353535;font-size:clamp(.78rem,1vw,1rem);padding:8px 7px}
.au-tbl tr.lead td{background:rgba(37,136,255,.12)}
.au-bar{background:#414141}.au-bar i{background:#2588ff}
.au-k-lead{background:#2588ff;color:#fff}.au-k-in{background:rgba(53,214,111,.13);color:#35d66f}
.au-k-out{background:rgba(255,104,104,.13);color:#ff6868}.au-k-full{background:#383838;color:#c4c4c4}
.au-sold{background:#252525;border-color:#444;animation:none}.au-stamp{color:#e8e8e8;letter-spacing:.25em}
.au-price{color:#fff;text-shadow:none}.au-stat{background:#232323;border-color:#343434;border-radius:8px}
.au-n-ok{background:rgba(53,214,111,.1)}.au-n-warn{background:rgba(251,191,36,.1)}
.au-home a{background:#232323;border-color:#343434;border-radius:10px}
.au-dashboard-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.au-manager{background:#2a2a2a;border:1px solid #343434;border-radius:7px;padding:10px;min-width:0}
.au-manager-icon{height:66px;border-radius:5px;background:#373737;display:flex;align-items:center;justify-content:center;font-size:27px;margin-bottom:8px}
.au-manager-team{font-size:.82rem;font-weight:800;overflow-wrap:anywhere}
.au-manager-name{font-size:.7rem;color:#aaa;margin-top:3px;overflow-wrap:anywhere}
.au-host-art{height:92px;border:2px solid #35d66f;border-radius:5px;background:linear-gradient(135deg,#8abed0,#b7d5dc);color:#172126;display:flex;align-items:center;justify-content:center;font-size:34px}
.au-live-tag{float:right;background:#ff3157;color:white;padding:3px 7px;border-radius:3px;font-size:.65rem;font-weight:800;margin-top:-25px;position:relative}
.au-current-bid{font-size:clamp(1.9rem,3vw,2.8rem);font-weight:800;text-align:center;color:#f5f5f5;letter-spacing:-.04em}
.au-current-caption{text-align:center;font-weight:800;font-size:.8rem;margin-bottom:12px}
.au-bid-sub{text-align:center;color:#bbb;font-size:.7rem;margin:6px 0}
.au-history-item{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:9px 0;border-bottom:1px solid #3a3a3a;font-size:.72rem}
.au-history-item:last-child{border-bottom:0}
.au-teamstats{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:9px}
.au-teamstat{background:#191919;padding:8px;border-radius:5px;min-width:0}
.au-teamstat-title{display:flex;justify-content:space-between;gap:4px;font-size:.68rem;margin-bottom:6px}
.au-teamstat-row{display:flex;justify-content:space-between;gap:4px;background:#343434;border-radius:3px;padding:5px 6px;margin:3px 0;font-size:.63rem}
@media(max-width:1050px){.au-teamstats{grid-template-columns:1fr}.au-pname{font-size:1.7rem}}
@media(max-width:760px){.au-dashboard-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.au-grid{grid-template-columns:1fr 1fr}.au-teamstats{grid-template-columns:repeat(2,minmax(0,1fr))}}
/* ISC logo, photos, neon leader */
.au-brandrow{display:flex;align-items:center;gap:14px}
.au-logo{height:56px;width:56px;object-fit:contain;background:#fff;border-radius:10px;padding:3px;flex:none}
.au-herorow{display:flex;gap:18px;align-items:center}
.au-photo{width:clamp(84px,9vw,150px);height:clamp(84px,9vw,150px);border-radius:14px;object-fit:cover;border:2px solid #3b3b3b;background:#333;flex:none;display:block}
.au-timg{max-height:100%;max-width:100%;object-fit:contain;padding:3px}
.au-manager{position:relative;transition:box-shadow .25s,opacity .25s,transform .25s}
.au-manager-lead{border-color:#22f0ff;transform:scale(1.03);z-index:1;background:#10282e;
 box-shadow:0 0 6px #22f0ff,0 0 20px rgba(34,240,255,.75),0 0 44px rgba(139,92,246,.6),inset 0 0 16px rgba(34,240,255,.25);animation:neonpulse 1.3s ease-in-out infinite alternate}
.au-manager-lead .au-manager-team{color:#7ff6ff;text-shadow:0 0 10px rgba(34,240,255,.9)}
.au-manager-lead .au-manager-icon{background:#173b44}
.au-leadbadge{position:absolute;top:5px;right:5px;z-index:2;background:#22f0ff;color:#04121A;font-size:.55rem;font-weight:900;letter-spacing:.12em;padding:2px 6px;border-radius:4px;box-shadow:0 0 10px #22f0ff}
.au-manager-out{opacity:.4;filter:grayscale(.7)}
.au-tbl tr.lead td{background:rgba(34,240,255,.16)}.au-tbl tr.lead td:first-child{box-shadow:inset 3px 0 0 #22f0ff}
.au-hero .au-lead{color:#7ff6ff;text-shadow:0 0 12px rgba(34,240,255,.8)}
@keyframes neonpulse{from{box-shadow:0 0 4px #22f0ff,0 0 14px rgba(34,240,255,.55),0 0 28px rgba(139,92,246,.4),inset 0 0 10px rgba(34,240,255,.18)}to{box-shadow:0 0 8px #22f0ff,0 0 26px rgba(34,240,255,.9),0 0 56px rgba(139,92,246,.75),inset 0 0 20px rgba(34,240,255,.32)}}
</style>"""


def html_block(markup: str) -> None:
    st.markdown(markup.replace("\n", ""), unsafe_allow_html=True)


def conn_html(sn: Snap) -> str:
    if not sn.persistent:
        return '<span class="au-conn au-c-warn">DEMO MODE · NOT SAVED</span>'
    if not sn.ok:
        return '<span class="au-conn au-c-bad">OFFLINE · showing last known state</span>'
    return f'<span class="au-conn au-c-ok">● SYNCED · rev {sn.rev} · {datetime.fromtimestamp(sn.synced, IST):%H:%M:%S}</span>'


def banner_html(sn: Snap, admin: bool = False) -> str:
    out = ""
    if not sn.persistent and sn.view is not None:
        out += ('<div class="au au-banner au-n-warn">DEMO MODE: data lives only in memory and disappears when the app restarts. '
                'Do NOT use this for the real event. Add the Supabase secrets.</div>')
    if not sn.ok:
        out += f'<div class="au au-banner au-n-bad">{e(sn.error)}. Bidding is disabled until the connection returns.</div>'
    return out


def topbar(s: dict, sn: Snap, right: str = "") -> None:
    cfg = s["settings"]
    pill = ('<span class="au-pill au-paused">PAUSED</span>' if s["paused"] else
            '<span class="au-pill au-live">LIVE</span>' if s["current"] else '<span class="au-pill au-idle">STANDBY</span>')
    logo = static_img("", "logo")
    logo_html = f'<img class="au-logo" src="{e(logo)}" alt="Sports committee logo">' if logo else ""
    ev = current_event()
    ev_pill = f'<span class="au-pill au-idle">{e(event_labels().get(ev, ev).upper())}</span>' if ev else ""
    html_block(banner_html(sn) + f'<div class="au"><div class="au-top"><div class="au-brandrow">{logo_html}<div><div class="au-brand">{e(cfg["title"])}</div>'
               f'<div class="au-sub">{e(cfg["subtitle"])}</div></div></div><div>{right}{ev_pill}{conn_html(sn)}{pill}</div></div></div>')


def unavailable(sn: Snap) -> None:
    html_block(f'<div class="au au-card" style="text-align:center;padding:50px"><div class="au-stamp">AUCTION UNAVAILABLE</div>'
               f'<div class="au-meta" style="margin-top:16px">{e(sn.error)}</div>'
               f'<div class="au-small" style="margin-top:10px">No data has been changed. This page retries automatically.</div></div>')


def hero_html(s: dict, compact: bool = False) -> str:
    cur = s["current"]
    p = player_of(s, cur["pid"])
    lot = [x["id"] for x in s["players"]].index(p["id"]) + 1
    leader = s["managers"].get(cur["leader"]) if cur["leader"] else None
    n = len(cur["history"]) % 2
    bid = (f'<div class="au-bid" style="animation-name:bump{n}">{money(cur["bid"])}</div>' if cur["bid"] is not None
           else '<div class="au-bid au-muted" style="font-size:2rem;text-shadow:none">No bids yet</div>')
    lead = (f'<div class="au-lead">{e(leader["team"])}</div><div class="au-small">{e(leader["name"])}</div>' if leader
            else '<div class="au-lead au-muted">Awaiting opening bid</div>')
    call = {1: "GOING ONCE", 2: "GOING TWICE"}.get(cur["call"], "")
    origin = f'<div class="au-meta">From {e(p["origin"])}</div>' if p["origin"] else ""
    tag = f'<div class="au-tag">{e(p["role"])}</div>' if p["role"] else ""
    photo = static_img("players", p["name"])
    ph = f'<img class="au-photo" src="{e(photo)}" alt="">' if photo else ""
    return (f'<div class="au au-card au-hero{" au-compact" if compact else ""}"><div class="au-herorow">{ph}<div><div class="au-kicker">Now on the block · '
            f'Lot {lot} of {len(s["players"])}</div>{tag}<div class="au-pname">{e(p["name"])}</div>{origin}</div></div>'
            f'<div class="au-grid"><div><div class="au-lbl">Base price</div><div class="au-val">{money(p["base"])}</div></div>'
            f'<div><div class="au-lbl">Current bid</div>{bid}</div><div><div class="au-lbl">Leading</div>{lead}</div></div>'
            + (f'<div class="au-call">{call}</div>' if call else "") + "</div>")


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
        sp = static_img("players", lr["player"])
        sph = f'<img class="au-photo" style="margin:0 auto 12px" src="{e(sp)}" alt="">' if sp else ""
        body = (f'<div class="au au-card au-sold">{sph}<div class="au-stamp">SOLD</div><div class="au-big">{e(lr["player"])}</div>'
                f'<div class="au-meta">{e(lr["role"])}{" · " if lr["role"] and lr["origin"] else ""}{e(lr["origin"])}</div>'
                f'<div class="au-price">{money(lr["price"])}</div>'
                f'<div class="au-lead" style="margin-top:12px">{e(lr["team"])}</div><div class="au-small">{e(lr["manager"])}</div></div>')
    elif lr:
        body = (f'<div class="au au-card" style="text-align:center;padding:44px"><div class="au-stamp" style="color:var(--mu)">UNSOLD</div>'
                f'<div class="au-big" style="color:var(--mu)">{e(lr["player"])}</div>'
                f'<div class="au-meta">Base price {money(lr["base"])} · no takers</div></div>')
    else:
        started = any(p["status"] != "pending" for p in s["players"])
        msg = "Next lot coming up" if started else "The auction will begin shortly"
        body = (f'<div class="au au-card" style="text-align:center;padding:56px"><div class="au-stamp">{msg.upper()}</div>'
                f'<div class="au-meta" style="margin-top:14px">{len(s["managers"])} managers · {len(s["players"])} players</div></div>')
    nxt = [p for p in s["players"] if p["status"] == "pending"][:3]
    if nxt:
        rows = "".join(f'<tr><td class="tm">{e(p["name"])}</td><td>{e(p["role"])}</td><td>{e(p["origin"])}</td>'
                       f'<td class="r">{money(p["base"])}</td></tr>' for p in nxt)
        body += f'<div class="au au-card"><div class="au-sec">Up next</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>'
    return body


def board_html(s: dict) -> str:
    cur, cfg, rows = s["current"], s["settings"], ""
    for m in s["managers"].values():
        full = len(m["squad"]) >= cfg["max_squad"]
        chip, cls = "", ""
        if cur:
            if m["id"] == cur["leader"]:
                chip, cls = '<span class="au-chip au-k-lead">LEADING</span>', "lead"
            elif m["id"] in cur["out"]:
                chip = '<span class="au-chip au-k-out">OUT</span>'
            elif full:
                chip = '<span class="au-chip au-k-full">FULL</span>'
            elif max_bid(s, m) < min_next(s):
                chip = '<span class="au-chip au-k-full">LIMIT</span>'
            else:
                chip = '<span class="au-chip au-k-in">IN</span>'
        elif full:
            chip = '<span class="au-chip au-k-full">FULL</span>'
        pct = max(0, min(100, m["purse"] / max(1, cfg["purse"]) * 100))
        rows += (f'<tr class="{cls}"><td><div class="tm">{e(m["team"])}</div><div class="mg">{e(m["name"])}</div></td>'
                 f'<td class="r">{money(m["purse"])}<div class="au-bar"><i style="width:{pct:.0f}%"></i></div></td>'
                 f'<td class="r">{len(m["squad"])}/{cfg["max_squad"]}</td><td class="r">{chip}</td></tr>')
    return (f'<div class="au au-card"><div class="au-sec">Team purses &amp; squads</div><table class="au-tbl"><thead><tr><th>Team</th>'
            f'<th class="r">Purse left</th><th class="r">Squad</th><th class="r">Status</th></tr></thead><tbody>{rows}</tbody></table></div>')


def recent_html(s: dict, n: int = 5) -> str:
    sold = list(reversed(s["sales"]))[:n]
    if not sold:
        return ""
    rows = "".join(f'<tr><td class="tm">{e(player_of(s, x["pid"])["name"])}</td><td>{e(s["managers"][x["mid"]]["team"])}</td>'
                   f'<td class="r">{money(x["price"])}</td></tr>' for x in sold)
    return f'<div class="au au-card"><div class="au-sec">Recently sold</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>'


def footer_html(s: dict) -> str:
    pl = s["players"]
    c = lambda *k: sum(p["status"] in k for p in pl)
    return (f'<div class="au au-foot"><span>Sold <b>{c("sold")}</b></span><span>Unsold <b>{c("unsold")}</b></span>'
            f'<span>Remaining <b>{c("pending", "live")}</b></span>'
            f'<span>Total spent <b>{money(sum(x["price"] for x in s["sales"]))}</b></span></div>')



def screen_managers_html(s: dict) -> str:
    """Compact manager cards for the projector. Only public team/manager names are shown."""
    icons = ["👨🏻‍💼", "👩🏻‍💼", "🧑🏻‍💼", "👨🏽‍💻", "👩🏽‍💼", "🧑🏾‍💼", "👨🏻‍💻", "👩🏻‍💻"]
    cards = ""
    cur = s.get("current")
    leader = cur["leader"] if cur else None
    outs = set(cur["out"]) if cur else set()
    for i, m in enumerate(s["managers"].values()):
        logo = static_img("teams", m["team"])
        icon = f'<img class="au-timg" src="{e(logo)}" alt="">' if logo else icons[i % len(icons)]
        is_lead = leader is not None and m["id"] == leader
        cls = "au-manager" + (" au-manager-lead" if is_lead else " au-manager-out" if m["id"] in outs else "")
        badge = '<div class="au-leadbadge">LEADING</div>' if is_lead else ""
        cards += (f'<div class="{cls}">{badge}<div class="au-manager-icon">{icon}</div>'
                  f'<div class="au-manager-team">{e(m["team"])}</div>'
                  f'<div class="au-manager-name">{e(m["name"])}</div></div>')
    return (f'<div class="au au-card"><div class="au-sec">Auction managers</div>'
            f'<div class="au-dashboard-grid">{cards}</div></div>')


def screen_host_html(s: dict) -> str:
    return (f'<div class="au au-card"><div class="au-host-art">🎙</div><span class="au-live-tag">LIVE AUCTION</span>'
            f'<div style="font-size:.95rem;font-weight:800;margin-top:12px">{e(s["settings"]["title"])}</div>'
            f'<div class="au-manager-name">Auction control room · projector view</div></div>')


def screen_current_bid_html(s: dict) -> str:
    cur = s["current"]
    if not cur:
        return idle_html(s)
    p = player_of(s, cur["pid"])
    leader = s["managers"].get(cur["leader"]) if cur["leader"] else None
    bid_text = money(cur["bid"]) if cur["bid"] is not None else "No bids yet"
    leader_text = e(leader["team"]) if leader else "Awaiting opening bid"
    html = (f'<div class="au au-card"><div class="au-current-bid">{e(bid_text)}</div>'
            f'<div class="au-current-caption">CURRENT BID</div>'
            f'<div class="au-bid-sub">{e(p["name"])}</div>'
            f'<div class="au-bid-sub">Leading team: <b>{leader_text}</b></div>')
    if cur["call"]:
        html += f'<div class="au-call" style="font-size:.9rem;padding:9px">{e({1: "GOING ONCE", 2: "GOING TWICE"}.get(cur["call"], ""))}</div>'
    html += '</div>'
    if cur["history"]:
        html += '<div class="au au-card"><div class="au-sec">Bid history</div>'
        for h in reversed(cur["history"][-5:]):
            manager = s["managers"].get(h["mid"], {})
            html += (f'<div class="au-history-item"><div><b>{e(manager.get("team", "Team"))}</b>'
                     f'<div class="au-manager-name">{e(clock(h["t"]))}</div></div>'
                     f'<b>{e(money(h["amt"]))}</b></div>')
        html += '</div>'
    return html


CRICKET_CATS = [
    ("Batsmen", ("bat", "batter", "batsman")),
    ("Keepers", ("keeper", "wicketkeeper", "wicket-keeper")),
    ("All-rounders", ("allrounder", "all-rounder", "all rounder")),
    ("Fast bowlers", ("fast bowler", "pace bowler", "bowler")),
    ("Spinners", ("spinner", "spin bowler")),
]


def screen_team_stats_html(s: dict) -> str:
    """Public squad-category counts derived from the actual sale/player records."""
    categories = CRICKET_CATS
    roles = [str(p.get("role", "")).strip() for p in s["players"] if str(p.get("role", "")).strip()]
    exact = False
    if roles:
        low = [r.lower().replace("_", " ") for r in roles]
        hits = sum(any(t in r for _, terms in CRICKET_CATS for t in terms) for r in low)
        if hits * 2 < len(roles):                    # not a cricket roster: one row per distinct role (football, etc.)
            first, counts = {}, {}
            for r in roles:
                k = r.lower().replace("_", " ")
                first.setdefault(k, r)
                counts[k] = counts.get(k, 0) + 1
            top = sorted(counts, key=lambda k: (-counts[k], k))[:6]
            categories, exact = [(first[k], (k,)) for k in top], True
    team_cards = ""
    sales_by_manager = {mid: [] for mid in s["managers"]}
    for sale in s["sales"]:
        if sale["mid"] in sales_by_manager:
            player = player_of(s, sale["pid"])
            if player:
                sales_by_manager[sale["mid"]].append(player)
    for mid, m in s["managers"].items():
        roster = sales_by_manager.get(mid, [])
        rows = ""
        for label, terms in categories:
            count = 0
            for player in roster:
                role = str(player.get("role", "")).lower().replace("_", " ")
                if any((term == role) if exact else (term in role) for term in terms):
                    count += 1
            rows += f'<div class="au-teamstat-row"><span>{e(label)}</span><b>{count}</b><span>/ {len(roster)}</span></div>'
        team_cards += (f'<div class="au-teamstat"><div class="au-teamstat-title"><b>{e(m["team"])}</b>'
                       f'<span>{len(roster)}/{s["settings"]["max_squad"]}</span></div>{rows}</div>')
    return f'<div class="au au-card"><div class="au-sec">Team squad stats</div><div class="au-teamstats">{team_cards}</div></div>'


def flash_show() -> None:
    f = st.session_state.get("au_flash")
    if f and time.time() - f[2] < 8:
        html_block(f'<div class="au"><div class="au-note {"au-n-ok" if f[0] else "au-n-bad"}" role="status">{e(f[1])}</div></div>')


# --------------------------------------------------------------------------- views
def view_home() -> None:
    """Neutral landing page: deliberately shows no links to the other views."""
    sn = get_store(current_event()).read()
    title = sn.view["settings"]["title"] if sn.view else "Intellics Auction Room"
    html_block(f'<div class="au"><div class="au-card" style="text-align:center;padding:64px 24px;margin-top:12vh">'
               f'<div class="au-brand" style="font-size:clamp(1.6rem,3vw,3rem)">{e(title)}</div>'
               f'<div class="au-sub" style="margin-top:12px">Please use the access link shared by the organiser</div></div></div>')


@st.fragment(run_every=POLL_SCREEN)
def screen_live(S: Store) -> None:
    """Read-only projector dashboard styled to resemble the requested charcoal auction UI.

    Bidding controls deliberately remain in the authenticated manager view (?view=bid).
    The projector must never be able to mutate auction state.
    """
    S = get_store(current_event())                    # follow the organiser's event choice on every refresh
    sn = S.read()
    if sn.view is None:
        html_block(banner_html(sn))
        unavailable(sn)
        return
    s = sn.view
    topbar(s, sn)
    left, center, right = st.columns([0.92, 1.02, 1.62], gap="small")
    with left:
        html_block(screen_host_html(s) + screen_managers_html(s))
    with center:
        html_block((hero_html(s, compact=True) if s["current"] else idle_html(s)) + recent_html(s, 5))
    with right:
        html_block(screen_current_bid_html(s) + screen_team_stats_html(s))
    html_block(footer_html(s))


def view_screen() -> None:
    screen_live(get_store(current_event()))


@st.fragment(run_every=POLL_BID)
def bid_console(S: Store) -> None:
    ss = st.session_state
    S = get_store(current_event())
    sn = S.read()
    actor = manager_session(sn)
    if sn.view is None or actor is None or actor["id"] not in sn.view["managers"]:
        if sn.view is not None:
            ss.pop("au_mgr", None)
            st.rerun(scope="app")
        html_block(banner_html(sn))
        unavailable(sn)
        return
    s, mid = sn.view, actor["id"]
    m, cfg, cur = s["managers"][mid], s["settings"], s["current"]
    topbar(s, sn, f'<span class="au-small" style="margin-right:6px">{e(m["team"])} · {e(m["name"])}</span>')
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
        can = sn.ok and not s["paused"] and cur["leader"] != mid and mid not in cur["out"] and len(m["squad"]) < cfg["max_squad"]
        if can:
            st.markdown("**Place a bid**")
            cols = st.columns(4)
            for i, (col, a) in enumerate(zip(cols, [need, need + cfg["step"], need + 2 * cfg["step"], need + 4 * cfg["step"]])):
                if col.button(money(a), key=f"q{pid}_{i}", type="primary" if i == 0 else "secondary",
                              disabled=a > cap, use_container_width=True):
                    do(S, actor, "bid", {"amount": a})
                    st.rerun(scope="fragment")
            with st.expander("Custom amount"):
                kk = f"amt_{pid}"
                ss.setdefault(kk, need)
                with st.form(f"cust_{pid}"):
                    amt = st.number_input("Your bid in lakhs (100 lakh = 1 Cr)", min_value=1, step=cfg["step"], format="%d", key=kk)
                    if st.form_submit_button("Place custom bid", type="primary"):
                        do(S, actor, "bid", {"amount": int(amt)})
                        st.rerun(scope="fragment")
            ckey = f"au_conf_{pid}"
            if ss.get(ckey):
                html_block('<div class="au"><div class="au-note au-n-warn">Withdraw from this player? You cannot re-enter unless the organiser lets you back in.</div></div>')
                c1, c2 = st.columns(2)
                if c1.button("Yes, withdraw", key=f"y{pid}", use_container_width=True):
                    ss[ckey] = False
                    do(S, actor, "withdraw")
                    st.rerun(scope="fragment")
                if c2.button("Cancel", key=f"n{pid}", use_container_width=True):
                    ss[ckey] = False
                    st.rerun(scope="fragment")
            elif st.button("Withdraw from this player", key=f"w{pid}", use_container_width=True):
                ss[ckey] = True
                st.rerun(scope="fragment")
        elif not sn.ok:
            html_block('<div class="au"><div class="au-note au-n-bad">Bidding is disabled while the connection is down.</div></div>')
        html_block(history_html(s, 4))
    if m["squad"]:
        rows = "".join(f'<tr><td class="tm">{e(x["name"])}</td><td class="r">{money(x["price"])}</td></tr>' for x in m["squad"])
        html_block(f'<div class="au au-card"><div class="au-sec">Your squad</div><table class="au-tbl"><tbody>{rows}</tbody></table></div>')


def view_bid() -> None:
    S, ss = get_store(current_event()), st.session_state
    sn = S.read()
    if manager_session(sn):
        bid_console(S)
        if st.button("Log out", key="au_logout"):
            ss.pop("au_mgr", None)
            st.rerun()
        return
    if sn.view is None:
        html_block(banner_html(sn))
        unavailable(sn)
        return
    topbar(sn.view, sn)
    if not sn.view["managers"]:
        st.info("The organiser has not added any teams yet.")
        return
    _, col, _ = st.columns([1, 1.2, 1])
    with col, st.form("au_login"):
        teams = {m["id"]: f'{m["team"]} ({m["name"]})' for m in sn.view["managers"].values()}
        pick = st.selectbox("Your team", list(teams), format_func=lambda k: teams[k])
        pin = st.text_input("PIN", type="password", max_chars=8)
        if st.form_submit_button("Enter auction room", type="primary"):
            box: dict = {}

            def check():
                state, _ = S.backend.get_state()                      # authoritative read, not the display cache
                m = (state or {}).get("managers", {}).get(pick)
                box["m"] = m
                return bool(m) and check_pin(pin.strip(), m.get("pin_hash"))

            ok, err = verify_login(S.backend, f"mgr:{current_event()}:{pick}", check, PIN_MAX_FAILS, PIN_LOCK_SECONDS) if S.backend else (False, "Not configured.")
            if ok:
                ss["au_mgr"] = {"id": pick, "ver": box["m"]["session_ver"], "exp": time.time() + MANAGER_SESSION_SECONDS,
                                "event": current_event()}
                st.rerun()
            st.error(err)


def admin_login(S: Store, pin: str) -> None:
    _, col, _ = st.columns([1, 1.2, 1])
    with col, st.form("au_admin_login"):
        pw = st.text_input("Organiser password", type="password")
        if st.form_submit_button("Sign in", type="primary") and S.backend:
            ok, err = verify_login(S.backend, "admin", lambda: hmac.compare_digest(
                hashlib.sha256(pw.encode()).digest(), hashlib.sha256(pin.encode()).digest()), ADMIN_MAX_FAILS, ADMIN_LOCK_SECONDS)
            if ok:
                st.session_state["au_admin"] = {"t0": time.time(), "last": time.time()}
                st.rerun()
            st.error(err)


@st.fragment(run_every=POLL_ADMIN)
def admin_live(S: Store) -> None:
    S = get_store(current_event())
    sn = S.read()
    actor = admin_actor()
    if actor is None:
        st.warning("Organiser session expired. Reload the page and sign in again.")
        return
    if sn.view is None:
        html_block(banner_html(sn))
        unavailable(sn)
        return
    s, cur, rev = sn.view, sn.view["current"], sn.rev
    topbar(s, sn, '<span class="au-small" style="margin-right:6px">Organiser</span>')
    flash_show()
    go = lambda action, args=None, exp=None: (do(S, admin_actor(True), action, args, exp), st.rerun(scope="fragment"))
    off = not sn.ok
    if cur:
        html_block(hero_html(s, compact=True))
        c = st.columns(4)
        has_bid = cur["bid"] is not None
        if c[0].button("Going once", use_container_width=True, disabled=off or not has_bid):
            go("call", {"n": 1})
        if c[1].button("Going twice", use_container_width=True, disabled=off or not has_bid):
            go("call", {"n": 2})
        if c[2].button("SOLD", type="primary", use_container_width=True, disabled=off or not has_bid):
            go("sold", None, rev)
        if c[3].button("Mark unsold", use_container_width=True, disabled=off or has_bid):
            go("unsold", None, rev)
        c = st.columns(3)
        if c[0].button("Undo last bid", use_container_width=True, disabled=off or not cur["history"]):
            go("undo_bid", None, rev)
        if c[1].button("Let everyone back in", use_container_width=True, disabled=off or not cur["out"]):
            go("clear_out")
        if c[2].button("Resume bidding" if s["paused"] else "Pause bidding", use_container_width=True, disabled=off):
            go("pause", {"flag": not s["paused"]})
        html_block(history_html(s, 5))
    else:
        html_block(idle_html(s))
        pend = [p for p in s["players"] if p["status"] == "pending"]
        opts = {"": "Next in queue (automatic)", **{p["id"]: f'{p["name"]} · {money(p["base"])}' for p in pend}}
        pick = st.selectbox("Bring up", list(opts), format_func=lambda k: opts[k], key="adm_pick")
        c = st.columns(4)
        if c[0].button("Bring up player", type="primary", use_container_width=True, disabled=off or not pend):
            go("bring", {"pid": pick or None})
        if c[1].button("Shuffle queue", use_container_width=True, disabled=off or len(pend) < 2):
            go("shuffle")
        if c[2].button("Re-queue unsold", use_container_width=True, disabled=off):
            go("requeue")
        if c[3].button("Resume bidding" if s["paused"] else "Pause bidding", use_container_width=True, disabled=off):
            go("pause", {"flag": not s["paused"]})
    st.divider()
    c = st.columns([1, 2])
    with c[0]:
        confirm = st.checkbox("Allow undoing the last sale", key="au_undo_ok")
        if st.button("Undo last sale", use_container_width=True, disabled=off or bool(cur) or not s["sales"] or not confirm):
            go("undo_sale", None, rev)
    c[1].caption("Saved to PostgreSQL after every action." if sn.persistent else "DEMO MODE: nothing is being saved.")
    html_block(board_html(s))


def restore_ui(S: Store, rev: int | None) -> None:
    up = st.file_uploader("Restore from a backup file", type=["json"], key="au_restore")
    if not up:
        return
    cand, note = parse_backup(up.getvalue())
    if cand is None:
        st.error(note)
        return
    st.info(f"Backup is valid: {len(cand['managers'])} teams, {len(cand['players'])} players, {len(cand['sales'])} sales. "
            f"{note} Restoring replaces ALL current auction data. Managers need new PINs unless unchanged.")
    word = st.text_input("Type RESTORE to confirm", key="au_restore_word")
    if st.button("Restore this backup", disabled=word != "RESTORE"):
        do(S, admin_actor(True), "restore", {"state": cand, "confirm": word}, rev)
        st.rerun()


def prefill_pins(text: str):
    """Fill blank PINs with random 6-digit ones BEFORE the server sees the text. Returns (text, [(team, pin)])."""
    out, made = [], []
    for line in text.splitlines():
        parts = [x.strip() for x in re.split(r"[,\t]", line)]
        if len(parts) == 2 and parts[0] and parts[1] or (len(parts) == 3 and parts[0] and parts[1] and not parts[2]):
            pin = f"{secrets.randbelow(900000) + 100000}"
            made.append((parts[0], pin))
            line = f"{parts[0]}, {parts[1]}, {pin}"
        out.append(line)
    return "\n".join(out), made


def show_new_pins() -> None:
    pins = st.session_state.get("au_newpins")
    if pins:
        html_block('<div class="au"><div class="au-note au-n-warn">Generated PINs (shown once, write them down):</div></div>')
        st.code("\n".join(f"{t}: {p}" for t, p in pins))
        if st.button("I have noted the PINs"):
            st.session_state.pop("au_newpins")
            st.rerun()


def event_switcher(S: Store, sn: Snap) -> None:
    labels, cur_ev = event_labels(), current_event()
    ids = list(labels)
    busy = bool(sn.view and sn.view["current"])
    c = st.columns([2, 1, 2], vertical_alignment="bottom")
    pick = c[0].selectbox("Active event (projector and manager screens follow this)", ids,
                          index=ids.index(cur_ev) if cur_ev in ids else 0, format_func=lambda k: labels[k], key="adm_event_pick")
    if c[1].button("Switch event", use_container_width=True, disabled=busy or pick == cur_ev, key="adm_event_go"):
        ok, msg = switch_event(pick, S.backend)
        st.session_state["au_flash"] = (ok, msg, time.time())
        st.rerun()
    c[2].caption(f"Now running: **{labels.get(cur_ev, cur_ev)}**." + (" Finish the current lot to switch." if busy else ""))


def view_admin() -> None:
    S, ss = get_store(current_event()), st.session_state
    pin = secret("ADMIN_PIN")
    sn = S.read()
    problem = admin_password_problem(pin)
    if problem:
        st.error(problem)
        return
    if S.backend is None:
        st.error(S.read().error)
        return
    if admin_actor() is None:
        if sn.view is not None:
            topbar(sn.view, sn, '<span class="au-small">Organiser</span>')
        else:
            html_block(banner_html(sn))
        admin_login(S, pin)
        return
    event_switcher(S, sn)
    live_tab, setup_tab, result_tab = st.tabs(["Live control", "Setup", "Results & backup"])
    with live_tab:
        admin_live(S)
    if sn.view is None:
        with setup_tab:
            st.error(sn.error)
        with result_tab:
            if sn.invalid:
                st.warning("The stored data is inconsistent. You can restore a known-good backup here.")
                restore_ui(S, sn.rev)
        return
    s = sn.view
    with setup_tab:
        cfg, locked = s["settings"], bool(s["sales"] or s["current"])
        flash_show()
        show_new_pins()
        st.markdown("#### Auction settings")
        if s["current"]:
            st.info("A player is on the block: bidding rules are locked. Only the title and subtitle can change.")
        with st.form("au_settings"):
            c = st.columns(2)
            title, sub = c[0].text_input("Title", cfg["title"], max_chars=80), c[1].text_input("Subtitle", cfg["subtitle"], max_chars=80)
            c = st.columns(4)
            purse = c[0].number_input("Purse per team (lakhs)", 100, 1_000_000, cfg["purse"], 100, disabled=bool(s["sales"] or s["current"]))
            squad = c[1].number_input("Max squad size", 1, 50, cfg["max_squad"], disabled=bool(s["current"]))
            step = c[2].number_input("Minimum bid step (lakhs)", 1, 10_000, cfg["step"], disabled=bool(s["current"]))
            res = c[3].number_input("Reserve per empty slot (lakhs)", 0, 10_000, cfg["reserve"], disabled=bool(s["current"]))
            if st.form_submit_button("Save settings", type="primary"):
                do(S, admin_actor(True), "settings", {"settings": {"title": title, "subtitle": sub, "purse": int(purse),
                   "max_squad": int(squad), "step": int(step), "reserve": int(res)}})
                st.rerun()
        st.caption("Money is in lakhs: 100 lakh = 1 Cr. The purse cannot change after sales start.")
        st.markdown("#### Managers (teams)")
        if s["managers"]:
            html_block('<div class="au au-card"><table class="au-tbl"><thead><tr><th>Team</th><th>Manager</th><th class="r">Purse</th></tr></thead><tbody>'
                       + "".join(f'<tr><td class="tm">{e(m["team"])}</td><td>{e(m["name"])}</td><td class="r">{money(m["purse"])}</td></tr>'
                                 for m in s["managers"].values()) + "</tbody></table></div>")
        with st.form("au_mgr"):
            txt = st.text_area("One manager per line:  Team, Manager, PIN (4-8 digits; leave the PIN out to generate one)",
                               height=120, placeholder="Apex Capital, Ravi Kumar, 482913\nNova Group, Asha Rao")
            up = st.file_uploader("...or upload a text/CSV file", type=["csv", "txt"], key="au_mfile")
            rep = st.checkbox("Replace all existing managers", disabled=locked)
            if st.form_submit_button("Save managers", type="primary"):
                data = up.getvalue().decode("utf-8-sig", errors="replace") if up and up.size <= MAX_UPLOAD_BYTES else txt
                data, made = prefill_pins(data)
                res_ = do(S, admin_actor(True), "add_managers", {"text": data, "replace": rep})
                if res_.ok and made:
                    ss["au_newpins"] = made
                st.rerun()
        with st.expander("Reset one manager's PIN (also signs them out)"):
            with st.form("au_pin"):
                who = st.selectbox("Team", list(s["managers"]) or [""], format_func=lambda k: s["managers"][k]["team"] if k else "-")
                newp = st.text_input("New PIN (blank = generate)", max_chars=8)
                if st.form_submit_button("Reset PIN") and who:
                    p_ = newp.strip() or f"{secrets.randbelow(900000) + 100000}"
                    if do(S, admin_actor(True), "reset_pin", {"mid": who, "pin": p_}).ok:
                        ss["au_newpins"] = [(s["managers"][who]["team"], p_)]
                    st.rerun()
        st.markdown("#### Players")
        st.caption(f"{len(s['players'])} players loaded, {sum(p['status'] == 'pending' for p in s['players'])} waiting. "
                   "CSV columns: name, origin, role, base_price (whole lakhs).")
        up = st.file_uploader("Upload CSV", type=["csv", "txt"], key="au_csv")
        txt = st.text_area("...or paste rows (with the header line)", height=110, placeholder="name,origin,role,base_price\nAarav Sharma,Delhi,Batter,100")
        rep = st.checkbox("Replace all existing players", disabled=locked, key="au_prep")
        c = st.columns(3)
        if c[0].button("Add players", type="primary", use_container_width=True):
            data = up.getvalue().decode("utf-8-sig", errors="replace") if up and up.size <= MAX_UPLOAD_BYTES else txt
            do(S, admin_actor(True), "add_players", {"text": data, "replace": rep})
            st.rerun()
        c[1].download_button("CSV template", "name,origin,role,base_price\nAarav Sharma,Delhi,Batter,100\n", "players_template.csv", use_container_width=True)
        if c[2].button("Load demo data", use_container_width=True, disabled=locked):
            demo = "\n".join(f"{t}, Manager {i}, {100000 + secrets.randbelow(899999)}" for i, t in enumerate(
                ["Apex Capital", "Meridian Ventures", "Northwind Holdings", "Sterling Partners", "Vertex Group", "Zenith Equity"], 1))
            demo_text, made = demo, [(l.split(",")[0], l.split(",")[2].strip()) for l in demo.splitlines()]
            if do(S, admin_actor(True), "demo", {"manager_text": demo_text}).ok:
                ss["au_newpins"] = made
            st.rerun()
        st.markdown("#### Danger zone")
        word = st.text_input("Type RESET to enable the reset button (purses, squads and sales are wiped)", key="au_reset_word")
        if st.button("Reset auction", disabled=word != "RESET"):
            do(S, admin_actor(True), "reset", {"confirm": word}, sn.rev)
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
            w.writerow([i, csv_safe(p["name"]), csv_safe(p["origin"]), csv_safe(p["role"]), p["base"], csv_safe(m["team"]), csv_safe(m["name"]), x["price"]])
        c = st.columns(2)
        c[0].download_button("Download sales (CSV)", buf.getvalue(), "auction_sales.csv", use_container_width=True)
        try:
            full, _ = S.backend.get_state()
            c[1].download_button("Download full backup (JSON)", json.dumps(make_backup(full), indent=1), "auction_backup.json",
                                 use_container_width=True)
        except BackendError as exc:
            c[1].error(f"Backup unavailable: {exc}")
        st.caption("Backups contain no PINs. After a restore, managers whose PIN is missing need a new one in Setup.")
        restore_ui(S, sn.rev)
        with st.expander("Activity log"):
            for entry in reversed(s["log"][-60:]):
                st.text(f'{clock(entry["t"])}  {entry["text"]}')


def main() -> None:
    st.set_page_config(page_title="Auction Room", page_icon="🔨", layout="wide", initial_sidebar_state="collapsed")
    st.markdown(CSS, unsafe_allow_html=True)
    view = str(st.query_params.get("view", "") or "").lower()
    {"screen": view_screen, "bid": view_bid, "admin": view_admin}.get(view, view_home)()


if __name__ == "__main__":
    main()
