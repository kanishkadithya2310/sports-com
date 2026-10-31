"""Intellics Auction Room v2: a live, play-money player auction (5-10 managers + projector).

Run:  streamlit run auction_app.py

VIEWS (same app, chosen by the web address)
  ?view=screen   Projector display (read-only, no login, shows no secrets)
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
  * Roles are enforced in apply_action() on the server. The organiser runs the whole auction live: they place
    bids on behalf of teams (any amount, validated against purse and rules) and can edit base prices.
    There is no manager-facing screen any more.
"""
from __future__ import annotations

import base64
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
AUTO_NEXT_SECONDS = 6              # automatic mode: pause on the sold/unsold result, then bring up the next player
SORT_LABELS = {"role": "By role (A-Z)", "role_base": "By role, then base price (high to low)",
               "base": "By base price (high to low)", "name": "By name (A-Z)"}
STATIC_DIR = Path(__file__).resolve().parent / "static"
IMG_EXTS = (".png", ".jpg", ".jpeg", ".webp")
DEFAULTS = {"title": "Intellics Auction Room", "subtitle": "Live Player Auction", "purse": 10000,
            "max_squad": 10, "step": 25, "reserve": 20}


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
    """Image for static/<kind>/<slug(name)>.png|jpg|jpeg|webp if that file exists, else ''. kind '' = static/ itself.

    The picture is shrunk and embedded in the page as a data: URI, so it shows even when the host does not
    serve /app/static (no extra server setting needed)."""
    sl = slug(name)
    if not sl:
        return ""
    base = (STATIC_DIR / kind) if kind else STATIC_DIR
    for ext in IMG_EXTS:
        f = base / (sl + ext)
        if not f.is_file():
            continue
        try:
            from PIL import Image

            im = Image.open(f)
            im.thumbnail((200, 200) if not kind else (640, 800) if kind == "players" else (256, 256))
            buf = io.BytesIO()
            if im.mode in ("RGBA", "LA", "P"):
                im.convert("RGBA").save(buf, "PNG", optimize=True)
                mime = "image/png"
            else:
                im.convert("RGB").save(buf, "JPEG", quality=85, optimize=True)
                mime = "image/jpeg"
            return f"data:{mime};base64," + base64.b64encode(buf.getvalue()).decode("ascii")
        except Exception:  # pragma: no cover - fall back to the served file
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
            "last_result": None, "sales": [], "log": [], "paused": False, "auto_next": False, "role_filter": None, "base_price": None, "rev": 0}


def migrate_state(raw: dict) -> dict:
    """Upgrade a state from the original app (or fill gaps) without changing its meaning."""
    s = copy.deepcopy(raw)
    base = new_state()
    for k, v in base.items():
        s.setdefault(k, v)
    s["settings"] = {**DEFAULTS, **(s["settings"] if isinstance(s["settings"], dict) else {})}
    if s["settings"].get("max_squad") == 8:          # the old default; squads are now capped at 10 players
        s["settings"]["max_squad"] = DEFAULTS["max_squad"]
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


def base_price_of(s: dict) -> int:
    """The single base price: the saved one, else the most common base among players, else the default."""
    bp = s.get("base_price")
    if isinstance(bp, int) and not isinstance(bp, bool) and bp > 0:
        return bp
    bases = [p["base"] for p in s.get("players", []) if isinstance(p.get("base"), int)]
    return max(set(bases), key=bases.count) if bases else 100


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


def f_admin_bid(s, actor, a):
    """Organiser places a bid for a team with any amount at or above the minimum (still limited by purse rules)."""
    cur, m = s["current"], s["managers"].get(a.get("mid"))
    if not cur:
        return False, "No player is up for auction right now."
    if s["paused"]:
        return False, "Bidding is paused. Resume bidding first."
    if not m:
        return False, "Pick a team."
    if len(m["squad"]) >= s["settings"]["max_squad"]:
        return False, f"{m['team']} already has a full squad."
    if cur["leader"] == m["id"]:
        return False, f"{m['team']} already holds the highest bid."
    amount = parse_amount(a.get("amount"))
    if amount is None:
        return False, "Enter a whole number of lakhs."
    need = min_next(s)
    if amount < need:
        return False, f"The minimum bid is now {money(need)}."
    cap = max_bid(s, m)
    if amount > cap:
        return False, (f"{m['team']} can bid at most {money(max(cap, 0))} (purse {money(m['purse'])}, "
                       f"{money(reserve_after(s, m))} reserved for remaining squad slots).")
    if m["id"] in cur["out"]:
        cur["out"].remove(m["id"])                      # the organiser is bidding for them, so they are back in
    cur["bid"], cur["leader"], cur["call"] = amount, m["id"], 0
    cur["history"].append({"t": now_iso(), "mid": m["id"], "amt": amount})
    _log(s, f"BID {m['team']} {money(amount)} on {player_of(s, cur['pid'])['name']}")
    res = _auto(s)
    return True, (f"Bid accepted. {res}" if res else f"{m['team']} leads at {money(amount)}.")


def f_admin_out(s, actor, a):
    """Organiser marks a team as out for the current player."""
    cur, m = s["current"], s["managers"].get(a.get("mid"))
    if not cur:
        return False, "No player is up for auction."
    if not m:
        return False, "Pick a team."
    if cur["leader"] == m["id"]:
        return False, f"{m['team']} holds the highest bid, so it cannot be marked out."
    if m["id"] in cur["out"]:
        return False, f"{m['team']} is already out."
    cur["out"].append(m["id"])
    _log(s, f"OUT {m['team']}")
    res = _auto(s)
    return True, (f"{m['team']} is out. {res}" if res else f"{m['team']} is out for this player.")


def f_set_base(s, actor, a):
    """Organiser changes a player's base price live (only before the first bid, so bid history stays valid)."""
    p = player_of(s, a.get("pid"))
    base = parse_amount(a.get("base"))
    if not p or p["status"] not in ("pending", "live", "unsold"):
        return False, "Only queued, live or unsold players can be changed."
    if base is None or base > s["settings"]["purse"]:
        return False, f"Base price must be a whole number of lakhs, at most the purse ({money(s['settings']['purse'])})."
    cur = s["current"]
    if p["status"] == "live" and cur and cur["bid"] is not None:
        return False, "This player already has a bid. Undo the bids first to change the base price."
    old, p["base"] = p["base"], base
    _log(s, f"BASE {p['name']} {money(old)} -> {money(base)}")
    return True, f"{p['name']} base price is now {money(base)}."


def f_bring(s, actor, a):
    if s["current"]:
        return False, "Finish the current player first."
    if not s["managers"]:
        return False, "Add managers first."
    pid, rf = a.get("pid"), s.get("role_filter")
    pend = [p for p in s["players"] if p["status"] == "pending" and (not rf or p.get("role") == rf)]
    p = player_of(s, pid) if pid else (pend[0] if pend else None)      # a player picked by hand ignores the role filter
    if not p or p["status"] not in ("pending", "unsold"):
        return False, f"No {rf} player left in the queue." if rf else "No player left in the queue."
    p["status"] = "live"
    s["current"] = {"pid": p["id"], "bid": None, "leader": None, "out": [], "history": [], "call": 0, "opened": now_iso()}
    s["last_result"] = None
    _log(s, f"UP {p['name']}")
    return True, f"{p['name']} is up for auction."


def f_set_role(s, actor, a):
    """Only players of this role come up for bidding (None = everyone)."""
    role = a.get("role") or None
    if role and not any(p.get("role") == role and p["status"] != "sold" for p in s["players"]):
        return False, f"No waiting players with the role {role}."
    s["role_filter"] = role
    _log(s, f"Role: {role or 'all roles'}")
    return True, f"Only {role} players will come up for bidding." if role else "All roles will come up for bidding."


def f_set_base_all(s, actor, a):
    """One base price for every player who is still waiting or unsold."""
    base = parse_amount(a.get("base"))
    if s["current"]:
        return False, "Finish the current player before changing the base price."
    if base is None or base > s["settings"]["purse"]:
        return False, f"Base price must be a whole number of lakhs, at most the purse ({money(s['settings']['purse'])})."
    n = 0
    for p in s["players"]:
        if p["status"] in ("pending", "unsold"):
            p["base"] = base
            n += 1
    s["base_price"] = base
    _log(s, f"Base price for all players: {money(base)}")
    return True, f"Base price is now {money(base)} for all {n} waiting player(s)."


def f_call(s, actor, a):
    cur, n = s["current"], a.get("n")
    if n not in (1, 2):
        return False, "Call must be going once or going twice."
    if not cur or cur["bid"] is None:
        return False, "There is no bid to call on."
    cur["call"] = n
    return True, "Going once..." if n == 1 else "Going twice..."


def f_sell(s, actor, a):
    """Organiser records the result of a manually run bidding round: which team bought the live player, and for how much."""
    cur, m = s["current"], s["managers"].get(a.get("mid"))
    if not cur:
        return False, "No player is up for auction right now."
    if s["paused"]:
        return False, "Auction is paused. Resume it first."
    if not m:
        return False, "Pick the team that bought the player."
    p = player_of(s, cur["pid"])
    if len(m["squad"]) >= s["settings"]["max_squad"]:
        return False, f"{m['team']} already has a full squad ({s['settings']['max_squad']} players)."
    amount = parse_amount(a.get("amount"))
    if amount is None:
        return False, "Enter the sold price as a whole number of lakhs."
    if amount < p["base"]:
        return False, f"The sold price cannot be below the base price ({money(p['base'])})."
    cap = max_bid(s, m)
    if amount > cap:
        return False, (f"{m['team']} can pay at most {money(max(cap, 0))} (purse {money(m['purse'])}, "
                       f"{money(reserve_after(s, m))} reserved for remaining squad slots).")
    before = copy.deepcopy(cur)                       # Undo sale brings the player back live with no price
    cur["bid"], cur["leader"], cur["call"] = amount, m["id"], 0
    cur["history"] = [{"t": now_iso(), "mid": m["id"], "amt": amount}]
    msg = _finish_sale(s)
    s["sales"][-1]["snapshot"] = before
    return True, msg


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
        if not a.get("force"):
            return False, "This player has a bid. Undo the bids first, or use Sold."
        cur["history"], cur["bid"], cur["leader"], cur["call"] = [], None, None, 0     # organiser drops the bids
        _log(s, f"Bids dropped on {player_of(s, cur['pid'])['name']}")
    return True, _finish_unsold(s)


def f_defer(s, actor, a):
    """Organiser sends the live player to the back of the queue; bids on this lot are dropped. He comes up again later."""
    cur = s["current"]
    if not cur:
        return False, "No player is up."
    p = player_of(s, cur["pid"])
    s["players"].remove(p)
    p["status"] = "pending"
    s["players"].append(p)
    s["last_result"] = {"kind": "unsold", "later": True, "player": p["name"], "origin": p["origin"], "role": p["role"],
                        "base": p["base"], "t": now_iso()}
    s["current"] = None
    _log(s, f"LATER {p['name']} sent to the back of the queue")
    return True, f"{p['name']} goes to the back of the queue and will come up later."


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
    """Unsold players go back into the queue at the END, so they come up after everyone still waiting."""
    pid = a.get("pid")
    items = [p for p in s["players"] if p["status"] == "unsold" and (not pid or p["id"] == pid)]
    if not items:
        return False, "No unsold players."
    ids = {p["id"] for p in items}
    for p in items:
        p["status"] = "pending"
    s["players"] = [p for p in s["players"] if p["id"] not in ids] + items
    return True, f"{len(items)} unsold player(s) back in the queue (at the end)."


def f_sort(s, actor, a):
    """Sort the waiting players (sold/unsold players keep their places)."""
    by = a.get("by")
    keys = {
        "role": lambda p: (not p.get("role"), str(p.get("role", "")).lower(), p["name"].lower()),
        "role_base": lambda p: (not p.get("role"), str(p.get("role", "")).lower(), -p["base"], p["name"].lower()),
        "base": lambda p: (-p["base"], p["name"].lower()),
        "name": lambda p: p["name"].lower(),
    }
    if by not in keys:
        return False, "Pick how to sort."
    idx = [i for i, p in enumerate(s["players"]) if p["status"] == "pending"]
    if len(idx) < 2:
        return False, "Fewer than two players are waiting."
    items = sorted((s["players"][i] for i in idx), key=keys[by])
    for i, p in zip(idx, items):
        s["players"][i] = p
    _log(s, f"Queue sorted: {SORT_LABELS[by]}")
    return True, f"Queue sorted: {SORT_LABELS[by].lower()}."


def f_auto_next(s, actor, a):
    flag = bool(a.get("flag"))
    s["auto_next"] = flag
    _log(s, "Next player: AUTOMATIC" if flag else "Next player: MANUAL")
    return True, ("Automatic mode: the next player in the queue comes up a few seconds after each result."
                  if flag else "Manual mode: you choose who comes up next.")


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


def parse_players_csv(text: str, default_base: int | None = None):
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
        if not name_h or (not base_h and default_base is None):
            return [], ["The first line must be a header containing: name, base_price (origin and role are optional)."]
        pick = lambda row, keys: clean_text(next((row[heads[k]] for k in keys if k in heads and row.get(heads[k])), ""), 60)
        rows, errs = [], []
        for n, row in enumerate(reader, 2):
            if None in row or any(v is None for v in row.values()):
                errs.append(f"Row {n}: wrong number of columns.")
                continue
            name = clean_text(row[name_h], 60)
            raw_base = (row[base_h] or "") if base_h else ""
            if default_base is not None and not raw_base.strip():
                base = default_base                                   # no price in the file: use the single base price
            else:
                mt = BASE_RE.match(raw_base)
                base = int(mt.group(1)) if mt else 0
            if not name or base < 1:
                errs.append(f"Row {n}: needs a name and a whole-number base_price in lakhs (e.g. 50).")
                continue
            rows.append({"name": name, "origin": pick(row, ("origin", "from", "city", "hometown", "location", "state")),
                         "role": pick(row, ("role", "category", "position")), "base": base})
            if len(rows) > MAX_PLAYERS:
                return [], [f"At most {MAX_PLAYERS} players."]
    except csv.Error as exc:
        return [], [f"Could not read the CSV ({exc})."]
    return rows, errs


def f_add_players(s, actor, a):
    replace = bool(a.get("replace"))
    if replace and (s["sales"] or s["current"]):
        return False, "Players can only be replaced before the first player is brought up or sold."
    rows, errs = parse_players_csv(str(a.get("text", "")), base_price_of(s))
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
    "defer": ("admin", f_defer), "set_role": ("admin", f_set_role), "set_base_all": ("admin", f_set_base_all), "sort": ("admin", f_sort), "auto_next": ("admin", f_auto_next),
    "admin_bid": ("admin", f_admin_bid), "admin_out": ("admin", f_admin_out), "set_base": ("admin", f_set_base),
    "bring": ("admin", f_bring), "call": ("admin", f_call), "sold": ("admin", f_sold), "sell": ("admin", f_sell), "unsold": ("admin", f_unsold),
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
/* Intellics Auction Room — Black & Gold design system */
#MainMenu,footer,header[data-testid="stHeader"],[data-testid="stToolbar"],[data-testid="stDecoration"]{display:none!important}
:root{--bg:#101010;--panel:#1B1B1B;--panel2:#252525;--line:#383838;--gold:#D4AF37;--gold2:#E5C76B;--gold-dark:#8C7025;--tx:#F5F5F5;--mu:#A8A8A8;--ok:#35D66F;--wn:#F5B942;--bad:#FF6868;--focus:#F3D982}
.stApp{background:radial-gradient(900px 460px at 50% -20%,rgba(212,175,55,.10),transparent 65%),var(--bg)!important;color:var(--tx);font-family:Inter,system-ui,-apple-system,"Segoe UI",Roboto,Helvetica,Arial,sans-serif!important}
.block-container{padding-top:.8rem!important;max-width:1600px;padding-bottom:2rem!important}
.stApp [data-testid="stMarkdownContainer"] p,.stApp [data-testid="stWidgetLabel"] p,.stApp label p,.stApp h1,.stApp h2,.stApp h3,.stApp h4{color:var(--tx)}
.stApp [data-testid="stCaptionContainer"]{color:var(--mu)}
.stApp input,.stApp textarea{background:#171717!important;color:var(--tx)!important;border-color:#454545!important;border-radius:8px!important}
.stApp [data-baseweb="select"]>div{background:#171717!important;border-color:#454545!important;color:var(--tx)!important}
.stApp .stButton>button,.stApp .stDownloadButton>button,.stApp [data-testid="stFormSubmitButton"]>button{background:#242424;color:var(--tx);border:1px solid #484848;border-radius:9px;font-weight:700;padding:.58rem 1rem;min-height:2.65rem;transition:background .15s ease,border-color .15s ease,transform .15s ease}
.stApp .stButton>button:hover,.stApp .stDownloadButton>button:hover{border-color:var(--gold);color:var(--gold2);background:#2b281f}
.stApp .stButton>button[kind="primary"],.stApp [data-testid="stFormSubmitButton"]>button[kind="primaryFormSubmit"]{background:linear-gradient(135deg,#E5C76B,#C49A28);color:#17130a;border:1px solid #E5C76B;box-shadow:0 3px 12px rgba(212,175,55,.12)}
.stApp .stButton>button[kind="primary"]:hover,.stApp [data-testid="stFormSubmitButton"]>button[kind="primaryFormSubmit"]:hover{background:#F0D987;color:#17130a;border-color:#F0D987}
.stApp .stButton>button:disabled{opacity:.38;cursor:not-allowed}
.stApp button:focus-visible,.stApp input:focus-visible{outline:2px solid var(--focus)!important;outline-offset:2px}
.stApp [data-testid="stExpander"]{border:1px solid var(--line);border-radius:12px;background:#171717}
.stApp [data-testid="stTabs"] button[role="tab"]{font-weight:700}
.stApp [data-testid="stTabs"] button[aria-selected="true"]{color:var(--gold2)!important}
.stApp [data-testid="stTabs"] [data-baseweb="tab-highlight"]{background:var(--gold)!important}
.au{color:var(--tx)}.au *{box-sizing:border-box}
.au-top{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;padding:14px 20px;border-radius:14px;background:linear-gradient(110deg,#191919,#242116);border:1px solid #4A4028;margin-bottom:14px;box-shadow:0 8px 26px rgba(0,0,0,.18)}
.au-brand{font-weight:850;font-size:clamp(1.1rem,1.8vw,1.7rem);letter-spacing:.035em;color:#fff}
.au-sub{font-size:clamp(.7rem,1vw,.88rem);color:var(--mu);letter-spacing:.15em;text-transform:uppercase;margin-top:3px}
.au-pill{display:inline-block;padding:6px 12px;border-radius:999px;font-size:.72rem;font-weight:800;letter-spacing:.12em;margin-left:7px;white-space:nowrap}
.au-live{background:rgba(53,214,111,.10);color:var(--ok);border:1px solid rgba(53,214,111,.45)}
.au-paused{background:rgba(245,185,66,.12);color:var(--wn);border:1px solid rgba(245,185,66,.48)}
.au-idle{background:rgba(212,175,55,.08);color:var(--gold2);border:1px solid rgba(212,175,55,.35)}
.au-conn{display:inline-block;font-size:.72rem;font-weight:700;letter-spacing:.035em;padding:6px 9px;border-radius:8px;margin-left:7px}
.au-c-ok{color:var(--ok);background:rgba(53,214,111,.08)}.au-c-warn{color:var(--wn);background:rgba(245,185,66,.10)}.au-c-bad{color:#fff;background:#8D2828}
.au-card{background:linear-gradient(145deg,#1E1E1E,#191919);border:1px solid #353535;border-radius:14px;padding:18px 20px;margin-bottom:14px;box-shadow:0 7px 22px rgba(0,0,0,.13)}
.au-hero{border-color:#695626;box-shadow:0 8px 28px rgba(0,0,0,.22);background:radial-gradient(850px 300px at 0% 0%,rgba(212,175,55,.10),transparent 70%),linear-gradient(145deg,#202020,#191919)}
.au-kicker{font-size:.76rem;font-weight:800;letter-spacing:.18em;color:var(--gold2);text-transform:uppercase}
.au-tag{display:inline-block;margin-top:10px;padding:5px 10px;border-radius:7px;background:rgba(212,175,55,.10);border:1px solid rgba(212,175,55,.42);color:var(--gold2);font-size:.78rem;font-weight:750;letter-spacing:.08em;text-transform:uppercase}
.au-pname{font-size:clamp(1.65rem,2.7vw,3rem);font-weight:850;line-height:1.12;margin-top:0;color:#fff;text-shadow:none;overflow-wrap:anywhere}
.au-meta{font-size:clamp(.95rem,1.35vw,1.3rem);color:#C0C0C0;margin-top:8px}
.au-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;margin-top:20px;padding-top:0;border-top:0}
.au-grid>div{background:#252525;border:1px solid #393939;border-radius:9px;padding:12px 13px;min-width:0}
.au-lbl{font-size:clamp(.65rem,.8vw,.8rem);letter-spacing:.1em;color:var(--mu);text-transform:uppercase;font-weight:750}
.au-val{font-size:clamp(1.1rem,1.7vw,1.8rem);font-weight:750;margin-top:6px;font-variant-numeric:tabular-nums;color:#fff;overflow-wrap:anywhere}
.au-bid{font-size:clamp(1.6rem,3vw,3.3rem);font-weight:850;line-height:1.08;margin-top:4px;color:var(--gold2);font-variant-numeric:tabular-nums;text-shadow:0 0 16px rgba(212,175,55,.14);animation-duration:.7s;animation-timing-function:ease-out}
.au-lead{font-size:clamp(1rem,1.6vw,1.6rem);font-weight:800;margin-top:6px;color:#fff;overflow-wrap:anywhere}
.au-small{font-size:clamp(.78rem,1vw,.95rem);color:var(--mu);margin-top:3px}.au-muted{color:#858585!important}
.au-call{margin-top:16px;padding:12px;text-align:center;font-weight:850;font-size:clamp(1rem,1.8vw,1.7rem);letter-spacing:.22em;border-radius:10px;background:rgba(212,175,55,.10);color:var(--gold2);border:1px solid rgba(212,175,55,.45)}
.au-compact .au-pname{font-size:clamp(1.55rem,2.3vw,2.4rem)}.au-compact .au-bid{font-size:clamp(1.5rem,2.5vw,2.6rem)}
.au-sec{font-size:.76rem;font-weight:850;letter-spacing:.16em;color:var(--gold2);text-transform:uppercase;margin:2px 0 12px}
.au-tbl{width:100%;border-collapse:collapse}
.au-tbl th{text-align:left;font-size:.68rem;letter-spacing:.12em;color:var(--mu);text-transform:uppercase;padding:7px 8px;border-bottom:1px solid #484033}
.au-tbl td{padding:9px 8px;border-bottom:1px solid #303030;font-size:clamp(.78rem,1vw,1rem);vertical-align:middle;font-variant-numeric:tabular-nums;color:#EAEAEA}
.au-tbl tbody tr:last-child td{border-bottom:0}.au-tbl tbody tr:hover td{background:rgba(212,175,55,.045)}
.au-tbl .r{text-align:right}.au-tbl tr.lead td{background:rgba(212,175,55,.10)}.au-tbl .tm{font-weight:800}.au-tbl .mg{font-size:.78rem;color:var(--mu)}
.au-bar{height:5px;border-radius:4px;background:#414141;margin-top:6px;overflow:hidden}.au-bar i{display:block;height:100%;background:linear-gradient(90deg,#9A7620,var(--gold2))}
.au-chip{display:inline-block;padding:4px 9px;border-radius:999px;font-size:.66rem;font-weight:850;letter-spacing:.08em}
.au-k-lead{background:var(--gold);color:#19150A}.au-k-in{background:rgba(53,214,111,.13);color:var(--ok)}.au-k-out{background:rgba(255,104,104,.13);color:var(--bad)}.au-k-full{background:#383838;color:#D0D0D0}
.au-sold{text-align:center;padding:38px 22px;border-color:#8C7025;background:radial-gradient(700px 260px at 50% 0%,rgba(212,175,55,.13),transparent 75%),#1B1B1B;animation:auglow 3s ease-in-out infinite alternate}
.au-stamp{font-size:clamp(1.1rem,2vw,2rem);font-weight:850;letter-spacing:.36em;color:var(--gold2)}
.au-big{font-size:clamp(2.1rem,4.5vw,4.8rem);font-weight:850;color:#fff;line-height:1.08;margin-top:12px;overflow-wrap:anywhere}
.au-price{font-size:clamp(1.8rem,3.6vw,3.5rem);font-weight:850;color:var(--gold2);margin-top:12px;text-shadow:none}
.au-stats{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:10px;margin-bottom:12px}
.au-stat{background:#1B1B1B;border:1px solid #383838;border-radius:11px;padding:12px 14px;min-width:0}.au-stat .au-val{font-size:clamp(1rem,1.4vw,1.4rem)}
.au-note{padding:11px 14px;border-radius:10px;font-weight:700;margin:8px 0}
.au-n-ok{background:rgba(53,214,111,.09);border:1px solid rgba(53,214,111,.4);color:var(--ok)}
.au-n-warn{background:rgba(245,185,66,.09);border:1px solid rgba(245,185,66,.4);color:var(--wn)}
.au-n-bad{background:rgba(255,104,104,.10);border:1px solid rgba(255,104,104,.4);color:var(--bad)}
.au-banner{padding:13px 16px;border-radius:10px;font-weight:800;margin-bottom:12px;text-align:center;letter-spacing:.025em}
.au-foot{display:flex;gap:24px;flex-wrap:wrap;justify-content:center;color:var(--mu);font-size:clamp(.8rem,1vw,1rem);margin-top:8px}.au-foot b{color:var(--gold2)}
.au-home{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:16px;margin-top:10px}
.au-home a{display:block;text-decoration:none;background:#1B1B1B;border:1px solid #383838;border-radius:14px;padding:24px;color:var(--tx)}
.au-home a:hover,.au-home a:focus-visible{border-color:var(--gold);box-shadow:0 0 0 1px rgba(212,175,55,.15);background:#211f18}
.au-home .h{font-size:1.2rem;font-weight:850;margin-bottom:6px;color:#fff}.au-home .d{color:var(--mu);line-height:1.45}
.au-dashboard-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.au-manager{background:#242424;border:1px solid #3A3A3A;border-radius:9px;padding:10px;min-width:0;position:relative;transition:border-color .2s,background .2s,opacity .2s}
.au-manager-icon{height:66px;border-radius:7px;background:#303030;display:flex;align-items:center;justify-content:center;font-size:27px;margin-bottom:8px}
.au-manager-team{font-size:.82rem;font-weight:850;overflow-wrap:anywhere;color:#F4F4F4;min-height:2.4em;line-height:1.2}
.au-manager-name{font-size:.7rem;color:#A8A8A8;margin-top:3px;overflow-wrap:anywhere}
.au-host-art{height:92px;border:1px solid #8C7025;border-radius:8px;background:linear-gradient(135deg,#2B271A,#514426);color:var(--gold2);display:flex;align-items:center;justify-content:center;font-size:34px}
.au-live-tag{float:right;background:var(--gold);color:#17130A;padding:3px 7px;border-radius:4px;font-size:.65rem;font-weight:850;margin-top:-25px;position:relative}
.au-current-bid{font-size:clamp(1.8rem,3vw,2.8rem);font-weight:850;text-align:center;color:var(--gold2);letter-spacing:-.035em;font-variant-numeric:tabular-nums}
.au-current-caption{text-align:center;font-weight:850;font-size:.75rem;letter-spacing:.13em;color:var(--mu);margin-bottom:12px}
.au-bid-sub{text-align:center;color:#BDBDBD;font-size:.75rem;margin:6px 0}.au-bid-sub b{color:var(--gold2)}
.au-history-item{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:9px 0;border-bottom:1px solid #383838;font-size:.75rem}
.au-history-item:last-child{border-bottom:0}.au-history-item>b{color:var(--gold2)}
.au-teamstats{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:9px}
.au-teamstat{background:#171717;border:1px solid #303030;padding:9px;border-radius:7px;min-width:0}
.au-teamstat-title{display:flex;justify-content:space-between;gap:4px;font-size:.68rem;margin-bottom:6px;color:#F0F0F0}
.au-teamstat-title span{color:var(--gold2);white-space:nowrap}
.au-teamstat-row{display:flex;justify-content:space-between;gap:4px;background:#292929;border-radius:4px;padding:5px 6px;margin:3px 0;font-size:.63rem;color:#D0D0D0}
.au-teamstat-row b{color:var(--gold2)}
.au-brandrow{display:flex;align-items:center;gap:13px}.au-logo{height:54px;width:54px;object-fit:contain;background:#fff;border-radius:10px;padding:3px;flex:none}
.au-herorow{display:flex;gap:18px;align-items:center}.au-herorow>div{min-width:0}
.au-photo{width:clamp(78px,8vw,132px);height:clamp(78px,8vw,132px);border-radius:12px;object-fit:cover;border:1px solid #6A572A;background:#2A2A2A;flex:none;display:block}
.au-timg{max-height:100%;max-width:100%;object-fit:contain;padding:3px}
.au-manager-lead{border-color:var(--gold);background:#302919;box-shadow:0 0 0 1px rgba(212,175,55,.18),0 0 18px rgba(212,175,55,.13);transform:translateY(-1px)}
.au-manager-lead .au-manager-team{color:var(--gold2)}.au-manager-lead .au-manager-icon{background:#3A321F}
/* Live auction electric-violet status LEDs */
.au-led{display:inline-block;width:5px;height:5px;border-radius:50%;flex:none;background:#fff;box-shadow:0 0 2px 1px #fff,0 0 6px 3px #b45cff,0 0 11px 4px rgba(158,65,255,.48);animation:none;opacity:1;vertical-align:middle;margin-right:7px}
.au-led-name{display:inline-flex;align-items:center;gap:0}
.au-manager-lead{border-color:#a85cff!important;background:linear-gradient(145deg,#21152f,#302919)!important;box-shadow:0 0 0 1px rgba(180,92,255,.2),0 0 18px rgba(160,65,255,.2)!important}
.au-manager-lead .au-manager-team{color:#d8b5ff!important}
.au-manager-lead .au-leadbadge{background:#a85cff;color:#fff}
@keyframes au-led-pulse{0%,100%{opacity:.72;filter:brightness(.9);box-shadow:0 0 2px 1px #fff,0 0 6px 3px #a84dff,0 0 12px 4px rgba(158,65,255,.35)}50%{opacity:1;filter:brightness(1.35);box-shadow:0 0 3px 2px #fff,0 0 10px 5px #b45cff,0 0 20px 7px rgba(158,65,255,.7)}}
.au-proj-nav{display:flex;gap:8px;flex-wrap:wrap;margin:4px 0 14px}
.au-proj-note{color:#b9a0d9;font-size:.72rem;letter-spacing:.08em;font-weight:800}
/* Responsive projector layout: full-width manager grid, consistent rounded cards, stable text */
.au-dashboard-grid{display:grid!important;grid-template-columns:repeat(8,minmax(0,1fr))!important;gap:8px!important}
.au-manager{min-width:0!important;border-radius:12px!important;padding:9px!important;position:relative;overflow:hidden}
.au-manager-icon{height:clamp(42px,5.2vw,64px)!important;border-radius:9px!important;overflow:hidden}
.au-manager-team{font-size:clamp(.62rem,.82vw,.82rem)!important;line-height:1.18!important;min-height:2.35em!important;overflow-wrap:normal!important;word-break:normal!important;hyphens:auto}
.au-manager-name{font-size:clamp(.58rem,.72vw,.72rem)!important;line-height:1.2!important;overflow-wrap:anywhere}
.au-card{border-radius:14px!important;min-width:0!important}
.au-led-name{display:inline-flex;align-items:center;gap:5px;min-width:0}
.au-lead{overflow-wrap:normal!important;word-break:normal!important;line-height:1.2!important}
.au-manager-lead{border-color:#a85cff!important;background:linear-gradient(145deg,#21152f,#302919)!important;box-shadow:0 0 0 1px rgba(180,92,255,.22),0 0 14px rgba(160,65,255,.16)!important}
@media(max-width:1150px){.au-dashboard-grid{grid-template-columns:repeat(4,minmax(0,1fr))!important}.au-manager-icon{height:42px!important}}
@media(max-width:760px){.au-dashboard-grid{grid-template-columns:repeat(2,minmax(0,1fr))!important}}
@media(prefers-reduced-motion:reduce){.au-led{animation:none!important}}


.au-leadbadge{position:absolute;top:5px;right:5px;z-index:2;background:var(--gold);color:#17130A;font-size:.53rem;font-weight:900;letter-spacing:.08em;padding:3px 5px;border-radius:4px}
.au-manager-out{opacity:.48;filter:grayscale(.55)}
.au-tbl tr.lead td{background:rgba(212,175,55,.10)}.au-tbl tr.lead td:first-child{box-shadow:inset 3px 0 0 var(--gold)}
.au-hero .au-lead{color:var(--gold2)}
@keyframes bump0{0%{transform:scale(1)}40%{transform:scale(1.045)}100%{transform:scale(1)}}
@keyframes bump1{0%{transform:scale(1)}40%{transform:scale(1.045)}100%{transform:scale(1)}}
@keyframes auglow{from{box-shadow:0 0 8px rgba(212,175,55,.08)}to{box-shadow:0 0 26px rgba(212,175,55,.20)}}
@media(max-width:1050px){.au-teamstats{grid-template-columns:1fr}.au-pname{font-size:1.7rem}.au-top{padding:12px 14px}.au-card{padding:15px}}
@media(max-width:900px){.au-grid{grid-template-columns:1fr 1fr}.au-stats{grid-template-columns:1fr 1fr}.au-home{grid-template-columns:1fr}.au-foot{gap:12px}}
@media(max-width:760px){.au-dashboard-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.au-grid{grid-template-columns:1fr}.au-teamstats{grid-template-columns:repeat(2,minmax(0,1fr))}.au-herorow{gap:12px}.au-pill,.au-conn{margin:4px 4px 0 0}.au-tbl td{padding:7px 5px;font-size:.78rem}}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}
.au-photo-xl{width:clamp(150px,19vw,320px)!important;height:clamp(150px,19vw,320px)!important;border-radius:18px!important;border-width:2px!important}
.au-xl .au-herorow{gap:26px}.au-xl .au-pname{font-size:clamp(1.8rem,3.2vw,3.4rem)!important}
.au-manager-purse{font-size:clamp(.72rem,.98vw,1rem);font-weight:850;color:var(--gold2);margin-top:3px}
/* Projector stage: portrait photo + details, sized to the screen height so everything is visible at once */
.au-stage{display:grid!important;grid-template-columns:auto minmax(0,1fr);gap:clamp(18px,2.6vw,44px);align-items:center;padding:clamp(14px,1.6vw,26px)!important}
.au-stage-photo{height:clamp(220px,46vh,580px);aspect-ratio:4/5;width:auto;max-width:42vw;border-radius:18px;object-fit:cover;object-position:top center;border:2px solid #6A572A;background:#2A2A2A;display:block;box-shadow:0 10px 40px rgba(0,0,0,.45)}
.au-sp-none{display:flex;align-items:center;justify-content:center;font-size:clamp(4rem,10vw,9rem);color:#555;height:clamp(220px,46vh,580px)}
.au-stage-info{min-width:0}
.au-stage-name{font-size:clamp(2rem,4.4vw,4.8rem);font-weight:850;line-height:1.06;color:#fff;margin-top:8px;overflow-wrap:break-word}
.au-stage-meta{font-size:clamp(1rem,1.8vw,1.9rem);color:#C8C8C8;margin-top:10px}
.au-stage-box{margin-top:clamp(14px,2.4vh,30px);display:inline-block;min-width:min(100%,300px);padding:12px 18px;border-radius:12px;background:#252525;border:1px solid #4A4028}
.au-stage-base{font-size:clamp(1.7rem,3.4vw,3.6rem);font-weight:850;color:var(--gold2);font-variant-numeric:tabular-nums;line-height:1.1;margin-top:4px}
.au-stage-wait{margin-top:clamp(12px,2vh,22px);font-size:clamp(.8rem,1.1vw,1.1rem);font-weight:800;letter-spacing:.22em;text-transform:uppercase;color:#b9a0d9}
.au-stage-team{display:flex;align-items:center;gap:16px;margin-top:clamp(12px,2vh,24px)}
.au-sold.au-stage{text-align:left;padding:clamp(14px,1.6vw,26px)!important}
.au-sold .au-stamp{font-size:clamp(1.4rem,2.6vw,2.8rem)}
.au-sold .au-price{margin-top:4px;font-size:clamp(2.2rem,4.8vw,5rem)}
.au-stage-compact,.au-sold.au-stage-compact{gap:16px!important;padding:14px!important}
.au-stage-compact .au-stage-photo,.au-stage-compact .au-sp-none{height:190px}
.au-stage-compact .au-stage-name{font-size:clamp(1.4rem,2.2vw,2.2rem)}
.au-stage-compact .au-stage-meta{font-size:1rem;margin-top:4px}
.au-stage-compact .au-stage-base,.au-stage-compact .au-sold .au-price{font-size:1.6rem}
.au-stage-compact .au-stage-box{margin-top:10px;padding:8px 14px}
.au-stage-compact .au-stage-wait{display:none}
.au-stage-compact .au-stamp{font-size:1.2rem}
.au-stage-compact .au-price{font-size:1.8rem!important}
@media(max-width:700px){.au-stage{grid-template-columns:1fr}.au-stage-photo{max-width:100%;margin:0 auto}}
/* Team squad stats: team name + players bought out of the maximum */
.au-sqgrid{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:clamp(10px,1.2vw,18px)}
.au-sq{background:#171717;border:1px solid #303030;border-radius:14px;padding:clamp(12px,1.4vw,22px);min-width:0}
.au-sq-full{border-color:var(--gold-dark);background:#1f1b10}
.au-sq-head{display:flex;align-items:center;gap:10px}
.au-sq-name{font-size:clamp(.9rem,1.5vw,1.5rem);font-weight:850;color:#F4F4F4;line-height:1.2;overflow-wrap:break-word;min-width:0}
.au-sq-count{margin-top:clamp(8px,1.6vh,18px);line-height:1}
.au-sq-count b{font-size:clamp(2.2rem,4.4vw,4.6rem);font-weight:850;color:var(--gold2);font-variant-numeric:tabular-nums}
.au-sq-count span{font-size:clamp(1.1rem,2vw,2rem);font-weight:750;color:var(--mu);margin-left:6px}
.au-sq-lbl{font-size:clamp(.65rem,.85vw,.85rem);letter-spacing:.14em;text-transform:uppercase;color:var(--mu);font-weight:750;margin:4px 0 8px}
@media(max-width:1000px){.au-sqgrid{grid-template-columns:repeat(2,minmax(0,1fr))}}
/* Tighter team strip under the player so the whole projector page fits */
.au-dashboard-grid{gap:6px!important}
.au-manager{padding:7px!important}
.au-manager-icon{height:clamp(34px,4.2vw,54px)!important;margin-bottom:5px!important}
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


def photo_html(name: str, compact: bool = False) -> str:
    """Portrait of a player (4:5 frame). A neutral placeholder keeps the layout stable when no photo exists."""
    cls = "au-stage-photo" + (" au-sp-compact" if compact else "")
    img = static_img("players", name)
    if img:
        return f'<img class="{cls}" src="{e(img)}" alt="{e(name)}">'
    return f'<div class="{cls} au-sp-none">👤</div>'


def hero_html(s: dict, compact: bool = False, xl: bool = False) -> str:
    """The player currently on the block: portrait on the left, all details on the right. Shows no bid information:
    bidding is run in the room and the projector only reveals the final team and price once the player is sold."""
    cur = s["current"]
    p = player_of(s, cur["pid"])
    lot = [x["id"] for x in s["players"]].index(p["id"]) + 1
    tag = f'<div class="au-tag">{e(p["role"])}</div>' if p["role"] else ""
    origin = f'<div class="au-stage-meta">From {e(p["origin"])}</div>' if p["origin"] else ""
    return (f'<div class="au au-card au-hero au-stage{" au-stage-compact" if compact else ""}">{photo_html(p["name"], compact)}'
            f'<div class="au-stage-info"><div class="au-kicker">Now on the block · Lot {lot} of {len(s["players"])}</div>{tag}'
            f'<div class="au-stage-name">{e(p["name"])}</div>{origin}'
            f'<div class="au-stage-box"><div class="au-lbl">Base price</div><div class="au-stage-base">{money(p["base"])}</div></div>'
            f'<div class="au-stage-wait">Bidding in progress</div></div></div>')


def history_html(s: dict, n: int = 6) -> str:
    cur = s["current"]
    if not cur or not cur["history"]:
        return ""
    rows = "".join(f'<tr><td>{clock(h["t"])}</td><td class="tm">{e(s["managers"][h["mid"]]["team"])}</td>'
                   f'<td class="r">{money(h["amt"])}</td></tr>' for h in reversed(cur["history"][-n:]))
    return (f'<div class="au au-card"><div class="au-sec">Bid history</div><table class="au-tbl"><thead><tr><th>Time</th>'
            f'<th>Team</th><th class="r">Bid</th></tr></thead><tbody>{rows}</tbody></table></div>')


def idle_html(s: dict, compact: bool = False) -> str:
    lr = s["last_result"]
    if lr and lr["kind"] == "sold":
        crest = static_img("teams", lr["team"])
        crest_html = f'<img class="au-timg" style="width:clamp(44px,5vw,76px);height:clamp(44px,5vw,76px);padding:0" src="{e(crest)}" alt="">' if crest else ""
        mt = f'{e(lr["role"])}{" · " if lr["role"] and lr["origin"] else ""}{e(lr["origin"])}'
        return (f'<div class="au au-card au-sold au-stage{" au-stage-compact" if compact else ""}">{photo_html(lr["player"], compact)}'
                f'<div class="au-stage-info"><div class="au-stamp">SOLD</div><div class="au-stage-name">{e(lr["player"])}</div>'
                f'<div class="au-stage-meta">{mt}</div>'
                f'<div class="au-stage-box"><div class="au-lbl">Sold for</div><div class="au-price">{money(lr["price"])}</div></div>'
                f'<div class="au-stage-team">{crest_html}<div><div class="au-lbl">Sold to</div>'
                f'<div class="au-lead" style="margin-top:2px">{e(lr["team"])}</div></div></div></div></div>')
    if lr:
        later = bool(lr.get("later"))
        return (f'<div class="au au-card" style="text-align:center;padding:44px"><div class="au-stamp" style="color:var(--mu)">{"COMES BACK LATER" if later else "UNSOLD"}</div>'
                f'<div class="au-big" style="color:var(--mu)">{e(lr["player"])}</div>'
                f'<div class="au-meta">Base price {money(lr["base"])} · {"back of the queue" if later else "no takers"}</div></div>')
    started = any(p["status"] != "pending" for p in s["players"])
    msg = "Next lot coming up" if started else "The auction will begin shortly"
    return (f'<div class="au au-card" style="text-align:center;padding:56px"><div class="au-stamp">{msg.upper()}</div>'
            f'<div class="au-meta" style="margin-top:14px">{len(s["managers"])} managers · {len(s["players"])} players</div></div>')


def board_html(s: dict) -> str:
    cfg, rows = s["settings"], ""
    for m in s["managers"].values():
        full = len(m["squad"]) >= cfg["max_squad"]
        chip = '<span class="au-chip au-k-full">FULL</span>' if full else ""
        pct = max(0, min(100, m["purse"] / max(1, cfg["purse"]) * 100))
        rows += (f'<tr><td><div class="tm">{e(m["team"])}</div><div class="mg">{e(m["name"])}</div></td>'
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
    """Compact team cards (crest, team, purse left). After a sale the buying team's card glows."""
    icons = ["👨🏻‍💼", "👩🏻‍💼", "🧑🏻‍💼", "👨🏽‍💻", "👩🏽‍💼", "🧑🏾‍💼", "👨🏻‍💻", "👩🏻‍💻"]
    lr = s.get("last_result")
    buyer = lr["team"] if (lr and lr.get("kind") == "sold" and not s.get("current")) else None
    cards = ""
    for i, m in enumerate(s["managers"].values()):
        logo = static_img("teams", m["team"])
        icon = f'<img class="au-timg" src="{e(logo)}" alt="">' if logo else icons[i % len(icons)]
        won = buyer is not None and m["team"] == buyer
        badge = '<div class="au-leadbadge">BOUGHT</div>' if won else ""
        cards += (f'<div class="au-manager{" au-manager-lead" if won else ""}">{badge}<div class="au-manager-icon">{icon}</div>'
                  f'<div class="au-manager-team">{e(m["team"])}</div>'
                  f'<div class="au-manager-purse">{money(m["purse"])} left</div>'
                  f'<div class="au-manager-name">{len(m["squad"])}/{s["settings"]["max_squad"]} players</div></div>')
    return (f'<div class="au au-card"><div class="au-sec">Teams · purse left</div>'
            f'<div class="au-dashboard-grid">{cards}</div></div>')


def screen_team_stats_html(s: dict) -> str:
    """Squad size per team (players bought out of the maximum). No positions."""
    mx, cards = s["settings"]["max_squad"], ""
    for m in s["managers"].values():
        n = len(m["squad"])
        logo = static_img("teams", m["team"])
        crest = f'<img class="au-timg" style="width:clamp(34px,3.6vw,56px);height:clamp(34px,3.6vw,56px);padding:0;flex:none" src="{e(logo)}" alt="">' if logo else ""
        pct = max(0, min(100, n / max(1, mx) * 100))
        cards += (f'<div class="au-sq{" au-sq-full" if n >= mx else ""}"><div class="au-sq-head">{crest}<div class="au-sq-name">{e(m["team"])}</div></div>'
                  f'<div class="au-sq-count"><b>{n}</b><span>/ {mx}</span></div><div class="au-sq-lbl">players</div>'
                  f'<div class="au-bar"><i style="width:{pct:.0f}%"></i></div></div>')
    return f'<div class="au au-card"><div class="au-sec">Team squad stats · max {mx} players per team</div><div class="au-sqgrid">{cards}</div></div>'


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
    """Read-only projector. Bidding happens in the room: the screen shows the player on the block, then the final team and price."""
    S = get_store(current_event())
    sn = S.read()
    if sn.view is None:
        html_block(banner_html(sn))
        unavailable(sn)
        return
    s = sn.view
    topbar(s, sn)
    pages = ["Live Auction", "Team Squad Stats"]
    page_key = f"au_projector_page_{current_event()}"
    if st.session_state.get(page_key) not in pages:
        st.session_state[page_key] = pages[0]
    st.radio("Projector page", pages, horizontal=True, key=page_key, label_visibility="collapsed")
    if st.session_state[page_key] == "Live Auction":
        html_block(hero_html(s) if s["current"] else idle_html(s))
        html_block(screen_managers_html(s))
    else:
        html_block(screen_team_stats_html(s))
    html_block(footer_html(s))


def view_screen() -> None:
    screen_live(get_store(current_event()))


@st.fragment(run_every=POLL_BID)
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


def admin_sell_panel(s: dict, cur: dict, off: bool, go) -> None:
    """The bidding itself is run in the room. The organiser only records the final team and price after the player is sold."""
    cfg, pid = s["settings"], cur["pid"]
    p = player_of(s, pid)
    st.markdown("**Record the sale**")
    if s["paused"]:
        st.caption("The auction is paused. Resume it to record a sale.")
        return
    eligible = {m["id"]: m for m in s["managers"].values()
                if len(m["squad"]) < cfg["max_squad"] and max_bid(s, m) >= p["base"]}
    if not eligible:
        st.caption("No team has a free squad spot and enough purse for this player. Mark him unsold below.")
        return
    st.caption("Run the bidding in the room. When it ends, pick the winning team and the final price, then press SOLD. "
               "The projector shows the result only at that moment.")
    with st.form(f"adm_sell_{pid}"):
        c = st.columns([3, 2, 1], vertical_alignment="bottom")
        who = c[0].selectbox("Sold to team", list(eligible), index=None, placeholder="Select the team",
                             format_func=lambda k: f'{eligible[k]["team"]} · {len(eligible[k]["squad"])}/{cfg["max_squad"]} players · max {money(max_bid(s, eligible[k]))}')
        amt = c[1].number_input("Sold price (lakhs)", min_value=p["base"], value=p["base"], step=cfg["step"], format="%d")
        if c[2].form_submit_button("SOLD", type="primary", use_container_width=True, disabled=off):
            go("sell", {"mid": who, "amount": int(amt)}, None)


def _toggle_auto() -> None:
    """Callback for the automatic/manual switch: save it, and snap the switch back if the save failed."""
    ss = st.session_state
    res = do(get_store(current_event()), admin_actor(True), "auto_next", {"flag": bool(ss.get("adm_auto"))})
    if not res.ok:
        ss["adm_auto"] = not ss.get("adm_auto")


def _set_role() -> None:
    """Callback for the role selector: only players of that role come up for bidding."""
    pick = st.session_state.get("adm_role_sel")
    do(get_store(current_event()), admin_actor(True), "set_role", {"role": None if pick in (None, "All roles") else pick})


def queue_html(pend: list, n: int = 40) -> str:
    rows = "".join(f'<tr><td class="au-muted">{i}</td><td class="tm">{e(p["name"])}</td><td>{e(p.get("role", ""))}</td>'
                   f'<td class="r">{money(p["base"])}</td></tr>' for i, p in enumerate(pend[:n], 1))
    more = f'<div class="au-small">...and {len(pend) - n} more</div>' if len(pend) > n else ""
    return (f'<div class="au au-card"><table class="au-tbl"><thead><tr><th>#</th><th>Player</th><th>Role</th>'
            f'<th class="r">Base</th></tr></thead><tbody>{rows}</tbody></table>{more}</div>')


def admin_next_picker(s: dict, off: bool, go, pend: list, unsold: list) -> None:
    """Choose the next player by hand from the players of the active role (waiting ones first, then unsold)."""
    rf = s.get("role_filter")
    label = lambda p: f'{p["name"]} · {p.get("role", "")} · {money(p["base"])}'
    opts = {"": f"Next {rf} in queue" if rf else "Next in queue",
            **{p["id"]: label(p) for p in pend}, **{p["id"]: label(p) + " (unsold)" for p in unsold}}
    pick = st.selectbox("Bring up", list(opts), format_func=lambda k: opts[k], key=f"adm_pick_{rf or 'all'}")
    if st.button("Bring up player", type="primary", use_container_width=True, disabled=off or not (pend or unsold)):
        go("bring", {"pid": pick or None})


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
    auto, rf = bool(s.get("auto_next")), s.get("role_filter")
    roles = sorted({p["role"] for p in s["players"] if p.get("role") and p["status"] != "sold"} | ({rf} if rf else set()), key=str.lower)
    st.session_state["adm_auto"] = auto                       # the saved settings are the truth; the widgets just mirror them
    st.session_state["adm_role_sel"] = rf or "All roles"
    c = st.columns([2, 3], vertical_alignment="bottom")
    c[0].selectbox("Players coming up for bidding", ["All roles", *roles], key="adm_role_sel", on_change=_set_role, disabled=off)
    c[1].toggle(f"Automatic next player ({AUTO_NEXT_SECONDS}s after each result)", key="adm_auto", on_change=_toggle_auto, disabled=off)
    if cur:
        html_block(hero_html(s, compact=True))
        admin_sell_panel(s, cur, off, go)
        c = st.columns(3)
        if c[0].button("Mark unsold", use_container_width=True, disabled=off):
            go("unsold", None, rev)
        if c[1].button("Come back later (back of queue)", use_container_width=True, disabled=off):
            go("defer", None, rev)
        if c[2].button("Resume auction" if s["paused"] else "Pause auction", use_container_width=True, disabled=off):
            go("pause", {"flag": not s["paused"]})
    else:
        html_block(idle_html(s, compact=True))
        inrole = lambda p: not rf or p.get("role") == rf
        pend_all = [p for p in s["players"] if p["status"] == "pending"]
        pend = [p for p in pend_all if inrole(p)]
        unsold_all = [p for p in s["players"] if p["status"] == "unsold"]
        unsold = [p for p in unsold_all if inrole(p)]
        lr = s["last_result"]
        who = f"{rf} " if rf else ""
        if auto:
            if not pend:
                st.caption(f"Automatic mode: no {who}players are waiting. Pick another role, re-queue unsold players or add more.")
            elif s["paused"]:
                st.caption("Automatic mode is waiting because bidding is paused.")
            elif lr and not off:
                try:
                    age = (datetime.now(timezone.utc) - datetime.fromisoformat(lr["t"])).total_seconds()
                except (KeyError, ValueError):
                    age = AUTO_NEXT_SECONDS
                if age >= AUTO_NEXT_SECONDS:
                    go("bring", {"pid": None}, rev)
                st.caption(f"Next up automatically: {pend[0]['name']}. Coming up in a moment...")
            else:
                st.caption(f"Next in queue: {pend[0]['name']}. Press the button below to start; after that it runs by itself.")
            if st.button("Bring up next player now", type="primary", use_container_width=True, disabled=off or not pend):
                go("bring", {"pid": None})
            with st.expander("Choose a specific player instead"):
                admin_next_picker(s, off, go, pend, unsold)
        else:
            admin_next_picker(s, off, go, pend, unsold)
        c = st.columns(3)
        if c[0].button("Shuffle queue", use_container_width=True, disabled=off or len(pend_all) < 2):
            go("shuffle")
        if c[1].button(f"Re-queue unsold ({len(unsold_all)})", use_container_width=True, disabled=off or not unsold_all):
            go("requeue")
        if c[2].button("Resume bidding" if s["paused"] else "Pause bidding", use_container_width=True, disabled=off):
            go("pause", {"flag": not s["paused"]})
        with st.expander(f"Queue order ({len(pend)} {who}waiting)"):
            html_block(queue_html(pend)) if pend else st.caption("Nobody is waiting.")
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
            f"{note} Restoring replaces ALL current auction data.")
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


def event_switcher(S: Store, sn: Snap) -> None:
    labels, cur_ev = event_labels(), current_event()
    ids = list(labels)
    busy = bool(sn.view and sn.view["current"])
    c = st.columns([2, 1, 2], vertical_alignment="bottom")
    pick = c[0].selectbox("Active event (the projector screen follows this)", ids,
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
        st.markdown("#### One base price for every player")
        with st.form("au_base"):
            c = st.columns([3, 1], vertical_alignment="bottom")
            nb = c[0].number_input("Base price (lakhs, 100 lakh = 1 Cr)", min_value=1, max_value=1_000_000, value=int(base_price_of(s)),
                                   step=cfg["step"], format="%d", disabled=bool(s["current"]))
            if c[1].form_submit_button("Apply to all players", type="primary", use_container_width=True, disabled=bool(s["current"])):
                do(S, admin_actor(True), "set_base_all", {"base": int(nb)})
                st.rerun()
        st.caption("Applies to every player who is waiting or unsold. Players you add later use this price unless their CSV row has its own base_price.")
        st.markdown("#### Managers (teams)")
        if s["managers"]:
            html_block('<div class="au au-card"><table class="au-tbl"><thead><tr><th>Team</th><th>Manager</th><th class="r">Purse</th></tr></thead><tbody>'
                       + "".join(f'<tr><td class="tm">{e(m["team"])}</td><td>{e(m["name"])}</td><td class="r">{money(m["purse"])}</td></tr>'
                                 for m in s["managers"].values()) + "</tbody></table></div>")
        with st.form("au_mgr"):
            txt = st.text_area("One team per line:  Team, Manager",
                               height=120, placeholder="Apex Capital, Ravi Kumar\nNova Group, Asha Rao")
            up = st.file_uploader("...or upload a text/CSV file", type=["csv", "txt"], key="au_mfile")
            rep = st.checkbox("Replace all existing managers", disabled=locked)
            if st.form_submit_button("Save managers", type="primary"):
                data = up.getvalue().decode("utf-8-sig", errors="replace") if up and up.size <= MAX_UPLOAD_BYTES else txt
                data, _ = prefill_pins(data)            # PINs are no longer used, but the data model still stores one
                do(S, admin_actor(True), "add_managers", {"text": data, "replace": rep})
                st.rerun()
        st.markdown("#### Players")
        st.caption(f"{len(s['players'])} players loaded, {sum(p['status'] == 'pending' for p in s['players'])} waiting. "
                   "CSV columns: name, origin, role (base_price is optional: without it the single base price above is used).")
        up = st.file_uploader("Upload CSV", type=["csv", "txt"], key="au_csv")
        txt = st.text_area("...or paste rows (with the header line)", height=110, placeholder="name,origin,role\nAarav Sharma,Delhi,Batter")
        rep = st.checkbox("Replace all existing players", disabled=locked, key="au_prep")
        c = st.columns(3)
        if c[0].button("Add players", type="primary", use_container_width=True):
            data = up.getvalue().decode("utf-8-sig", errors="replace") if up and up.size <= MAX_UPLOAD_BYTES else txt
            do(S, admin_actor(True), "add_players", {"text": data, "replace": rep})
            st.rerun()
        c[1].download_button("CSV template", "name,origin,role\nAarav Sharma,Delhi,Batter\n", "players_template.csv", use_container_width=True)
        if c[2].button("Load demo data", use_container_width=True, disabled=locked):
            demo = "\n".join(f"{t}, Manager {i}, {100000 + secrets.randbelow(899999)}" for i, t in enumerate(
                ["Apex Capital", "Meridian Ventures", "Northwind Holdings", "Sterling Partners", "Vertex Group", "Zenith Equity"], 1))
            do(S, admin_actor(True), "demo", {"manager_text": demo})
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
        st.caption("Backups contain all auction data except team PINs, which are no longer used.")
        restore_ui(S, sn.rev)
        with st.expander("Activity log"):
            for entry in reversed(s["log"][-60:]):
                st.text(f'{clock(entry["t"])}  {entry["text"]}')


def main() -> None:
    st.set_page_config(page_title="Auction Room", page_icon="🔨", layout="wide", initial_sidebar_state="collapsed")
    st.markdown(CSS, unsafe_allow_html=True)
    view = str(st.query_params.get("view", "") or "").lower()
    {"screen": view_screen, "admin": view_admin}.get(view, view_home)()


if __name__ == "__main__":
    main()
