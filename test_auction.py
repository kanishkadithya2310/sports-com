"""Offline tests for the auction rules, security and persistence logic. No database, no Streamlit needed.

Run from this folder:   python -m unittest -v test_auction
(If pytest is installed:  pytest -q)
"""
import copy
import hashlib
import json
import threading
import unittest

import auction_app as A
from auction_app import BackendError, MemoryBackend, Result, run_action

A.COMMIT_BACKOFF = 0
ADMIN = {"role": "admin"}


class Flaky(MemoryBackend):
    """MemoryBackend with injectable faults."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.down = False
        self.fail_before = 0       # commits that fail before reaching the database (unknown outcome)
        self.fail_after = 0        # commits that DO land but whose reply is lost
        self.definitive = False
        self.before_commit = None
        self.init_calls = 0

    def get_state(self):
        if self.down:
            raise BackendError("down", unknown=True)
        return super().get_state()

    def get_rev(self):
        if self.down:
            raise BackendError("down", unknown=True)
        return super().get_rev()

    def init_state(self, state):
        self.init_calls += 1
        return super().init_state(state)

    def commit(self, *a):
        if self.before_commit:
            hook, self.before_commit = self.before_commit, None
            hook()
        if self.definitive:
            raise BackendError("refused", unknown=False)
        if self.fail_before > 0:
            self.fail_before -= 1
            raise BackendError("timeout", unknown=True)
        out = super().commit(*a)
        if self.fail_after > 0:
            self.fail_after -= 1
            raise BackendError("lost reply", unknown=True)
        return out


def env(n=3, purse=10000, squad=8, step=25, reserve=20, players=((("A", 100),) * 1), backend=None):
    be = backend or MemoryBackend()
    txt = "\n".join(f"Team{i}, Mgr{i}, {1000 + i}" for i in range(1, n + 1))
    assert run_action(be, "add_managers", ADMIN, {"text": txt, "replace": True}).ok
    r = run_action(be, "settings", ADMIN, {"settings": {"title": "T", "subtitle": "", "purse": purse, "max_squad": squad,
                                                        "step": step, "reserve": reserve}})
    assert r.ok, r.message
    csvt = "name,origin,role,base_price\n" + "\n".join(f"{nm},X,Bat,{b}" for nm, b in players)
    assert run_action(be, "add_players", ADMIN, {"text": csvt, "replace": True}).ok
    return be


def mgr(be, i):
    mid = f"m{i}"
    return {"role": "manager", "id": mid, "ver": be.state["managers"][mid]["session_ver"]}


def bid(be, i, amt, **k):
    return run_action(be, "bid", mgr(be, i), {"amount": amt}, **k)


def up(be, pid=None):
    r = run_action(be, "bring", ADMIN, {"pid": pid})
    assert r.ok, r.message
    return r


def st_(be):
    return be.get_state()[0]


class Rules(unittest.TestCase):
    def test_first_bid_at_base_and_below_base(self):
        be = env(players=[("A", 100)])
        up(be)
        self.assertFalse(bid(be, 1, 90).ok)
        self.assertTrue(bid(be, 1, 100).ok)
        self.assertEqual(st_(be)["current"]["bid"], 100)

    def test_minimum_raise(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        r = bid(be, 2, 110)
        self.assertFalse(r.ok)
        self.assertIn("minimum", r.message)
        self.assertTrue(bid(be, 2, 125).ok)

    def test_leader_cannot_rebid(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        self.assertIn("already hold", bid(be, 1, 200).message)

    def test_insufficient_purse(self):
        be = env(n=2, purse=200, squad=1, reserve=0, players=[("A", 150)])
        up(be)
        r = bid(be, 1, 250)
        self.assertFalse(r.ok)
        self.assertEqual(st_(be)["managers"]["m1"]["purse"], 200)

    def test_squad_reserve(self):
        be = env(purse=300, squad=3, reserve=50, players=[("A", 100)])
        up(be)
        self.assertFalse(bid(be, 1, 250).ok)        # cap = 300 - 2*50 = 200
        self.assertTrue(bid(be, 1, 200).ok)

    def test_full_squad_cannot_bid(self):
        be = env(n=2, squad=1, players=[("A", 100), ("B", 100)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "withdraw", mgr(be, 2))       # auto-sold to m1
        up(be)
        r = bid(be, 1, 100)
        self.assertIn("squad is full", r.message)

    def test_withdraw_and_reentry(self):
        be = env(players=[("A", 100)])
        up(be)
        self.assertTrue(run_action(be, "withdraw", mgr(be, 1)).ok)
        self.assertIn("withdrawn", bid(be, 1, 100).message)
        run_action(be, "clear_out", ADMIN)
        self.assertTrue(bid(be, 1, 100).ok)

    def test_leader_cannot_withdraw(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        self.assertFalse(run_action(be, "withdraw", mgr(be, 1)).ok)

    def test_auto_sale_when_others_withdraw(self):
        be = env(n=2, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        r = run_action(be, "withdraw", mgr(be, 2))
        s = st_(be)
        self.assertIn("sold", r.message)
        self.assertIsNone(s["current"])
        self.assertEqual(s["managers"]["m1"]["purse"], 9900)
        self.assertEqual(s["players"][0]["status"], "sold")

    def test_auto_sale_when_challenger_cannot_afford(self):
        be = env(n=2, purse=200, squad=1, reserve=0, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        bid(be, 2, 175)
        r = bid(be, 1, 200)                           # m2's cap is 200 < 225 -> nobody can top it
        self.assertIn("sold", r.message)
        self.assertEqual(st_(be)["managers"]["m1"]["purse"], 0)

    def test_auto_unsold_when_nobody_bids(self):
        be = env(n=2, players=[("A", 100)])
        up(be)
        run_action(be, "withdraw", mgr(be, 1))
        self.assertIsNotNone(st_(be)["current"])
        r = run_action(be, "withdraw", mgr(be, 2))
        self.assertIn("unsold", r.message)
        self.assertEqual(st_(be)["players"][0]["status"], "unsold")

    def test_going_once_twice_sold(self):
        be = env(players=[("A", 100)])
        up(be)
        self.assertFalse(run_action(be, "call", ADMIN, {"n": 1}).ok)   # no bid yet
        bid(be, 1, 100)
        run_action(be, "call", ADMIN, {"n": 1})
        self.assertEqual(st_(be)["current"]["call"], 1)
        run_action(be, "call", ADMIN, {"n": 2})
        self.assertEqual(st_(be)["current"]["call"], 2)
        bid(be, 2, 125)
        self.assertEqual(st_(be)["current"]["call"], 0)
        self.assertTrue(run_action(be, "sold", ADMIN).ok)
        self.assertEqual(st_(be)["managers"]["m2"]["purse"], 10000 - 125)

    def test_mark_unsold_blocked_when_bid_exists(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        self.assertFalse(run_action(be, "unsold", ADMIN).ok)

    def test_undo_last_bid(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        bid(be, 2, 125)
        run_action(be, "undo_bid", ADMIN)
        c = st_(be)["current"]
        self.assertEqual((c["leader"], c["bid"]), ("m1", 100))
        run_action(be, "undo_bid", ADMIN)
        c = st_(be)["current"]
        self.assertEqual((c["leader"], c["bid"]), (None, None))

    def test_undo_last_sale(self):
        be = env(n=2, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "sold", ADMIN)
        self.assertTrue(run_action(be, "undo_sale", ADMIN).ok)
        s = st_(be)
        self.assertEqual(s["managers"]["m1"]["purse"], 10000)
        self.assertEqual(s["managers"]["m1"]["squad"], [])
        self.assertEqual(s["current"]["bid"], 100)
        self.assertEqual(A.validate_state(s), [])

    def test_pause_resume(self):
        be = env(players=[("A", 100)])
        up(be)
        run_action(be, "pause", ADMIN, {"flag": True})
        self.assertIn("paused", bid(be, 1, 100).message)
        run_action(be, "pause", ADMIN, {"flag": False})
        self.assertTrue(bid(be, 1, 100).ok)

    def test_bring_up_rules(self):
        be = env(players=[("A", 100), ("B", 100)])
        up(be)
        self.assertFalse(run_action(be, "bring", ADMIN, {}).ok)    # one lot at a time

    def test_requeue_and_shuffle(self):
        be = env(n=2, players=[("A", 100), ("B", 90), ("C", 80)])
        up(be)
        run_action(be, "withdraw", mgr(be, 1))
        run_action(be, "withdraw", mgr(be, 2))                     # A unsold
        self.assertTrue(run_action(be, "requeue", ADMIN).ok)
        self.assertTrue(run_action(be, "shuffle", ADMIN).ok)
        self.assertEqual(A.validate_state(st_(be)), [])


class Settings(unittest.TestCase):
    def S(self, **o):
        base = {"title": "T", "subtitle": "", "purse": 10000, "max_squad": 8, "step": 25, "reserve": 20}
        return {"settings": {**base, **o}}

    def test_bad_values(self):
        be = env()
        for bad in ({"purse": 5}, {"step": 0}, {"max_squad": "x"}, {"reserve": -1}, {"title": ""}, {"purse": True},
                    {"purse": 200, "max_squad": 10, "reserve": 50}):
            self.assertFalse(run_action(be, "settings", ADMIN, self.S(**bad)).ok, bad)

    def test_locked_during_live_lot(self):
        be = env()
        up(be)
        self.assertFalse(run_action(be, "settings", ADMIN, self.S(step=50)).ok)
        self.assertTrue(run_action(be, "settings", ADMIN, self.S(title="New title")).ok)

    def test_purse_locked_after_sales_and_squad_floor(self):
        be = env(n=2, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "sold", ADMIN)
        self.assertFalse(run_action(be, "settings", ADMIN, self.S(purse=20000)).ok)
        self.assertFalse(run_action(be, "settings", ADMIN, self.S(max_squad=0)).ok)
        self.assertTrue(run_action(be, "settings", ADMIN, self.S(step=50)).ok)
        self.assertEqual(A.validate_state(st_(be)), [])

    def test_purse_change_resets_purses_before_sales(self):
        be = env()
        self.assertTrue(run_action(be, "settings", ADMIN, self.S(purse=5000)).ok)
        self.assertEqual(st_(be)["managers"]["m1"]["purse"], 5000)


class ImportsAndBackups(unittest.TestCase):
    def test_malformed_csv(self):
        for text in ("", "name,origin\nA,B", "name,base_price\nA,abc", "name,base_price\nA,5-10", "name,base_price\nA,1.2.3",
                     "name,base_price\nA,0", "name,base_price\nA,10,extra", "name,base_price\n,50", "name,base_price\nA"):
            rows, errs = A.parse_players_csv(text)
            self.assertTrue(errs or not rows, text)
        rows, errs = A.parse_players_csv("Name,Origin,Role,Base Price\nAarav,Delhi,Bat,₹100\nB,,,75 L\nC,,,50.0")
        self.assertEqual((errs, [r["base"] for r in rows]), ([], [100, 75, 50]))

    def test_duplicate_players_rejected(self):
        be = env(players=[("A", 100)])
        r = run_action(be, "add_players", ADMIN, {"text": "name,origin,base_price\nA,X,50", "replace": False})
        self.assertFalse(r.ok)

    def test_manager_input_validation(self):
        be = MemoryBackend()
        for t in ("T, M, 12", "T, M", "T, M, abcd", "T, M, 12345678901"):
            self.assertFalse(run_action(be, "add_managers", ADMIN, {"text": t, "replace": True}).ok, t)
        self.assertFalse(run_action(be, "add_managers", ADMIN, {"text": "T, M, 1234\nt, N, 5678", "replace": True}).ok)

    def test_csv_export_formula_guard(self):
        self.assertEqual(A.csv_safe("=1+1"), "'=1+1")
        self.assertEqual(A.csv_safe("Ravi"), "Ravi")

    def test_backup_roundtrip(self):
        be = env(n=2, players=[("A", 100), ("B", 80)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "sold", ADMIN)
        raw = json.dumps(A.make_backup(st_(be))).encode()
        self.assertNotIn(b"pin_hash", raw)
        cand, note = A.parse_backup(raw)
        self.assertIsNotNone(cand, note)
        self.assertFalse(run_action(be, "restore", ADMIN, {"state": cand, "confirm": "no"}).ok)
        old_ver = be.state["managers"]["m1"]["session_ver"]
        r = run_action(be, "restore", ADMIN, {"state": cand, "confirm": "RESTORE"})
        self.assertTrue(r.ok, r.message)
        s = st_(be)
        self.assertNotEqual(s["managers"]["m1"]["session_ver"], old_ver)
        self.assertTrue(A.check_pin("1001", s["managers"]["m1"]["pin_hash"]))      # same team keeps its PIN
        self.assertEqual(A.validate_state(s), [])

    def test_corrupted_and_invalid_backups(self):
        be = env()
        good = A.make_backup(st_(be))
        for raw in (b"not json", b"[]", b'{"x":1}', b"\xff\xfe", b"{" * 10):
            self.assertIsNone(A.parse_backup(raw)[0])
        tampered = copy.deepcopy(good)
        tampered["state"]["managers"]["m1"]["purse"] = 1
        self.assertIn("checksum", A.parse_backup(json.dumps(tampered).encode())[1])
        bad = copy.deepcopy(good)                        # valid checksum, invalid content (negative purse)
        bad["state"]["managers"]["m1"]["purse"] = -5
        bad["checksum"] = hashlib.sha256(json.dumps(bad["state"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        cand, why = A.parse_backup(json.dumps(bad).encode())
        self.assertIsNone(cand)
        self.assertIn("validation", why)
        self.assertIsNone(A.parse_backup(b"x" * (A.MAX_STATE_BYTES + 1))[0])

    def test_legacy_backup_and_hash_migration(self):
        salt = "aa" * 8
        legacy_hash = hashlib.pbkdf2_hmac("sha256", b"4321", bytes.fromhex(salt), 60_000).hex()
        old = A.new_state()
        old["managers"] = {"m1": {"id": "m1", "team": "T", "name": "N", "salt": salt, "pin_hash": legacy_hash, "purse": 10000, "squad": []}}
        cand, note = A.parse_backup(json.dumps(old).encode())
        self.assertIsNotNone(cand, note)
        self.assertTrue(A.check_pin("4321", cand["managers"]["m1"]["pin_hash"]))
        self.assertFalse(A.check_pin("0000", cand["managers"]["m1"]["pin_hash"]))

    def test_public_state_has_no_secrets(self):
        be = env()
        pub = json.dumps(A.public_state(st_(be)))
        for word in ("pin_hash", "session_ver", "pbkdf2"):
            self.assertNotIn(word, pub)

    def test_invariants_detect_corruption(self):
        be = env(n=2, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "sold", ADMIN)
        s = st_(be)
        self.assertEqual(A.validate_state(s), [])
        for mutate in (lambda x: x["managers"]["m1"].update(purse=-1), lambda x: x["managers"]["m2"]["squad"].append(x["managers"]["m1"]["squad"][0]),
                       lambda x: x["players"][0].update(status="pending"), lambda x: x["sales"].append(copy.deepcopy(x["sales"][0])),
                       lambda x: x["managers"]["m1"].update(purse=9999)):
            c = copy.deepcopy(s)
            mutate(c)
            self.assertTrue(A.validate_state(c))


class Security(unittest.TestCase):
    def test_roles_enforced(self):
        be = env(players=[("A", 100)])
        up(be)
        self.assertIn("Not authorised", run_action(be, "sold", mgr(be, 1)).message)
        self.assertIn("Not authorised", run_action(be, "bid", ADMIN, {"amount": 100}).message)
        self.assertIn("Not authorised", run_action(be, "bid", None, {"amount": 100}).message)
        self.assertFalse(run_action(be, "bid", {"role": "manager", "id": "m99", "ver": "x"}, {"amount": 100}).ok)

    def test_cannot_impersonate_via_args(self):
        be = env(players=[("A", 100)])
        up(be)
        r = run_action(be, "bid", mgr(be, 1), {"amount": 100, "mid": "m2", "id": "m2"})
        self.assertTrue(r.ok)
        self.assertEqual(st_(be)["current"]["leader"], "m1")

    def test_session_invalidation_on_pin_reset_and_wrong_token(self):
        be = env(players=[("A", 100)])
        up(be)
        old = mgr(be, 1)
        forged = {**old, "ver": "deadbeef"}
        self.assertIn("session", run_action(be, "bid", forged, {"amount": 100}).message)
        self.assertTrue(run_action(be, "reset_pin", ADMIN, {"mid": "m1", "pin": "999999"}).ok)
        self.assertIn("session", run_action(be, "bid", old, {"amount": 100}).message)
        self.assertTrue(run_action(be, "bid", mgr(be, 1), {"amount": 100}).ok)
        self.assertTrue(A.check_pin("999999", be.state["managers"]["m1"]["pin_hash"]))
        self.assertFalse(run_action(be, "reset_pin", ADMIN, {"mid": "m1", "pin": "12"}).ok)

    def test_pin_hashing(self):
        h = A.hash_pin("1234")
        self.assertTrue(h.startswith("pbkdf2_sha256$"))
        self.assertTrue(A.check_pin("1234", h))
        self.assertFalse(A.check_pin("1235", h))
        self.assertNotEqual(h, A.hash_pin("1234"))          # salted
        self.assertFalse(A.check_pin("1234", None))

    def test_admin_password_policy(self):
        self.assertTrue(A.admin_password_problem(""))
        self.assertTrue(A.admin_password_problem("short"))
        self.assertEqual(A.admin_password_problem("a-long-passphrase-123"), "")

    def test_rate_limit_lockout(self):
        be = MemoryBackend()
        for _ in range(A.PIN_MAX_FAILS):
            ok, msg = A.verify_login(be, "mgr:m1", lambda: False, A.PIN_MAX_FAILS, 60)
            self.assertFalse(ok)
        ok, msg = A.verify_login(be, "mgr:m1", lambda: True, A.PIN_MAX_FAILS, 60)
        self.assertFalse(ok)
        self.assertIn("Too many", msg)                      # even the right PIN is refused while locked
        ok, _ = A.verify_login(be, "mgr:m2", lambda: True, A.PIN_MAX_FAILS, 60)
        self.assertTrue(ok)                                 # other accounts unaffected

    def test_login_blocked_when_database_down(self):
        be = Flaky()
        be.down = True
        be.auth_check = lambda k: (_ for _ in ()).throw(BackendError("down", unknown=True))
        ok, msg = A.verify_login(be, "admin", lambda: True, 5, 60)
        self.assertFalse(ok)
        self.assertIn("unavailable", msg)


class Persistence(unittest.TestCase):
    def test_concurrent_identical_bids_only_one_wins(self):
        be = env(n=8, players=[("A", 100)])
        up(be)
        barrier, results = threading.Barrier(8), []

        def worker(i):
            barrier.wait()
            results.append(bid(be, i, 100))

        ts = [threading.Thread(target=worker, args=(i,)) for i in range(1, 9)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        self.assertEqual(sum(r.ok for r in results), 1)
        s = st_(be)
        self.assertEqual(len(s["current"]["history"]), 1)
        self.assertEqual(A.validate_state(s), [])

    def test_concurrent_different_bids_stay_consistent(self):
        be = env(n=8, players=[("A", 100)])
        up(be)
        barrier = threading.Barrier(8)

        def worker(i):
            barrier.wait()
            bid(be, i, 100 + 25 * i)

        ts = [threading.Thread(target=worker, args=(i,)) for i in range(1, 9)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        s = st_(be)
        self.assertEqual(A.validate_state(s), [])
        h = s["current"]["history"]
        self.assertEqual(s["current"]["bid"], h[-1]["amt"])
        self.assertEqual(s["current"]["leader"], h[-1]["mid"])
        self.assertTrue(all(a["amt"] < b["amt"] for a, b in zip(h, h[1:])))

    def test_concurrent_sales_never_double_sell(self):
        be = env(n=3, players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        res = []
        ts = [threading.Thread(target=lambda: res.append(run_action(be, "sold", ADMIN))) for _ in range(5)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        self.assertEqual(sum(r.ok for r in res), 1)
        s = st_(be)
        self.assertEqual(len(s["sales"]), 1)
        self.assertEqual(s["managers"]["m1"]["purse"], 9900)

    def test_retry_with_same_key_is_not_applied_twice(self):
        be = env(players=[("A", 100)])
        up(be)
        state, rev = be.get_state()
        new = copy.deepcopy(state)
        A.apply_action(new, "bid", mgr(be, 1), {"amount": 100})
        first = be.commit(rev, new, "K1", "manager:m1", "ok")
        again = be.commit(rev, new, "K1", "manager:m1", "ok")          # replayed request, stale revision, same key
        self.assertEqual((first["status"], again["status"]), ("committed", "duplicate"))
        self.assertEqual(len(st_(be)["current"]["history"]), 1)
        # and a user-level repeat of the same bid is refused by the rules (leader cannot rebid)
        self.assertFalse(run_action(be, "bid", mgr(be, 1), {"amount": 100}, idem_key="K2").ok)
        self.assertEqual(len(st_(be)["current"]["history"]), 1)

    def test_lost_reply_is_recovered_without_double_charge(self):
        be = env(n=2, players=[("A", 100)], backend=Flaky())
        up(be)
        bid(be, 1, 100)
        be.fail_after = 1                                   # sale commits, reply lost, retry hits the idempotency key
        r = run_action(be, "withdraw", mgr(be, 2))
        self.assertTrue(r.ok, r.message)
        s = st_(be)
        self.assertEqual(len(s["sales"]), 1)
        self.assertEqual(s["managers"]["m1"]["purse"], 9900)

    def test_total_commit_outage_reports_unknown_and_changes_nothing_extra(self):
        be = env(players=[("A", 100)], backend=Flaky())
        up(be)
        be.fail_before = 99
        r = bid(be, 1, 100)
        self.assertFalse(r.ok)
        self.assertEqual(r.status, "unknown")
        be.fail_before = 0
        self.assertIsNone(st_(be)["current"]["leader"])

    def test_definitive_database_failure_during_mutation(self):
        be = env(players=[("A", 100)], backend=Flaky())
        up(be)
        before = copy.deepcopy(be.state)
        be.definitive = True
        r = bid(be, 1, 100)
        self.assertFalse(r.ok)
        self.assertEqual(be.state, before)

    def test_database_down_before_mutation(self):
        be = env(players=[("A", 100)], backend=Flaky())
        up(be)
        be.down = True
        r = bid(be, 1, 100)
        self.assertEqual((r.ok, r.status), (False, "unavailable"))

    def test_revision_conflict_revalidates_against_latest_state(self):
        be = env(players=[("A", 100)], backend=Flaky())
        up(be)
        be.before_commit = lambda: bid(be, 2, 125)          # a rival's bid lands first
        r = bid(be, 1, 100)                                 # now stale: minimum is 150
        self.assertEqual(r.status, "rejected")
        self.assertIn("minimum", r.message)
        self.assertEqual(st_(be)["current"]["leader"], "m2")

    def test_conflict_then_still_legal_bid_is_accepted(self):
        be = env(players=[("A", 100)], backend=Flaky())
        up(be)
        be.before_commit = lambda: run_action(be, "pause", ADMIN, {"flag": False})   # unrelated change bumps the revision
        self.assertTrue(bid(be, 1, 100).ok)

    def test_expected_revision_rejects_stale_admin_action(self):
        be = env(players=[("A", 100)])
        up(be)
        bid(be, 1, 100)
        seen = be.get_rev()
        bid(be, 2, 125)                                     # a new bid arrives after the organiser's screen loaded
        r = run_action(be, "sold", ADMIN, expected_rev=seen)
        self.assertEqual(r.status, "stale")
        self.assertEqual(len(st_(be)["sales"]), 0)

    def test_startup_outage_is_read_only_and_never_overwrites(self):
        be = env(players=[("A", 100)], backend=Flaky())
        snapshot = copy.deepcopy(be.state)
        be.down = True
        store = A.Store(be)
        sn = store.read()
        self.assertFalse(sn.ok)
        self.assertIsNone(sn.view)
        self.assertEqual(be.init_calls, 0)
        self.assertEqual(be.state, snapshot)
        be.down = False
        store.invalidate()
        self.assertTrue(store.read().ok)

    def test_missing_config_disables_not_memory_fallback(self):
        sn = A.Store(None, "bad config").read()
        self.assertFalse(sn.ok)
        self.assertIsNone(sn.view)

    def test_memory_backend_is_labelled_non_persistent(self):
        self.assertFalse(MemoryBackend.persistent)
        self.assertTrue(A.SupabaseBackend.persistent)

    def test_state_consistent_after_restart(self):
        be = env(n=2, players=[("A", 100), ("B", 80)])
        up(be)
        bid(be, 1, 100)
        run_action(be, "sold", ADMIN)
        up(be)
        bid(be, 2, 80)
        before = A.Store(be).read()
        after = A.Store(be).read()                          # "new process" reading the same database
        self.assertEqual((before.rev, before.view), (after.rev, after.view))
        self.assertEqual(A.validate_state(st_(be)), [])

    def test_inconsistent_stored_state_blocks_mutations_but_allows_restore(self):
        be = env(players=[("A", 100)])
        good = A.make_backup(st_(be))
        be.state["managers"]["m1"]["purse"] = -1
        self.assertEqual(run_action(be, "bring", ADMIN, {}).status, "unavailable")
        sn = A.Store(be).read()
        self.assertTrue(sn.invalid)
        cand, _ = A.parse_backup(json.dumps(good).encode())
        self.assertTrue(run_action(be, "restore", ADMIN, {"state": cand, "confirm": "RESTORE"}).ok)

    def test_full_auction_invariants(self):
        be = env(n=4, purse=2000, squad=3, reserve=50, players=[(f"P{i}", 50 + 10 * i) for i in range(10)])
        import random
        rnd = random.Random(7)
        for _ in range(10):
            if not run_action(be, "bring", ADMIN, {}).ok:
                break
            for _ in range(30):
                if st_(be)["current"] is None:
                    break
                i = rnd.randint(1, 4)
                if rnd.random() < 0.25:
                    run_action(be, "withdraw", mgr(be, i))
                else:
                    s = st_(be)
                    bid(be, i, A.min_next(s) + 25 * rnd.randint(0, 3))
            if st_(be)["current"]:
                run_action(be, "sold" if st_(be)["current"]["bid"] else "unsold", ADMIN)
            self.assertEqual(A.validate_state(st_(be)), [])


if __name__ == "__main__":
    unittest.main()
