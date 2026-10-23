"""OPTIONAL integration test for the SQL functions. NOT RUN by the author: you must run it yourself.

Use a THROWAWAY database (a free local Postgres or a second Supabase project), never the live auction:
    pip install -r requirements-dev.txt
    set TEST_DATABASE_URL=postgresql://user:pass@host:5432/dbname      (Windows)   /  export ... (Mac/Linux)
    python -m unittest -v test_postgres_integration
"""
import os
import threading
import unittest

try:
    import psycopg2
except ImportError:
    psycopg2 = None

URL = os.environ.get("TEST_DATABASE_URL")


@unittest.skipUnless(URL and psycopg2, "set TEST_DATABASE_URL and install psycopg2 to run")
class PostgresCommit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.conn = psycopg2.connect(URL)
        cls.conn.autocommit = True
        with cls.conn.cursor() as c:
            c.execute("drop table if exists public.auction_ops, public.auction_auth, public.auction_state cascade")
            c.execute(open(os.path.join(os.path.dirname(__file__), "supabase_migration.sql"), encoding="utf-8").read())

    def call(self, sql, *args):
        conn = psycopg2.connect(URL)
        conn.autocommit = True
        try:
            with conn.cursor() as c:
                c.execute(sql, args)
                return c.fetchone()[0]
        finally:
            conn.close()

    STATE = '{"settings":{},"managers":{},"players":[]}'

    def setUp(self):
        with self.conn.cursor() as c:
            c.execute("delete from public.auction_ops; delete from public.auction_state")
        self.assertTrue(self.call("select auction_init('t', %s::jsonb)", self.STATE))
        self.assertFalse(self.call("select auction_init('t', %s::jsonb)", '{"x":1}'))     # never overwrites

    def commit(self, rev, key):
        return self.call("select auction_commit('t', %s, %s::jsonb, %s, 'test', 'm')", rev, self.STATE, key)

    def test_exactly_one_of_many_simultaneous_commits_wins(self):
        out = []
        ts = [threading.Thread(target=lambda i=i: out.append(self.commit(0, f"key-number-{i}")["status"])) for i in range(12)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        self.assertEqual(out.count("committed"), 1)
        self.assertEqual(out.count("conflict"), 11)
        self.assertEqual(self.call("select auction_rev('t')"), 1)

    def test_idempotent_replay_and_conflict_and_bad_input(self):
        self.assertEqual(self.commit(0, "same-key-1")["status"], "committed")
        self.assertEqual(self.commit(0, "same-key-1")["status"], "duplicate")      # replay even with stale revision
        self.assertEqual(self.commit(0, "other-key-1")["status"], "conflict")
        self.assertEqual(self.call("select auction_rev('t')"), 1)
        with self.assertRaises(Exception):
            self.call("select auction_commit('t', 1, '[]'::jsonb, 'bad-shape-key', 'x', 'y')")

    def test_lockout_counter(self):
        for _ in range(4):
            self.assertFalse(self.call("select auction_auth_record('k', false, 5, 30)")["locked"])
        self.assertTrue(self.call("select auction_auth_record('k', false, 5, 30)")["locked"])
        self.assertTrue(self.call("select auction_auth_check('k')")["locked"])
        self.call("select auction_auth_record('k', true, 5, 30)")
        self.assertFalse(self.call("select auction_auth_check('k')")["locked"])


if __name__ == "__main__":
    unittest.main()
