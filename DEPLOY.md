# Auction Room v2: deployment guide (beginner friendly)

## 0. What is in the folder
| File | What it is |
|---|---|
| `auction_app.py` | The whole app (projector, manager console, organiser) |
| `supabase_migration.sql` | Database setup, run once in Supabase |
| `requirements.txt` | Python packages (pinned) |
| `.streamlit/config.toml` | Dark theme |
| `secrets.toml.example` | Template for your three secrets |
| `test_auction.py` | Offline tests (no database needed) |
| `test_postgres_integration.py` | Optional database test (throwaway database only) |

## 1. Save the files
Put the files in a GitHub repository exactly as in the table (keep `.streamlit/config.toml` inside a folder named `.streamlit`).
Do **not** upload your real secrets. `.gitignore` already excludes `.streamlit/secrets.toml`.

## 2. Create the database and run the SQL
1. supabase.com -> your project (or New project, free plan is enough).
2. Left menu **SQL Editor** -> **New query**.
3. Open `supabase_migration.sql`, copy everything, paste, press **Run**. "Success" means done.
   It runs as the database owner, which is the default in the SQL editor. You can run it again safely.
4. If you used the old app, your old row is kept. Its data is upgraded when first read. Old PINs still work.
   (If the old data is inconsistent the app will say so; restore a backup in the organiser view.)

## 3. Secrets
Supabase -> **Project Settings -> API Keys**. Copy the **secret** key (`sb_secret_...`) or, on older projects, the **service_role** key.
**Never use the anon/publishable key**: the database refuses it by design. Never put the secret key in the code or GitHub.

In Streamlit Cloud: your app -> **Settings -> Secrets**, paste the three lines from `secrets.toml.example` with real values:
`ADMIN_PIN` (at least 12 characters), `SUPABASE_URL`, `SUPABASE_KEY`.
Without the two Supabase secrets the app starts in a loud **DEMO MODE** banner: memory only, lost on restart, not for the event.
With them set but wrong/unreachable the app goes read-only and says so; it never silently falls back to memory.

## 4. Deploy
share.streamlit.io -> **New app** -> pick the repo -> main file `auction_app.py` -> Deploy. (`requirements.txt` is used automatically.)

## 5. Set up managers and players (organiser view)
Open `https://YOUR-APP.streamlit.app/?view=admin`, sign in, go to **Setup**.
1. **Settings**: purse (lakhs), squad size, bid step, reserve. 100 lakh = 1 Cr.
2. **Managers**: one per line `Team, Manager, PIN`. Leave the PIN out and a random 6-digit PIN is generated and shown **once**. Write them down.
3. **Players**: upload/paste CSV with header `name,origin,role,base_price` (whole lakhs).
4. Return to **Live control**.

## 6. The three web addresses
- Projector: `https://YOUR-APP.streamlit.app/?view=screen` (press F11 for full screen)
- Managers: `https://YOUR-APP.streamlit.app/?view=bid`
- Organiser: `https://YOUR-APP.streamlit.app/?view=admin`

## 7. Test before the event (15 minutes)
1. Open the projector page on one laptop and the organiser page on another. Top-right should say **SYNCED**.
2. Organiser: **Load demo data** (or your real data), then **Bring up player**.
3. On a phone/laptop open the manager link, sign in with a team + PIN, place a bid. The projector should update within ~2 seconds.
4. Wrong PIN 5 times: that team locks for 2 minutes (counter is stored in the database, so it holds on every server).
5. Organiser: Going once, Going twice, SOLD, Undo last sale. Confirm purses and squads on the projector.
6. Reset the auction (type RESET) and delete the demo data before the real event.
A manager must sign in again after refreshing the page: the sign-in lives only in the server-side session. That is by design.

## 8. Backup and restore
- **Results & backup** tab -> **Download full backup (JSON)**. Do this before the event and after every few lots.
  The file has a checksum and contains **no PINs**.
- Restore: upload the file in the same tab. It is validated, you must type `RESTORE`, and all signed-in sessions end.
  Teams whose PIN is unchanged keep it; others get a new PIN in Setup -> "Reset one manager's PIN".
- Old-format backups from the previous app are accepted if they pass validation.

## 9. If something breaks
- **Red banner "Database unavailable"**: Wi-Fi or Supabase is down. The screens keep the last known state, buttons are disabled, nothing is lost.
  Wait for **SYNCED** to return (automatic). If the organiser's action says "Could not confirm whether this was saved", reload and look at
  the projector first, then repeat only if it did not happen.
- **Streamlit app restarted**: no problem, everything is in the database. Managers sign in again.
- **Phone hotspot backup**: connect the organiser laptop and projector laptop to a hotspot if the college Wi-Fi fails.
- **Database lost or corrupted**: re-run the SQL, sign in as organiser, restore the latest backup.
- **"Saved auction data failed its consistency check"**: use **Results & backup -> Restore** with your last backup.

## 10. Running the tests
Offline (no database, no Streamlit install required):
```
python -m unittest -v test_auction
```
Optional database test against a THROWAWAY Postgres (see the header of `test_postgres_integration.py`).

## 11. Behaviour changes and fixed defects
Fixed: process-local lock + async background saves (could lose or reorder writes, silently fell back to memory); all state was kept in
memory per server; PINs/hashes were visible to the same process-wide state; settings could be changed during a live lot; restore accepted
almost any JSON; malformed base prices were guessed (`5-10` became 510); PIN rate limit was per-process; CSV export allowed formula injection.
Changed on purpose: withdrawing is blocked while paused; undo-bid, SOLD, mark-unsold, undo-sale, reset and restore reject if the organiser's
screen is out of date (a bid arrived meanwhile); purse is locked once sales exist; bidding rules are locked while a lot is live; duplicate
players on import are rejected; PINs are hashed with 200k-iteration salted PBKDF2; admin password must be 12+ characters.
Unchanged: all bidding rules, the automatic sale/unsold when no challenger remains, and the reserve rule.

## 12. What the app enforces vs what you must do
Enforced on the server: role + session check on every action; manager identity comes from the server-side session, never from the browser;
salted PBKDF2 hashes and constant-time comparison; database-backed lockouts; revision checks + idempotency keys in PostgreSQL; invariant
validation before every commit; input/CSV/JSON validation; the projector gets a copy with no hashes or tokens; the secret key never reaches the browser.
Your responsibility: keep `SUPABASE_KEY` and `ADMIN_PIN` secret and rotate them if leaked; use HTTPS (Streamlit Cloud does); share PINs privately;
keep the Streamlit app's sharing set to who you need; keep downloaded backups private (they contain player/team data).
Limits: the projector page is public to anyone with the link (read-only); a determined attacker with the manager PINs *is* that manager;
backup checksums detect damage, not deliberate forgery.
