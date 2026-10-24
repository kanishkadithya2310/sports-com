# Intellics Auction Room

A Streamlit live player auction (cricket + football events) with Supabase storage.

## Views
- Projector: `?view=screen`   - Manager bidding: `?view=bid`   - Organiser: `?view=admin`

## Features
- Auction rule validation, manager PIN sessions, bid history, Supabase persistence (survives restarts)
- **Event dropdown** (Admin page, top): switch between Cricket and Football; screens follow. Each event has its own data
- **Neon highlight** on the projector manager card of the team currently leading the bid
- **Images**: committee logo (`static/logo.png`), team crests (`static/teams/<team-name>.png`),
  player photos (`static/players/<player-name>.png`); names are lowercase with dashes. Missing images are skipped
- Sport-aware squad stats (cricket roles, or one row per role for football etc.)
- Manual player pick or automatic next-in-queue; unsold players can be re-queued

## Files that must be in the GitHub repo
`auction_app.py`, `requirements.txt`, `.streamlit/config.toml` (turns on image serving), `static/` folder.
Never commit `.streamlit/secrets.toml`.

## Setup
1. Supabase -> SQL Editor -> paste `supabase_migration.sql` -> Run (once).
2. Secrets (Streamlit Cloud -> app settings -> Secrets, or local `.streamlit/secrets.toml`):
```toml
SUPABASE_URL = "https://YOUR-PROJECT.supabase.co"
SUPABASE_KEY = "sb_secret_..."        # the secret key, never the publishable key
ADMIN_PIN = "a-passphrase-of-12+-characters"
# optional: EVENTS = "main:Cricket,football:Football,basketball:Basketball"
```
3. Run locally: `python -m pip install -r requirements.txt` then `streamlit run auction_app.py`

## Testing
Test data, the rule tests and the bot simulator are kept outside this repo (local use only).
