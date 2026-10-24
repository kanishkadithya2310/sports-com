# Intellics Auction Room

A Streamlit-based live player auction application.

## Features

- Projector view: `?view=screen`
- Manager bidding view: `?view=bid`
- Organiser/admin view: `?view=admin`
- Auction rule validation, manager sessions, bid history, and backend persistence integration.

## Requirements

- Python 3.10 or newer recommended
- pip

## Run locally

```bash
python -m venv .venv
```

Activate the virtual environment:

- Windows PowerShell: `.venv\\Scripts\\Activate.ps1`
- macOS/Linux: `source .venv/bin/activate`

Install packages and launch:

```bash
python -m pip install -r requirements.txt
streamlit run auction_app.py
```

Open the local URL Streamlit prints (usually `http://localhost:8501`). Add `?view=screen`, `?view=bid`, or `?view=admin` to the URL to select a view.

## Run the automated offline tests

```bash
python -m unittest -v test_auction
```

These tests exercise auction rules, validation, security, and simulated persistence behavior. They do not prove that a real Supabase/PostgreSQL instance is configured correctly.

## Secrets and database setup

Do not commit passwords, PINs, API keys, or database credentials. Configure secrets through Streamlit secrets locally (`.streamlit/secrets.toml`) or through your deployment platform's secrets settings.

The database migration file supplied in the current upload set could not be included: the file named `supabase_migration.sql` appears to contain an HTML search page rather than SQL. Obtain the real migration SQL from your original project before configuring persistent Supabase/PostgreSQL storage. Do not run the HTML file as a migration.
