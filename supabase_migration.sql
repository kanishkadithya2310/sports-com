-- =====================================================================================
-- Intellics Auction Room v2: Supabase / PostgreSQL migration
-- Run ONCE in Supabase: SQL Editor -> New query -> paste everything -> Run.
-- The SQL editor runs as the database owner ("postgres"), which is what this script needs.
-- It is safe to run again (every statement is "if not exists" / "create or replace").
--
-- DESIGN: one JSONB row per auction (id = 'main') plus a revision counter.
--   auction_commit() locks that row (SELECT ... FOR UPDATE), refuses the write if the caller's expected
--   revision is not the current one, refuses a repeated idempotency key, then writes the new state and
--   increments the revision, all in ONE transaction. Business rules live in the app (and are re-checked
--   against the latest state on every retry); the database guarantees atomicity, ordering and no double-apply.
-- ACCESS: the three tables are locked away from every API role. The only way in is the functions below,
--   and only the server-side secret key (service_role) may run them. The anon/publishable key can do nothing.
-- =====================================================================================

create table if not exists public.auction_state (
  id          text primary key,
  data        jsonb       not null,
  updated_at  timestamptz not null default now()
);
-- If you used the original app, this table already exists; add the revision column to it.
alter table public.auction_state add column if not exists rev bigint not null default 0;

create table if not exists public.auction_ops (          -- one row per committed action (idempotency + audit)
  event_id    text        not null,
  idem_key    text        not null,
  rev         bigint      not null,
  actor       text        not null,
  message     text        not null,
  created_at  timestamptz not null default now(),
  primary key (event_id, idem_key)
);
create index if not exists auction_ops_created_idx on public.auction_ops (created_at);

create table if not exists public.auction_auth (         -- login attempt counters (shared by every app instance)
  key           text primary key,
  fails         int         not null default 0,
  locked_until  timestamptz,
  updated_at    timestamptz not null default now()
);

alter table public.auction_state enable row level security;   -- RLS on, with NO policies = no API access
alter table public.auction_ops   enable row level security;
alter table public.auction_auth  enable row level security;

-- ---------------------------------------------------------------- functions
create or replace function public.auction_get(p_event text)
returns jsonb language plpgsql security definer set search_path = public as $$
declare r jsonb;
begin
  select jsonb_build_object('rev', rev, 'data', data) into r from public.auction_state where id = p_event;
  return r;                                   -- NULL when the auction row does not exist yet
end $$;

create or replace function public.auction_rev(p_event text)
returns bigint language plpgsql security definer set search_path = public as $$
declare r bigint;
begin
  select rev into r from public.auction_state where id = p_event;
  return r;
end $$;

create or replace function public.auction_init(p_event text, p_data jsonb)
returns boolean language plpgsql security definer set search_path = public as $$
declare n int;
begin                                          -- insert-if-absent: can NEVER overwrite an existing auction
  insert into public.auction_state (id, data, rev) values (p_event, p_data, 0) on conflict (id) do nothing;
  get diagnostics n = row_count;
  return n = 1;
end $$;

create or replace function public.auction_commit(
  p_event text, p_expected_rev bigint, p_new jsonb, p_idem text, p_actor text, p_message text)
returns jsonb language plpgsql security definer set search_path = public as $$
declare v_rev bigint; v_op public.auction_ops%rowtype;
begin
  if p_idem is null or length(p_idem) < 8 or length(p_idem) > 100 then
    raise exception 'bad idempotency key';
  end if;
  if jsonb_typeof(p_new) <> 'object' or not (p_new ? 'managers') or not (p_new ? 'players')
     or not (p_new ? 'settings') or octet_length(p_new::text) > 2000000 then
    raise exception 'refusing malformed or oversized state';
  end if;

  select rev into v_rev from public.auction_state where id = p_event for update;   -- row lock: commits queue here
  if not found then
    return jsonb_build_object('status', 'missing');
  end if;

  select * into v_op from public.auction_ops where event_id = p_event and idem_key = p_idem;
  if found then                                  -- this exact request was already committed: report, do NOT redo
    return jsonb_build_object('status', 'duplicate', 'rev', v_op.rev, 'message', v_op.message);
  end if;

  if v_rev <> p_expected_rev then                -- someone else committed since the caller read the state
    return jsonb_build_object('status', 'conflict', 'rev', v_rev);
  end if;

  update public.auction_state
     set data = jsonb_set(p_new, '{rev}', to_jsonb(v_rev + 1)), rev = v_rev + 1, updated_at = now()
   where id = p_event;
  insert into public.auction_ops (event_id, idem_key, rev, actor, message)
       values (p_event, p_idem, v_rev + 1, left(coalesce(p_actor, ''), 80), left(coalesce(p_message, ''), 500));
  delete from public.auction_ops where created_at < now() - interval '3 days';     -- keep the table tiny
  return jsonb_build_object('status', 'committed', 'rev', v_rev + 1);
end $$;

create or replace function public.auction_auth_check(p_key text)
returns jsonb language plpgsql security definer set search_path = public as $$
declare v_until timestamptz;
begin
  select locked_until into v_until from public.auction_auth where key = p_key;
  if v_until is not null and v_until > now() then
    return jsonb_build_object('locked', true, 'seconds', ceil(extract(epoch from (v_until - now())))::int);
  end if;
  return jsonb_build_object('locked', false, 'seconds', 0);
end $$;

create or replace function public.auction_auth_record(p_key text, p_ok boolean, p_max int, p_lock int)
returns jsonb language plpgsql security definer set search_path = public as $$
declare v_fails int;
begin
  if p_ok then
    delete from public.auction_auth where key = p_key;
    return jsonb_build_object('locked', false, 'seconds', 0);
  end if;
  insert into public.auction_auth (key, fails, updated_at) values (p_key, 1, now())
  on conflict (key) do update
     set fails = case when public.auction_auth.locked_until is not null and public.auction_auth.locked_until <= now()
                      then 1 else public.auction_auth.fails + 1 end,
         updated_at = now()
  returning fails into v_fails;
  if v_fails >= p_max then
    update public.auction_auth set fails = 0, locked_until = now() + make_interval(secs => p_lock) where key = p_key;
    return jsonb_build_object('locked', true, 'seconds', p_lock);
  end if;
  return jsonb_build_object('locked', false, 'seconds', 0);
end $$;

-- ---------------------------------------------------------------- permissions (least privilege)
do $$
declare r text;
begin
  revoke all on table public.auction_state, public.auction_ops, public.auction_auth from public;
  revoke all on function public.auction_get(text), public.auction_rev(text), public.auction_init(text, jsonb),
    public.auction_commit(text, bigint, jsonb, text, text, text), public.auction_auth_check(text),
    public.auction_auth_record(text, boolean, int, int) from public;
  foreach r in array array['anon', 'authenticated', 'service_role'] loop
    if exists (select 1 from pg_roles where rolname = r) then
      execute format('revoke all on table public.auction_state, public.auction_ops, public.auction_auth from %I', r);
      execute format('revoke all on function public.auction_get(text), public.auction_rev(text), public.auction_init(text, jsonb), '
                     'public.auction_commit(text, bigint, jsonb, text, text, text), public.auction_auth_check(text), '
                     'public.auction_auth_record(text, boolean, int, int) from %I', r);
    end if;
  end loop;
  if exists (select 1 from pg_roles where rolname = 'service_role') then      -- ONLY the server-side key may call them
    grant execute on function public.auction_get(text), public.auction_rev(text), public.auction_init(text, jsonb),
      public.auction_commit(text, bigint, jsonb, text, text, text), public.auction_auth_check(text),
      public.auction_auth_record(text, boolean, int, int) to service_role;
  end if;
end $$;
