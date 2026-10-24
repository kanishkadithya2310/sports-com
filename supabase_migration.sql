-- =====================================================================================
-- Intellics Auction Room: Supabase / PostgreSQL migration
--
-- HOW TO RUN: Supabase dashboard -> SQL Editor -> New query -> paste this whole file -> Run.
-- It is safe to run more than once (idempotent). It never drops your data.
--
-- HOW IT WORKS
--   The app keeps the whole auction as one JSON document and talks to the database ONLY
--   through the six auction_* functions below. Every change is a compare-and-swap on a
--   revision number, with an idempotency key so a retried request can never apply twice.
--
--   On every committed change the database also copies the JSON into plain tables
--   (managers, players, sales, bids) so you can browse and export them in the
--   Table Editor or with SQL. Those tables are READ-ONLY reports: never edit them by hand,
--   they are rebuilt from the JSON on the next commit. All money is in LAKHS.
--
-- SECURITY
--   Row Level Security is ON for every table and no policies exist, and all privileges are
--   revoked from the public/anon/authenticated roles. Only the server-side secret key
--   (service_role) can use these objects. NEVER put the secret key in browser code.
--   Manager PIN hashes live only in auction_events.data; the report tables exclude them.
-- =====================================================================================

-- ---------------------------------------------------------------- core tables
create table if not exists public.auction_events (
    event_id   text primary key,
    data       jsonb       not null,                 -- the full auction state (includes PIN hashes)
    rev        bigint      not null default 0,       -- bumps by 1 on every committed change
    created_at timestamptz not null default now(),
    updated_at timestamptz not null default now(),
    constraint auction_events_data_is_object check (jsonb_typeof(data) = 'object')
);

-- Permanent audit trail of every committed action; also the idempotency ledger.
create table if not exists public.auction_ops (
    event_id   text        not null references public.auction_events(event_id) on delete cascade,
    idem       text        not null,                 -- idempotency key from the app
    rev        bigint      not null,                 -- revision this action produced
    actor      text,                                 -- 'admin', 'manager:m3', ...
    message    text,                                 -- e.g. 'Bid of Rs 150L accepted. You lead.'
    created_at timestamptz not null default now(),
    primary key (event_id, idem)
);
create index if not exists auction_ops_event_rev_idx on public.auction_ops (event_id, rev);

-- Failed-PIN counter and lockout, shared across all app instances.
create table if not exists public.auction_auth (
    key          text primary key,
    fails        integer     not null default 0,
    locked_until timestamptz,
    updated_at   timestamptz not null default now()
);

-- ---------------------------------------------------------------- readable report tables
create table if not exists public.auction_managers (
    event_id      text   not null references public.auction_events(event_id) on delete cascade,
    manager_id    text   not null,
    team          text   not null,
    manager_name  text,
    initial_purse bigint,                            -- lakhs
    purse_left    bigint,                            -- lakhs still available
    spent         bigint,                            -- lakhs spent so far
    squad_size    integer,
    primary key (event_id, manager_id)
);

create table if not exists public.auction_players (
    event_id    text   not null references public.auction_events(event_id) on delete cascade,
    player_id   text   not null,
    queue_pos   integer,
    name        text   not null,
    origin      text,
    role        text,
    base_price  bigint,                              -- lakhs
    status      text,                                -- pending | live | sold | unsold
    sold_to     text,                                -- manager_id
    sold_price  bigint,                              -- lakhs
    primary key (event_id, player_id)
);

create table if not exists public.auction_sales (
    event_id   text   not null references public.auction_events(event_id) on delete cascade,
    player_id  text   not null,
    manager_id text   not null,
    price      bigint not null,                      -- lakhs
    sold_at    timestamptz,
    primary key (event_id, player_id)
);

create table if not exists public.auction_bids (
    id         bigint generated always as identity primary key,
    event_id   text   not null references public.auction_events(event_id) on delete cascade,
    player_id  text   not null,
    manager_id text,
    amount     bigint not null,                      -- lakhs
    bid_at     timestamptz,
    outcome    text                                  -- 'sold' (bid history of a sold player) | 'live' (on the block now)
);
create index if not exists auction_bids_event_player_idx on public.auction_bids (event_id, player_id);

-- ---------------------------------------------------------------- lock everything down
alter table public.auction_events   enable row level security;
alter table public.auction_ops      enable row level security;
alter table public.auction_auth     enable row level security;
alter table public.auction_managers enable row level security;
alter table public.auction_players  enable row level security;
alter table public.auction_sales    enable row level security;
alter table public.auction_bids     enable row level security;

revoke all on public.auction_events, public.auction_ops, public.auction_auth,
              public.auction_managers, public.auction_players,
              public.auction_sales, public.auction_bids
    from public, anon, authenticated;

-- ---------------------------------------------------------------- helpers
-- Timestamp cast that returns NULL instead of failing on odd input.
create or replace function public.auction_ts(p text)
returns timestamptz
language plpgsql immutable
set search_path = public, pg_temp
as $$
begin
    return p::timestamptz;
exception when others then
    return null;
end;
$$;

-- Rebuilds the report tables for one event from its JSON state.
create or replace function public.auction_sync_reports(p_event text, p_data jsonb)
returns void
language plpgsql
security definer
set search_path = public, pg_temp
as $$
declare
    v_init bigint := coalesce((p_data #>> '{settings,purse}')::bigint, 0);
begin
    delete from auction_managers where event_id = p_event;
    delete from auction_players  where event_id = p_event;
    delete from auction_sales    where event_id = p_event;
    delete from auction_bids     where event_id = p_event;

    insert into auction_managers (event_id, manager_id, team, manager_name,
                                  initial_purse, purse_left, spent, squad_size)
    select p_event, e.k, coalesce(e.v ->> 'team', ''), e.v ->> 'name',
           v_init,
           (e.v ->> 'purse')::bigint,
           v_init - (e.v ->> 'purse')::bigint,
           coalesce(jsonb_array_length(case when jsonb_typeof(e.v -> 'squad') = 'array'
                                            then e.v -> 'squad' end), 0)
    from jsonb_each(p_data -> 'managers') as e(k, v);

    insert into auction_players (event_id, player_id, queue_pos, name, origin, role,
                                 base_price, status, sold_to, sold_price)
    select p_event, t.x ->> 'id', t.ord::integer, coalesce(t.x ->> 'name', ''),
           t.x ->> 'origin', t.x ->> 'role',
           (t.x ->> 'base')::bigint, t.x ->> 'status',
           t.x ->> 'sold_to', (t.x ->> 'price')::bigint
    from jsonb_array_elements(p_data -> 'players') with ordinality as t(x, ord);

    insert into auction_sales (event_id, player_id, manager_id, price, sold_at)
    select p_event, t.x ->> 'pid', t.x ->> 'mid', (t.x ->> 'price')::bigint, auction_ts(t.x ->> 't')
    from jsonb_array_elements(case when jsonb_typeof(p_data -> 'sales') = 'array'
                                   then p_data -> 'sales' else '[]'::jsonb end) as t(x)
    on conflict do nothing;

    -- bid history of sold players
    insert into auction_bids (event_id, player_id, manager_id, amount, bid_at, outcome)
    select p_event, s.x ->> 'pid', h.x ->> 'mid', (h.x ->> 'amt')::bigint, auction_ts(h.x ->> 't'), 'sold'
    from jsonb_array_elements(case when jsonb_typeof(p_data -> 'sales') = 'array'
                                   then p_data -> 'sales' else '[]'::jsonb end) as s(x),
         jsonb_array_elements(case when jsonb_typeof(s.x #> '{snapshot,history}') = 'array'
                                   then s.x #> '{snapshot,history}' else '[]'::jsonb end) with ordinality as h(x, n)
    order by s.x ->> 'pid', h.n;

    -- bids on the player currently on the block
    insert into auction_bids (event_id, player_id, manager_id, amount, bid_at, outcome)
    select p_event, p_data #>> '{current,pid}', h.x ->> 'mid', (h.x ->> 'amt')::bigint,
           auction_ts(h.x ->> 't'), 'live'
    from jsonb_array_elements(case when jsonb_typeof(p_data #> '{current,history}') = 'array'
                                   then p_data #> '{current,history}' else '[]'::jsonb end) with ordinality as h(x, n)
    order by h.n;
end;
$$;

-- ---------------------------------------------------------------- the six functions the app calls
-- 1) Latest state: {"data": {...}, "rev": N}, or NULL when no row exists yet.
create or replace function public.auction_get(p_event text)
returns jsonb
language sql
stable
security definer
set search_path = public, pg_temp
as $$
    select jsonb_build_object('data', data, 'rev', rev)
    from auction_events
    where event_id = p_event;
$$;

-- 2) Cheap revision check used for polling: bigint, or NULL when no row exists.
create or replace function public.auction_rev(p_event text)
returns bigint
language sql
stable
security definer
set search_path = public, pg_temp
as $$
    select rev from auction_events where event_id = p_event;
$$;

-- 3) Insert-if-absent. Returns true only if it created the row. Never overwrites.
create or replace function public.auction_init(p_event text, p_data jsonb)
returns boolean
language plpgsql
security definer
set search_path = public, pg_temp
as $$
declare
    v_rows integer;
begin
    if p_data is null or jsonb_typeof(p_data) <> 'object' then
        raise exception 'refused: malformed state' using errcode = '22023';
    end if;
    insert into auction_events (event_id, data, rev)
    values (p_event, jsonb_set(p_data, '{rev}', '0'::jsonb), 0)
    on conflict (event_id) do nothing;
    get diagnostics v_rows = row_count;
    if v_rows > 0 then
        begin
            perform auction_sync_reports(p_event, p_data);
        exception when others then
            raise warning 'auction_sync_reports failed: %', sqlerrm;
        end;
    end if;
    return v_rows > 0;
end;
$$;

-- 4) Atomic compare-and-swap commit.
--    Returns {"status":"committed","rev":N} | {"status":"conflict","rev":N}
--          | {"status":"duplicate","rev":N,"message":"..."} | {"status":"missing"}
create or replace function public.auction_commit(
    p_event        text,
    p_expected_rev bigint,
    p_new          jsonb,
    p_idem         text,
    p_actor        text,
    p_message      text
)
returns jsonb
language plpgsql
security definer
set search_path = public, pg_temp
as $$
declare
    v_rev bigint;
    v_op  record;
begin
    -- lock the row so concurrent bids are processed one at a time
    select rev into v_rev from auction_events where event_id = p_event for update;
    if not found then
        return jsonb_build_object('status', 'missing');
    end if;

    -- a replayed request (same key) is answered with the original result, never re-applied
    select rev, message into v_op from auction_ops where event_id = p_event and idem = p_idem;
    if found then
        return jsonb_build_object('status', 'duplicate', 'rev', v_op.rev, 'message', v_op.message);
    end if;

    -- someone else committed first: the app re-reads and re-validates
    if p_expected_rev is distinct from v_rev then
        return jsonb_build_object('status', 'conflict', 'rev', v_rev);
    end if;

    if p_new is null or jsonb_typeof(p_new) <> 'object'
       or jsonb_typeof(p_new -> 'managers') <> 'object'
       or jsonb_typeof(p_new -> 'players') <> 'array' then
        raise exception 'refused: malformed state' using errcode = '22023';
    end if;
    if octet_length(p_new::text) > 2000000 then
        raise exception 'refused: state too large' using errcode = '22023';
    end if;

    v_rev := v_rev + 1;
    update auction_events
       set data = jsonb_set(p_new, '{rev}', to_jsonb(v_rev)),
           rev = v_rev,
           updated_at = now()
     where event_id = p_event;

    insert into auction_ops (event_id, idem, rev, actor, message)
    values (p_event, p_idem, v_rev, left(p_actor, 200), left(p_message, 2000));

    -- refresh the readable tables; a failure here must never block a live bid
    begin
        perform auction_sync_reports(p_event, p_new);
    exception when others then
        raise warning 'auction_sync_reports failed: %', sqlerrm;
    end;

    return jsonb_build_object('status', 'committed', 'rev', v_rev);
end;
$$;

-- 5) Is this login key currently locked out?  -> {"locked": bool, "seconds": int}
create or replace function public.auction_auth_check(p_key text)
returns jsonb
language plpgsql
security definer
set search_path = public, pg_temp
as $$
declare
    v_until timestamptz;
begin
    select locked_until into v_until from auction_auth where key = p_key;
    if v_until is not null and v_until > now() then
        return jsonb_build_object('locked', true,
                                  'seconds', ceil(extract(epoch from (v_until - now())))::int);
    end if;
    return jsonb_build_object('locked', false, 'seconds', 0);
end;
$$;

-- 6) Record a login attempt. Success clears the counter; the p_max-th failure locks for p_lock seconds.
create or replace function public.auction_auth_record(p_key text, p_ok boolean, p_max integer, p_lock integer)
returns jsonb
language plpgsql
security definer
set search_path = public, pg_temp
as $$
declare
    v_fails integer;
begin
    if p_ok then
        delete from auction_auth where key = p_key;
        return jsonb_build_object('locked', false, 'seconds', 0);
    end if;

    delete from auction_auth where locked_until < now() - interval '1 day';   -- tidy old rows

    insert into auction_auth (key, fails, updated_at)
    values (p_key, 1, now())
    on conflict (key) do update
        set fails = auction_auth.fails + 1, updated_at = now()
    returning fails into v_fails;

    if v_fails >= p_max then
        update auction_auth
           set fails = 0, locked_until = now() + make_interval(secs => p_lock)
         where key = p_key;
        return jsonb_build_object('locked', true, 'seconds', p_lock);
    end if;
    return jsonb_build_object('locked', false, 'seconds', 0);
end;
$$;

-- only the server-side secret key (service_role) may call these
revoke all on function public.auction_ts(text)                                   from public, anon, authenticated;
revoke all on function public.auction_sync_reports(text, jsonb)                  from public, anon, authenticated;
revoke all on function public.auction_get(text)                                  from public, anon, authenticated;
revoke all on function public.auction_rev(text)                                  from public, anon, authenticated;
revoke all on function public.auction_init(text, jsonb)                          from public, anon, authenticated;
revoke all on function public.auction_commit(text, bigint, jsonb, text, text, text) from public, anon, authenticated;
revoke all on function public.auction_auth_check(text)                           from public, anon, authenticated;
revoke all on function public.auction_auth_record(text, boolean, integer, integer) from public, anon, authenticated;

grant execute on function public.auction_ts(text)                                   to service_role;
grant execute on function public.auction_sync_reports(text, jsonb)                  to service_role;
grant execute on function public.auction_get(text)                                  to service_role;
grant execute on function public.auction_rev(text)                                  to service_role;
grant execute on function public.auction_init(text, jsonb)                          to service_role;
grant execute on function public.auction_commit(text, bigint, jsonb, text, text, text) to service_role;
grant execute on function public.auction_auth_check(text)                           to service_role;
grant execute on function public.auction_auth_record(text, boolean, integer, integer) to service_role;

-- ---------------------------------------------------------------- handy views for the organiser
-- Open these in the Supabase Table Editor / SQL Editor.
create or replace view public.auction_standings with (security_invoker = true) as
select m.event_id, m.team, m.manager_name, m.initial_purse, m.spent,
       m.purse_left, m.squad_size
from public.auction_managers m
order by m.event_id, m.purse_left desc;

create or replace view public.auction_results with (security_invoker = true) as
select p.event_id, p.name as player, p.origin, p.role, p.base_price,
       s.price as sold_price, m.team, m.manager_name, s.sold_at
from public.auction_sales s
join public.auction_players  p on p.event_id = s.event_id and p.player_id  = s.player_id
join public.auction_managers m on m.event_id = s.event_id and m.manager_id = s.manager_id
order by s.sold_at;

revoke all on public.auction_standings, public.auction_results from public, anon, authenticated;

-- Quick checks after running (optional):
--   select * from public.auction_standings;   -- team purses left
--   select * from public.auction_results;     -- who bought whom, for how much
--   select * from public.auction_ops order by created_at desc limit 20;   -- audit trail
--
-- To wipe the auction and start fresh (the app recreates an empty one on next load):
--   delete from public.auction_events where event_id = 'main';
