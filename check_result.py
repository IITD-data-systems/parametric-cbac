#!/usr/bin/env python3
import psycopg2
from pathlib import Path
import sys
import time
import sqlite3

# =========================
# Postgres CONFIG (UNCHANGED)
# =========================
PG_CONN = dict(
    host="localhost",
    port=5432,
    dbname="tpch",
    user="rls_user",
    password="secret",
)

RESULT_FILE = Path("result.txt")
SQLITE_DB_PATH = Path("tpch.sqlite")

# =========================
# --- SQLite helpers (FIXED/IMPROVED) ---
# =========================

def log(msg: str):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}")

def apply_speed_pragmas(conn: sqlite3.Connection, ram_gb: float = 10.0):
    """
    Speed-centric PRAGMAs for compute-only benchmarking (no durability).
    Uses ~80% of the provided RAM for SQLite page cache.
    """
    cache_kib = int(ram_gb * 1024 * 1024 * 0.8)  # negative => KiB
    conn.executescript(f"""
        PRAGMA journal_mode=OFF;
        PRAGMA synchronous=OFF;
        PRAGMA temp_store=MEMORY;
        PRAGMA locking_mode=EXCLUSIVE;
        PRAGMA cache_size=-{cache_kib};
        PRAGMA foreign_keys=OFF;
    """)

def drop_all_indexes(conn: sqlite3.Connection):
    cur = conn.cursor()
    cur.execute("""
        SELECT name FROM sqlite_master
        WHERE type='index' AND name NOT LIKE 'sqlite_%';
    """)
    idx_names = [r[0] for r in cur.fetchall()]
    for name in idx_names:
        cur.execute(f'DROP INDEX IF EXISTS "{name}";')
    conn.commit()
    print(f"Dropped {len(idx_names)} indexes.")

def apply_indexes_from_file(conn: sqlite3.Connection, path: Path):
    """
    Reads qr_policy.txt, skips the *first* line (policy), executes each subsequent non-empty line.
    """
    if not path.exists():
        print(f"qr_policy file not found at: {path}. Skipping index creation.")
        return 0

    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines:
        print("qr_policy.txt is empty; nothing to apply.")
        return 0

    # Skip exactly the first line (policy). Execute the rest as standalone statements.
    stmts = [ln.strip() for ln in lines[1:] if ln.strip()]
    created = 0
    cur = conn.cursor()
    for stmt in stmts:
        # Normalize statement to end with a semicolon for safety
        sql = stmt if stmt.endswith(";") else stmt + ";"
        try:
            cur.execute(sql)
            created += 1
        except sqlite3.Error as e:
            print(f"  ! Failed to execute: {sql}\n    -> {e}")
    conn.commit()
    print(f"Applied {created} index statements from {path}.")
    return created

def read_expected_set(path: Path):
    if not path.exists():
        raise FileNotFoundError(f"result.txt not found at: {path}")
    out = set()
    start = time.perf_counter()
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = [x.strip() for x in line.split(",")]
            if len(parts) != 2:
                raise ValueError(f"Bad line in result.txt: {line}")
            try:
                ok = int(parts[0]); ln = int(parts[1])
            except ValueError:
                ok = parts[0]; ln = parts[1]
            out.add((ok, ln))
    dur = (time.perf_counter() - start) * 1000
    log(f"Loaded {len(out):,} rows from {path.name} in {dur:.2f} ms")
    return out

def fetch_sqlite_set(conn: sqlite3.Connection, sql: str):
    """
    Streams rows (no fetchall) → lower memory, better responsiveness.
    Detects columns by name first, otherwise uses first two columns.
    """
    if not sql.strip():
        raise ValueError("SQL_QUERY is empty. Paste your SELECT into SQL_QUERY.")
    cur = conn.cursor()
    start = time.perf_counter()
    cur.execute(sql)

    # Column mapping
    cols = [c[0] for c in cur.description] if cur.description else []
    try:
        i_ok = cols.index("l_orderkey")
        i_ln = cols.index("l_linenumber")
    except ValueError:
        if len(cols) < 2:
            raise ValueError("Query must return at least two columns or named columns l_orderkey and l_linenumber.")
        i_ok, i_ln = 0, 1

    out = set()
    # Stream rows to avoid big temporary lists
    for r in cur:
        ok = r[i_ok]; ln = r[i_ln]
        try: ok = int(ok)
        except (TypeError, ValueError): pass
        try: ln = int(ln)
        except (TypeError, ValueError): pass
        out.add((ok, ln))

    dur = (time.perf_counter() - start) * 1000
    log(f"Fetched {len(out):,} rows from SQLite in {dur:.2f} ms")
    return out

# =========================
# Postgres side (UNCHANGED)
# =========================
def fetch_sqlite_set_UNUSED(*args, **kwargs):  # (keep name reserved in case of accidental imports)
    raise NotImplementedError

def read_expected_set_UNUSED(*args, **kwargs):
    raise NotImplementedError

def drop_all_indexes_UNUSED(*args, **kwargs):
    raise NotImplementedError

def apply_indexes_from_file_UNUSED(*args, **kwargs):
    raise NotImplementedError

def fetch_sqlite_set_UNUSED2(*args, **kwargs):
    raise NotImplementedError

# Special connection params for policy reset (UNCHANGED)
PG_CONN_ADMIN = dict(
    host="localhost",
    port=5432,
    dbname="tpch",
    user="postgres",
    password="12345",
)

def load_result_txt(path: Path):
    if not path.exists():
        print(f"ERROR: {path} not found", file=sys.stderr)
        sys.exit(1)
    rows = set()
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                ok, ln = line.split(",", 1)
                rows.add((int(ok), int(ln)))
            except Exception as e:
                print(f"WARNING: skipping malformed line: {line!r} ({e})", file=sys.stderr)
    return rows

def renew_and_add_policies_with_index():
    with psycopg2.connect(**PG_CONN_ADMIN) as conn:
        with conn.cursor() as cur:
            with open("qr_policy.txt", "r", encoding="utf-8") as f:
                policy_sql = f.read().strip()

            sql = f"""
            DO $$
            DECLARE
              r RECORD;
            BEGIN
              FOR r IN (
                SELECT 'DROP INDEX IF EXISTS ' || quote_ident(indexname) || ' CASCADE;' AS cmd
                FROM pg_indexes
                WHERE schemaname = 'public'
              )
              LOOP
                EXECUTE r.cmd;
              END LOOP;
            END
            $$ LANGUAGE plpgsql;

            DROP POLICY IF EXISTS p ON lineitem;
            {policy_sql}
            """

            cur.execute(sql)
            conn.commit()

def run_policy_query(cur):
    sql = """
        SELECT lineitem.l_orderkey, lineitem.l_linenumber
        FROM public.lineitem
    """
    cur.execute(sql)
    return {(int(r[0]), int(r[1])) for r in cur.fetchall()}

# =========================
# Main (SQLite-only flow by default)
# =========================
if __name__ == "__main__":
    # # --- SQLite benchmark path ---
    # conn = sqlite3.connect(SQLITE_DB_PATH)
    # apply_speed_pragmas(conn, ram_gb=10.0)  # leverages your 10 GB budget

    # # 1) Drop all indexes
    # t0 = time.perf_counter()
    # drop_all_indexes(conn)
    # log(f"Index drop finished in {(time.perf_counter()-t0)*1000:.2f} ms")

    # # 2) Apply index statements from qr_policy.txt (skip first line)
    # QR_POLICY_PATH = Path("qr_policy.txt")
    # t1 = time.perf_counter()
    # apply_indexes_from_file(conn, QR_POLICY_PATH)
    # log(f"Index creation finished in {(time.perf_counter()-t1)*1000:.2f} ms")

    # # 3) Your SELECT statement (KEEP THIS AS YOU NEED)
    # SQL_QUERY = """SELECT lineitem.l_orderkey, lineitem.l_linenumber
    #                FROM lineitem
    #                WHERE EXISTS (
    #                    SELECT 1
    #                    FROM orders o
    #                    WHERE o.o_orderstatus = 'O'
    #                      AND o.o_orderkey = lineitem.l_orderkey
    #                );"""
    # # Note: EXISTS is semantically equivalent to your original scalar subquery
    # # but can be faster in SQLite with an index on orders(o_orderkey).

    # # 4) Run SELECT and collect results
    # t2 = time.perf_counter()
    # got = fetch_sqlite_set(conn, SQL_QUERY)
    # log(f"Query finished in {(time.perf_counter()-t2)*1000:.2f} ms")

    # # 5) Read expected results and compare
    # RESULT_TXT_PATH = Path("result.txt")
    # expected = read_expected_set(RESULT_TXT_PATH)

    # if got == expected:
    #     print("MATCH ✅ — SQLite results and result.txt contain exactly the same (l_orderkey, l_linenumber) pairs.")
    # else:
    #     only_in_sqlite = got - expected
    #     only_in_file = expected - got
    #     print("MISMATCH ❌")
    #     print(f"  Pairs only in SQLite result: {len(only_in_sqlite)}")
    #     print(f"  Pairs only in result.txt    : {len(only_in_file)}")
    #     if only_in_sqlite:
    #         print("  Example only-in-SQLite:", list(only_in_sqlite)[:10])
    #     if only_in_file:
    #         print("  Example only-in-file  :", list(only_in_file)[:10])

    # conn.close()

    
    
    # 1) Load result.txt
    t0 = time.perf_counter()
    result_txt_set = load_result_txt(RESULT_FILE)
    t1 = time.perf_counter()
    print(f"[{time.strftime('%H:%M:%S')}] Loaded {len(result_txt_set):,} rows from {RESULT_FILE} in {(t1-t0)*1000:.2f} ms")
    
    # 2) Reset indexes & policies with admin connection
    t2 = time.perf_counter()
    renew_and_add_policies_with_index()
    t3 = time.perf_counter()
    print(f"[{time.strftime('%H:%M:%S')}] Reset indexes and policies in {(t3-t2)*1000:.2f} ms")
    
    # 3) Connect to Postgres (rls_user) and run query
    with psycopg2.connect(**PG_CONN) as conn_pg:
        with conn_pg.cursor() as cur_pg:
            t4 = time.perf_counter()
            sql_set = run_policy_query(cur_pg)
            t5 = time.perf_counter()
            print(f"[{time.strftime('%H:%M:%S')}] Fetched {len(sql_set):,} rows from Postgres in {(t5-t4)*1000:.2f} ms")
    
    # 4) Compare sets
    only_in_result = result_txt_set - sql_set
    only_in_sql    = sql_set - result_txt_set
    
    if not only_in_result and not only_in_sql:
        print("✅ Perfect match: result.txt equals SQL result.")
    else:
        print("❌ Mismatch detected.")
        print(f"  In result.txt but not in SQL: {len(only_in_result):,}")
        print(f"  In SQL but not in result.txt: {len(only_in_sql):,}")
        show_n = 10
        if only_in_result:
            print(f"  Examples only in result.txt (up to {show_n}): {list(only_in_result)[:show_n]}")
        if only_in_sql:
            print(f"  Examples only in SQL (up to {show_n}): {list(only_in_sql)[:show_n]}")
