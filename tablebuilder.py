import os
import json
import psycopg2
import numpy as np

from decimal import Decimal
from datetime import date

CHUNK_SIZE = 10_000
PG_CONN = dict(
    host="localhost",
    port=5432,
    dbname="tpch",
    user="postgres",
    password="12345",
)

tables = [
    "lineitem", "orders", "customer",
    "nation", "region", "supplier",
    "part", "partsupp"
]

# map Postgres types to Python types
pg_to_py = {
    "integer": int,
    "numeric": Decimal,
    "character": str,
    "character varying": str,
    "date": date,
}


def fetch_schema_and_count(conn_info, table, schema="public"):
    with psycopg2.connect(**conn_info) as conn:
        with conn.cursor() as cur:
            cur.execute("""
                SELECT column_name, data_type
                FROM information_schema.columns
                WHERE table_schema = %s
                  AND table_name   = %s
                ORDER BY ordinal_position;
            """, (schema, table))
            cols = cur.fetchall()
            names, dtypes = zip(*cols)
            norm_types = [
                "character" if t in ("character varying", "character") else t
                for t in dtypes
            ]
            cur.execute(f"SELECT COUNT(*) FROM {schema}.{table};")
            total = cur.fetchone()[0]
    return list(names), norm_types, total


def process_table(table, conn_info, schema="public"):
    base = os.path.join("tables", table)
    os.makedirs(base, exist_ok=True)

    col_names, col_types, total_rows = fetch_schema_and_count(conn_info, table, schema)

    # write schema.json
    schema_obj = [{"name": n, "dtype": t} for n, t in zip(col_names, col_types)]
    with open(os.path.join(base, "schema.json"), "w") as f:
        json.dump(schema_obj, f, indent=2)

    # first pass: collect distinct values
    global_sets = [set() for _ in col_names]
    with psycopg2.connect(**conn_info) as conn:
        with conn.cursor(name=f"{table}_d") as cur:
            cur.itersize = CHUNK_SIZE
            cur.execute(f"SELECT * FROM {schema}.{table};")
            while True:
                rows = cur.fetchmany(CHUNK_SIZE)
                if not rows:
                    break
                for row in rows:
                    for i, v in enumerate(row):
                        global_sets[i].add(v)

    # save each column’s distinct .npy with proper dtype
    values_by_col = []
    for i, (name, vals) in enumerate(zip(col_names, global_sets)):
        sorted_vals = sorted(vals)
        values_by_col.append(sorted_vals)

        pg_type = col_types[i]
        py_type = pg_to_py.get(pg_type)

        if py_type is int:
            arr = np.array(sorted_vals, dtype=np.int64)
        elif py_type is Decimal:
            # convert Decimal → float64
            arr = np.array([float(v) for v in sorted_vals], dtype=np.float64)
        elif py_type is str:
            arr = np.array(sorted_vals, dtype=str)
        elif py_type is date:
            # use daily datetime64
            arr = np.array(sorted_vals, dtype="datetime64[D]")
        else:
            # fallback (shouldn’t hit if your pg_to_py covers all dtypes)
            arr = np.array(sorted_vals, dtype=object)

        # pickle only if dtype is object
        allow_pickle = arr.dtype.hasobject
        np.save(os.path.join(base, f"{name}.npy"), arr, allow_pickle=allow_pickle)

    # build mapping from value → code
    code_maps = [
        {v: idx for idx, v in enumerate(vals)}
        for vals in values_by_col
    ]

    # second pass: encode each row as integers
    codes = np.empty((total_rows, len(col_names)), dtype=np.int32)
    row_cursor = 0
    with psycopg2.connect(**conn_info) as conn:
        with conn.cursor(name=f"{table}_e") as cur:
            cur.itersize = CHUNK_SIZE
            cur.execute(f"SELECT * FROM {schema}.{table};")
            while True:
                rows = cur.fetchmany(CHUNK_SIZE)
                if not rows:
                    break
                for r, row in enumerate(rows):
                    for c, v in enumerate(row):
                        codes[row_cursor + r, c] = code_maps[c][v]
                row_cursor += len(rows)

    # save the integer codes
    np.save(os.path.join(base, "codes.npy"), codes)
    print(f"→ {table}: wrote {total_rows}×{len(col_names)} codes")


if __name__ == "__main__":
    for tbl in tables:
        process_table(tbl, PG_CONN)
