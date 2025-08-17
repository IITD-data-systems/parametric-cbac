import json
from pathlib import Path
import random

import numpy as np
from decimal import Decimal
from datetime import date

# paths / inputs
json_path = "keys.json"
table_path = Path("tables")
tables_to_use_path = Path("tables.txt")
policy_txt = Path("policies.txt")
combo_txt = Path("combination.txt")

# params
policies = 10
depth = 5
rng_seed = 42  # set an int for reproducibility

if rng_seed is not None:
    random.seed(rng_seed)
    np.random.seed(rng_seed)

# dtype mapping (schema dtype -> category / python type hint)
pg_to_py = {
    "integer": int,
    "numeric": Decimal,
    "character": str,
    "date": date,
}

numeric_like = {"integer", "numeric"}
text_like = {"character"}
date_like = {"date"}

# load keys / constraints
with open(json_path, "r", encoding="utf-8") as f:
    data = json.load(f)

primary_keys = data.get("primary_keys", {})
foreign_keys = data.get("foreign_keys", [])
no_const = set(data.get("no_const", []))

# tables to use
with open(tables_to_use_path, "r", encoding="utf-8") as f:
    tables_to_use = [line.strip() for line in f if line.strip()]

# load schema once (names + dtypes)
def load_schema_and_dtypes(root: Path):
    schema_cols = {}     # table -> [col, ...]
    dtype_map = {}       # table -> {col: dtype}
    for tdir in root.iterdir():
        if not (tdir / "schema.json").exists():
            continue
        with open(tdir / "schema.json", "r", encoding="utf-8") as f:
            s = json.load(f)
        cols = [c["name"] for c in s]
        dtypes = {c["name"]: c["dtype"] for c in s}
        schema_cols[tdir.name] = cols
        dtype_map[tdir.name] = dtypes
    return schema_cols, dtype_map

schema, dtype_map = load_schema_and_dtypes(table_path)
tables_we_have = list(schema.keys())
print(tables_we_have)
print(tables_to_use)

def get_data_type(table, col):
    return dtype_map.get(table, {}).get(col)

def pick_random_col_for_pred(table):
    pk_cols = {col for keycols in primary_keys.get(table, []) for col in keycols}
    fk_cols = {
        src.split(".", 1)[1]
        for src, dst in foreign_keys
        if src.startswith(f"{table}.")
    }
    nc_cols = {
        col.split(".", 1)[1]
        for col in no_const
        if col.startswith(f"{table}.")
    }
    all_cols = set(schema.get(table, []))
    candidates = list(all_cols - pk_cols - fk_cols - nc_cols)
    if not candidates:
        return None
    return random.choice(candidates)

def pick_random_col_for_const(table):
    # same as above but exclude only pk/fk; allow const unless full name appears in no_const
    pk_cols = {col for keycols in primary_keys.get(table, []) for col in keycols}
    fk_cols = {
        src.split(".", 1)[1]
        for src, dst in foreign_keys
        if src.startswith(f"{table}.")
    }
    all_cols = set(schema.get(table, []))
    candidates = [c for c in (all_cols - pk_cols - fk_cols) if f"{table}.{c}" not in no_const]
    if not candidates:
        return None
    return random.choice(candidates)

def allowed_ops_for_dtype(dtype):
    if dtype in numeric_like or dtype in date_like:
        return ["=", "!=", ">=", "<=", ">", "<"]
    else:
        return ["=", "!="]

def load_const_candidate(table, col, dtype):
    arr_path = table_path / table / f"{col}.npy"
    if not arr_path.exists():
        return None
    try:
        value = np.load(arr_path, allow_pickle=True)
    except Exception:
        return None
    n = int(getattr(value, "shape", [0])[0]) if hasattr(value, "shape") else 0
    if n <= 0:
        return None
    # Q1..Q3 slice (25%..75%)
    start = int((n - 1) * 0.25)
    end = int((n - 1) * 0.75)
    if end < start:
        start, end = 0, n - 1
    candidates = value[start : end + 1]
    if candidates.size == 0:
        candidates = value
    raw = random.choice(candidates.tolist())
    # format literal per dtype
    if dtype in text_like:
        s = str(raw)
        s = s.replace("'", "''")
        return f"'{s}'"
    elif dtype in date_like:
        return f"'{str(raw)}'"
    else:
        return str(raw)

def make_col_col_clause():
    # try a few times to get a compatible pair
    for _ in range(50):
        t1 = random.choice(tables_to_use)
        t2 = random.choice(tables_to_use)
        c1 = pick_random_col_for_pred(t1)
        c2 = pick_random_col_for_pred(t2)
        if c1 is None or c2 is None:
            continue
        if t1 == t2 and c1 == c2:
            continue
        dt1 = get_data_type(t1, c1)
        dt2 = get_data_type(t2, c2)
        if dt1 is None or dt2 is None or dt1 != dt2:
            continue
        ops = allowed_ops_for_dtype(dt1)
        # avoid ordering ops on text
        if dt1 in text_like:
            ops = ["=", "!="]
        op = random.choice(ops)
        return f"{t1}.{c1} {op} {t2}.{c2}"
    return None

def make_col_const_clause():
    # try a few times to pick a legal const
    for _ in range(50):
        t = random.choice(tables_to_use)
        c = pick_random_col_for_const(t)
        if c is None:
            continue
        dtype = get_data_type(t, c)
        if dtype is None:
            continue
        lit = load_const_candidate(t, c, dtype)
        if lit is None:
            continue
        ops = allowed_ops_for_dtype(dtype)
        if dtype in text_like:
            ops = ["=", "!="]
        op = random.choice(ops)
        return f"{t}.{c} {op} {lit}"
    return None

def build_policy(depth_now):
    clauses = []
    attempts = 0
    max_attempts = 10000
    while len(clauses) < depth_now and attempts < max_attempts:
        attempts += 1
        variant = random.randint(0, 1)  # 0: col-col, 1: col-const
        clause = None
        if variant == 0:
            clause = make_col_const_clause()
        else:
            clause = make_col_const_clause()
        if clause:
            clauses.append(clause)
    return " and ".join(clauses)

def link_present(policy_str, left, right):
    # detect either direction of equality link
    a = f"{left} = {right}"
    b = f"{right} = {left}"
    return (a in policy_str) or (b in policy_str)

def second_pass_fix(policy_str):
    need_lineitem = "lineitem." not in policy_str
    has_orders = "orders." in policy_str
    has_customer = "customer." in policy_str
    has_lineitem = "lineitem." in policy_str

    # required links
    l_o = "lineitem.l_orderkey"
    o_o = "orders.o_orderkey"
    o_c = "orders.o_custkey"
    c_c = "customer.c_custkey"

    clauses_to_add = []

    # rule 1: if lineitem is not present → add both links to chain LI–O–C
    if not has_lineitem:
        # add both links to pull lineitem (and possibly orders) into the policy
        if not link_present(policy_str, l_o, o_o):
            clauses_to_add.append(f"{l_o} = {o_o}")
        if not link_present(policy_str, o_c, c_c):
            clauses_to_add.append(f"{o_c} = {c_c}")
    else:
        # rule 2: if LI and O present but missing link → add it
        if has_lineitem and has_orders and not link_present(policy_str, l_o, o_o):
            clauses_to_add.append(f"{l_o} = {o_o}")
        # if O and C present but missing link → add it
        if has_orders and has_customer and not link_present(policy_str, o_c, c_c):
            clauses_to_add.append(f"{o_c} = {c_c}")

        # if LI present but O not present, yet C present, still ensure the chain by adding both links
        if has_lineitem and (not has_orders) and has_customer:
            if not link_present(policy_str, l_o, o_o):
                clauses_to_add.append(f"{l_o} = {o_o}")
            if not link_present(policy_str, o_c, c_c):
                clauses_to_add.append(f"{o_c} = {c_c}")

    if clauses_to_add:
        if policy_str.strip():
            policy_str = policy_str + " and " + " and ".join(clauses_to_add)
        else:
            policy_str = " and ".join(clauses_to_add)
    return policy_str

def build_boolean_combo(n):
    ids = [f"P{i+1}" for i in range(n)]
    random.shuffle(ids)
    # iteratively combine with random and/or + parentheses
    exprs = ids[:]
    while len(exprs) > 1:
        i = random.randrange(0, len(exprs) - 1)
        left = exprs.pop(i)
        right = exprs.pop(i)
        op = random.choice(["and", "or"])
        exprs.insert(i, f"({left} {op} {right})")
    return exprs[0] if exprs else ""

# -------- first pass: generate policies --------
all_policies = []
for i in range(policies):
    depth_now = random.randint(1, depth)
    body = build_policy(depth_now)
    all_policies.append(body)
    if i%10==0: print(f"Number of policies: {i}")

# -------- second pass: enforce LI–O–C chain --------
fixed_policies = []
for p in all_policies:
    fixed_policies.append(second_pass_fix(p))

# label and write policies
with policy_txt.open("w", encoding="utf-8") as f:
    for idx, body in enumerate(fixed_policies, start=1):
        f.write(f"P{idx}: {body}\n")

# write combination
combo_expr = build_boolean_combo(policies)
with combo_txt.open("w", encoding="utf-8") as f:
    f.write(combo_expr + "\n")

# sanity logs
print(f"wrote {len(fixed_policies)} policies to {policy_txt}")
print(f"combination: {combo_expr}")
