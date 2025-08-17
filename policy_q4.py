import re
import json
from pathlib import Path

policies_path = Path("policies.txt")
combo_path = Path("combination.txt")
tables_root = Path("tables")
out_path = Path("qr_policy.txt")

role = "rls_user"
policy_name = "p"
target_table = "lineitem"

# load dtypes from tables/*/schema.json
def load_dtypes(root: Path):
    dtype_map = {}
    for tdir in root.iterdir():
        sj = tdir / "schema.json"
        if not sj.exists():
            continue
        with sj.open("r", encoding="utf-8") as f:
            s = json.load(f)
        dtype_map[tdir.name] = {c["name"]: c["dtype"] for c in s}
    return dtype_map

dtype_map = load_dtypes(tables_root)

def col_dtype(table, col):
    return dtype_map.get(table, {}).get(col)

# tokenization
token_re = re.compile(r"(\band\b|\bor\b|\(|\))", flags=re.IGNORECASE)
op_split_re = re.compile(r"\s*(=|!=|>=|<=|>|<)\s*")
col_ref_re = re.compile(r"^([A-Za-z_]\w*)\.([A-Za-z_]\w*)$")
lit_num_re = re.compile(r"^[-+]?\d+(\.\d+)?$")

def read_policies(pth):
    mapping = {}
    with pth.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or ":" not in line:
                continue
            pid, body = line.split(":", 1)
            mapping[pid.strip()] = body.strip()
    return mapping

def read_combo(pth):
    return pth.read_text(encoding="utf-8").strip()

def is_literal(s):
    s = s.strip()
    if s.startswith("'") and s.endswith("'"):
        return True
    return lit_num_re.fullmatch(s) is not None

def parse_pred(s):
    parts = op_split_re.split(s.strip(), maxsplit=1)
    if len(parts) != 3:
        return None, None, None
    return parts[0].strip(), parts[1], parts[2].strip()

# ---- literal normalization based on column dtype ----
def normalize_literal_for_column(lit, table, col):
    dt = col_dtype(table, col)
    if not dt:
        return lit  # no info; pass through

    # strip surrounding quotes for processing
    raw = lit
    quoted = raw.startswith("'") and raw.endswith("'")
    unq = raw[1:-1] if quoted else raw

    if dt in ("integer", "numeric"):
        # ensure bare numeric
        if quoted and lit_num_re.fullmatch(unq):
            return unq
        return unq if lit_num_re.fullmatch(unq) else raw  # leave as-is if not numeric
    if dt == "date":
        # ensure DATE 'YYYY-MM-DD'
        # accept already-typed DATE '...'
        if raw.lower().startswith("date '") and raw.endswith("'"):
            return raw
        s = unq if quoted else raw
        return f"DATE '{s}'"
    # character/text
    s = unq if quoted else raw
    s = s.replace("'", "''")
    return f"'{s}'"

# fk chain for EXISTS
joins = {
    ("lineitem", "orders"): "o.o_orderkey = lineitem.l_orderkey",
    ("orders", "customer"): "o.o_custkey = c.c_custkey",
}

def ref_info(side):
    m = col_ref_re.match(side)
    if not m:
        return None
    return m.group(1), m.group(2)

def exists_sql_for_clause(lhs, op, rhs):
    l_ref = ref_info(lhs)
    r_ref = ref_info(rhs)

    # column-literal normalization
    if l_ref and is_literal(rhs):
        rhs = normalize_literal_for_column(rhs, l_ref[0], l_ref[1])
    if r_ref and is_literal(lhs):
        lhs = normalize_literal_for_column(lhs, r_ref[0], r_ref[1])

    tables = set()
    if l_ref: tables.add(l_ref[0])
    if r_ref: tables.add(r_ref[0])

    # inline if only lineitem + literal
    if (not tables) or tables == {"lineitem"}:
        return f"{lhs} {op} {rhs}", {
            (l_ref[0], l_ref[1])} if l_ref else set() | ({(r_ref[0], r_ref[1])} if r_ref else set())

    # build EXISTS
    use_orders = "orders" in tables or "customer" in tables
    use_customer = "customer" in tables

    from_sql = []
    where_terms = []
    idx_cols = set()

    if use_orders:
        from_sql.append("orders o")
        where_terms.append(joins[("lineitem", "orders")])
        idx_cols |= {("orders", "o_orderkey"), ("lineitem", "l_orderkey")}

    if use_customer:
        if not use_orders:
            from_sql.append("orders o")
            where_terms.append(joins[("lineitem", "orders")])
            idx_cols |= {("orders", "o_orderkey"), ("lineitem", "l_orderkey")}
        from_sql.append("customer c")
        where_terms.append(joins[("orders", "customer")])
        idx_cols |= {("orders", "o_custkey"), ("customer", "c_custkey")}

    def rewrite_side(side):
        info = ref_info(side)
        if not info:
            return side
        t, c = info
        if t == "orders":
            idx_cols.add(("orders", c))
            return f"o.{c}"
        if t == "customer":
            idx_cols.add(("customer", c))
            return f"c.{c}"
        if t == "lineitem":
            idx_cols.add(("lineitem", c))
            return f"lineitem.{c}"
        return side

    lhs_in = rewrite_side(lhs)
    rhs_in = rewrite_side(rhs)
    where_terms.append(f"{lhs_in} {op} {rhs_in}")

    from_clause = ", ".join(from_sql)
    where_clause = " and ".join(where_terms)
    return f"EXISTS (SELECT 1 FROM {from_clause} WHERE {where_clause})", idx_cols

def text_to_sql_predicate(text):
    lhs, op, rhs = parse_pred(text)
    if not op:
        used_cols = set()
        for token in re.findall(r"[A-Za-z_]\w*\.[A-Za-z_]\w*", text):
            t, c = token.split(".", 1)
            used_cols.add((t, c))
        return text, used_cols
    return exists_sql_for_clause(lhs, op, rhs)

def substitute_policies(expr, policy_map):
    return re.sub(r"\bP\d+\b", lambda m: f"({policy_map.get(m.group(0), '')})", expr)

def rewrite_expression(expr):
    tokens = token_re.split(expr)
    out = []
    used = set()
    for tok in tokens:
        t = tok.strip()
        if not t:
            continue
        if t.lower() in ("and", "or") or t in ("(", ")"):
            out.append(t.lower())
            continue
        # split residual conjunctions inside a policy body (your policies use 'and')
        parts = re.split(r"\band\b", t, flags=re.IGNORECASE)
        if len(parts) == 1:
            sql, cols = text_to_sql_predicate(t)
            out.append(sql)
            used |= cols
        else:
            subs = []
            for p in parts:
                sql, cols = text_to_sql_predicate(p.strip())
                subs.append(sql)
                used |= cols
            out.append(" and ".join(subs))
    return " ".join(out), used

def make_index_sql(cols):
    stmts, seen = [], set()
    for table, col in sorted(cols):
        key = (table, col)
        if key in seen:
            continue
        seen.add(key)
        stmts.append(f"CREATE INDEX IF NOT EXISTS idx_{table}_{col} ON {table} ({col});")
    return stmts

def main():
    policy_map = read_policies(policies_path)
    combo_expr = read_combo(combo_path)
    substituted = substitute_policies(combo_expr, policy_map)
    using_sql, used_cols = rewrite_expression(substituted)

    create_policy_sql = (
        f"CREATE POLICY {policy_name}\n"
        f"ON {target_table}\n"
        f"FOR SELECT\n"
        f"TO {role}\n"
        f"USING ({using_sql});"
    )

    index_sql = make_index_sql(used_cols)

    with out_path.open("w", encoding="utf-8") as f:
        f.write(create_policy_sql + "\n\n")
        for stmt in index_sql:
            f.write(stmt + "\n")

    print(f"wrote policy and {len(index_sql)} indexes to {out_path}")

if __name__ == "__main__":
    main()
