import json
import re
from pathlib import Path

policies_path = Path("policies.txt")
combo_path = Path("combination.txt")
out_path = Path("path_ir.json")

# ----- parsing helpers -----

bool_tok_re = re.compile(r"\s*(\(|\)|\band\b|\bor\b|\bnot\b)\s*", flags=re.IGNORECASE)
op_split_re = re.compile(r"\s*(=|!=|<>|>=|<=|>|<)\s*")  # added <>

col_ref_re = re.compile(r"^([A-Za-z_]\w*)\.([A-Za-z_]\w*)$")

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
    return re.fullmatch(r"[-+]?\d+(\.\d+)?", s) is not None

def parse_predicate(s):
    parts = op_split_re.split(s.strip(), maxsplit=1)
    if len(parts) != 3:
        return None, None, None
    lhs, op, rhs = parts[0].strip(), parts[1], parts[2].strip()
    if op == "<>":  # normalize
        op = "!="
    return lhs, op, rhs

def normalize_ident(ident):
    m = col_ref_re.match(ident)
    if not m:
        return None, None
    return m.group(1), m.group(2)

# quote-aware splitter for AND (case-insensitive), skipping inside single quotes
def split_conjuncts(text):
    parts = []
    i, n = 0, len(text)
    start = 0
    in_str = False
    while i < n:
        ch = text[i]
        if ch == "'":
            if in_str and i + 1 < n and text[i + 1] == "'":  # escaped ''
                i += 2
                continue
            in_str = not in_str
            i += 1
            continue
        if not in_str:
            # check for word 'and' with word boundaries (case-insensitive)
            if i + 3 <= n and text[i:i+3].lower() == "and":
                prev = text[i-1] if i-1 >= 0 else " "
                nxt = text[i+3] if i+3 < n else " "
                if not (prev.isalnum() or prev == "_") and not (nxt.isalnum() or nxt == "_"):
                    parts.append(text[start:i].strip())
                    i += 3
                    start = i
                    continue
        i += 1
    tail = text[start:].strip()
    if tail:
        parts.append(tail)
    return parts

# ----- naming helpers -----

def row_var_for_table(table, existing):
    if table == "lineitem":
        return "rL"
    if table == "orders":
        name = "rO"
    elif table == "customer":
        name = "rC"
    else:
        name = f"r{table[:1].upper()}"
    base = name
    k = 2
    while name in existing.values():
        name = f"{base}{k}"
        k += 1
    return name

def col_suffix(col):
    return col.split("_", 1)[1] if "_" in col else col

def fresh_val_name(base, used_names):
    name = f"v_{base}"
    if name not in used_names:
        return name
    i = 2
    while f"{name}{i}" in used_names:
        i += 1
    return f"{name}{i}"

# ----- IR builders -----

def build_policy_ir(pid, body):
    row_vars = {}           # table -> row_var
    value_for_attr = {}     # "table.col" -> value_var
    used_val_names = set()
    atoms = []              # list of triplets
    guards = []

    def add_atom(kind, a, b):
        atoms.append((kind, a, b))

    def ensure_row(table):
        if table not in row_vars:
            row_vars[table] = row_var_for_table(table, row_vars)
        return row_vars[table]

    def ensure_value_var_for_attr(table, col, preferred=None, force_new=False):
        attr = f"{table}.{col}"
        if not force_new and attr in value_for_attr:
            return value_for_attr[attr]
        base = col_suffix(col)
        name = preferred or fresh_val_name(base, used_val_names)
        used_val_names.add(name)
        value_for_attr[attr] = name
        return name

    row_vars.setdefault("lineitem", "rL")

    # split into atomic preds, AND-aware wrt quotes
    parts = split_conjuncts(body)
    for raw in parts:
        chunk = raw.strip()
        if not chunk:
            continue
        lhs, op, rhs = parse_predicate(chunk)
        if op is None:
            continue

        l_tbl, l_col = normalize_ident(lhs) if not is_literal(lhs) else (None, None)
        r_tbl, r_col = normalize_ident(rhs) if not is_literal(rhs) else (None, None)

        if l_tbl and r_tbl and op == "=":
            rl = ensure_row(l_tbl)
            rr = ensure_row(r_tbl)
            base_l, base_r = col_suffix(l_col), col_suffix(r_col)
            base = base_l if base_l == base_r else f"{base_l}_{base_r}"
            shared = fresh_val_name(base, used_val_names)
            used_val_names.add(shared)
            vl = ensure_value_var_for_attr(l_tbl, l_col, preferred=shared)
            vr = ensure_value_var_for_attr(r_tbl, r_col, preferred=shared)
            add_atom("RV", rl, vl); add_atom("VA", vl, f"{l_tbl}.{l_col}")
            add_atom("RV", rr, vr); add_atom("VA", vr, f"{r_tbl}.{r_col}")
            continue

        left_term = lhs
        right_term = rhs

        if l_tbl:
            rl = ensure_row(l_tbl)
            vl = ensure_value_var_for_attr(l_tbl, l_col)
            add_atom("RV", rl, vl); add_atom("VA", vl, f"{l_tbl}.{l_col}")
            left_term = vl
        if r_tbl:
            rr = ensure_row(r_tbl)
            force_new = bool(l_tbl and (col_suffix(l_col) == col_suffix(r_col)))
            vr = ensure_value_var_for_attr(r_tbl, r_col, force_new=force_new)
            add_atom("RV", rr, vr); add_atom("VA", vr, f"{r_tbl}.{r_col}")
            right_term = vr

        guards.append({"type": "ValGuard", "args": [left_term, op, right_term]})

    seen = set()
    deduped = []
    for a in atoms:
        if a in seen:
            continue
        seen.add(a)
        deduped.append(a)

    rows_list = [rv for t, rv in row_vars.items() if t != "lineitem"]
    vals_used = sorted(set(v for _, v in value_for_attr.items()), key=lambda x: (len(x), x))

    return {
        "id": pid,
        "anchor": {"table": "lineitem", "row": "rL"},
        "vars": {"rows": rows_list, "values": vals_used},
        "atoms": [[a, b, c] for (a, b, c) in deduped],
        "guards": guards
    }

# ----- boolean combination parser -> JSON AST -----

class CombParser:
    def __init__(self, text):
        self.tokens = [t for t in bool_tok_re.split(text) if t and t.strip()]
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def eat(self, tok=None):
        cur = self.peek()
        if tok is None or (cur and cur.lower() == tok):
            self.pos += 1
            return cur
        return None

    def parse(self):
        return self.parse_or()

    def parse_or(self):
        left = self.parse_and()
        while True:
            cur = self.peek()
            if cur and cur.lower() == "or":
                self.eat()
                right = self.parse_and()
                left = {"op": "OR", "args": [left, right]}
            else:
                break
        return left

    def parse_and(self):
        left = self.parse_not()
        while True:
            cur = self.peek()
            if cur and cur.lower() == "and":
                self.eat()
                right = self.parse_not()
                left = {"op": "AND", "args": [left, right]}
            else:
                break
        return left

    def parse_not(self):
        cur = self.peek()
        if cur and cur.lower() == "not":
            self.eat()
            node = self.parse_atom()
            return {"op": "NOT", "args": [node]}
        return self.parse_atom()

    def parse_atom(self):
        cur = self.peek()
        if cur == "(":
            self.eat("(")
            node = self.parse_or()
            self.eat(")")
            return node
        tok = self.eat()
        return {"policy": tok}

# ----- main -----

def main():
    policy_map = read_policies(policies_path)
    combo_text = read_combo(combo_path)

    policies_ir = [build_policy_ir(pid, body) for pid, body in policy_map.items()]
    comb_ast = CombParser(combo_text).parse()

    out = {
        "policies": policies_ir,
        "combination": comb_ast,
        "output": {"want": "l_rows", "format": ["lineitem.l_orderkey", "lineitem.l_linenumber"]}
    }

    with out_path.open("w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    print(f"wrote Path-IR with {len(policies_ir)} policies to {out_path}")

if __name__ == "__main__":
    main()
