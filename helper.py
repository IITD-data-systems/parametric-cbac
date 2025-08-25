import json
import operator
import numpy as np
from z3 import Not, Implies, Solver,BoolVal,Bool,Or,And,sat
from itertools import count
t_counter = count()

oper = {
    "=":  operator.eq, "==": operator.eq,
    "!=": operator.ne, "<>": operator.ne,
    "<":  operator.lt, "<=": operator.le,
    ">":  operator.gt, ">=": operator.ge,
    "in": "in", "not in": "nin", "nin": "nin",
}
def load_schema(dirpath):
    with open(dirpath / "schema.json", "r") as f:
        return json.load(f)
    
def col_index(schema, name):
    return {c["name"]: i for i, c in enumerate(schema)}[name]

def load_vals(dirpath, col):
    return np.load(dirpath / f"{col}.npy")

def find_code(vals, pred):
    literal, op = pred
    op = op.strip().lower()
    op = oper[op]
    idx = np.flatnonzero(op(vals,literal))
    return idx

def build_gid_maps(vals_a: np.ndarray, vals_b: np.ndarray):
    comb = np.concatenate([vals_a.astype(object), vals_b.astype(object)])
    uniq, inv = np.unique(comb, return_inverse=True)
    gid_a = inv[:len(vals_a)].astype(np.int64)
    gid_b = inv[len(vals_a):].astype(np.int64)
    return gid_a, gid_b, uniq

def edges_from_pairs(src_idx, dst_idx):
    out = np.empty((src_idx.size, 2), dtype=np.int64)
    out[:,0] = src_idx
    out[:,1] = dst_idx
    return out

def report(name, arr):
    print(f"  {name} edges: {arr.shape[0]}")
    
def find_codes(vals, pred):

    lit, op = pred
    op = op.strip().lower()

    op = oper[op]
    return(np.flatnonzero(op(vals,lit)))

def bin_by_signature(sig_arr):
    classes, inv = np.unique(sig_arr, return_inverse=True)
    buckets = {int(cls): np.flatnonzero(inv == i) for i, cls in enumerate(classes)}
    return classes, buckets

def X(i):  return ('X', int(i))
def AndN(*nodes): return ('and', list(nodes))
def OrN(*nodes):  return ('or', list(nodes))

def bit_of(p, i):
    return BoolVal( ((p >> (i-1)) & 1) == 1 )

def create_constraint(p, node, solver):
    kind = node[0] if isinstance(node, tuple) else ('X' if isinstance(node, int) else None)

    if kind == 'X':
        i = node[1] if isinstance(node, tuple) else int(node)
        return bit_of(p, i)

    if kind == 'and':
        children = node[1]
        compiled = [create_constraint(p, ch, solver) for ch in children]
        t = Bool(f"t_and_p{p}_{next(t_counter)}")
        for a in compiled:
            solver.add(Implies(t, a))
        solver.add(Or(t, *[Not(a) for a in compiled]))
        return t

    if kind == 'or':
        children = node[1]
        compiled = [create_constraint(p, ch, solver) for ch in children]
        return Or(*compiled) if compiled else BoolVal(False)

