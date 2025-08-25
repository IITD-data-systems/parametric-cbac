"""
policy = l_orderkry = o_orderkey and o_orderstatus = "O" and/or o_total_price < 40000
"""

import time
from pathlib import Path
import numpy as np
from helper import load_schema, col_index, load_vals, find_code,build_gid_maps, edges_from_pairs,find_codes,report,bin_by_signature, X, AndN, OrN, bit_of,create_constraint
from z3 import Not, Implies, Solver,BoolVal,Bool,Or,And,sat
from itertools import count

t0 = time.time()

tables   = Path("tables")
lineitem = tables / "lineitem"
orders   = tables / "orders"

l_ok , l_ln = "l_orderkey", "l_linenumber"
o_ok , o_st, o_tp = "o_orderkey", "o_orderstatus","o_totalprice"

o_pred_1 = ("O","=")
o_pred_2 = (40000,"<")

l_sch = load_schema(lineitem)
o_sch = load_schema(orders)

i_l_ok = col_index(l_sch, l_ok)
i_l_ln = col_index(l_sch, l_ln)

i_o_ok = col_index(o_sch, o_ok)
i_o_tp = col_index(o_sch, o_tp)
i_o_st = col_index(o_sch, o_st)

print(f"  L: ok={i_l_ok}, ln={i_l_ln}")
print(f"  O: ok={i_o_ok}, tp={i_o_tp}, st={i_o_st}")

l_ok_val = load_vals(lineitem, l_ok)         
l_ln_val = load_vals(lineitem, l_ln)         

o_ok_val = load_vals(orders,   o_ok)
o_tp_val = load_vals(orders,   o_tp)
o_st_val = load_vals(orders,   o_st)

code_st = find_code(o_st_val,o_pred_1)
code_tp = find_code(o_tp_val,o_pred_2)
print(f"  code('O') in o_status: {code_st}")
print(f"  code(<40000) in o_totalprice: {code_tp}")

map_l = np.load(lineitem / "codes.npy")[:, [i_l_ok, i_l_ln]]
map_o = np.load(orders   / "codes.npy")[:, [i_o_ok, i_o_tp, i_o_st]]

nL, nO = map_l.shape[0], map_o.shape[0]
print(f"  rows: lineitem={nL:,}, orders={nO:,}")

l_ok_code = map_l[:,0]
l_ln_code = map_l[:,1]

o_ok_code = map_o[:,0]
o_tp_code = map_o[:,1]
o_st_code = map_o[:,2]

t1=time.time()
print(f"Data loaded. {(t1-t0):.4f} seconds")

ok_gid_of_lval, ok_gid_of_oval, ok_universe = build_gid_maps(l_ok_val, o_ok_val)

l_ok_gid  = ok_gid_of_lval[l_ok_code]
o_ok_gid  = ok_gid_of_oval[o_ok_code]
n_ok_gid = int(len(ok_universe))
a_ok = 0
a_st = 1
a_tp = 2

E1 = edges_from_pairs(np.arange(nL), l_ok_gid)

E2 = edges_from_pairs(np.arange(n_ok_gid),np.full(n_ok_gid, a_ok))
E3 = edges_from_pairs(np.arange(nO, dtype=np.int64), o_ok_gid)
mask_O1 = (o_st_code == code_st)
E4 = edges_from_pairs(np.flatnonzero(mask_O1),np.full(int(np.count_nonzero(mask_O1)), code_st))
E5 = edges_from_pairs(np.array([code_st]),np.array([a_st]))
mask_O2 = np.isin(o_tp_code, code_tp)
E6 = edges_from_pairs(np.flatnonzero(mask_O2),o_tp_code[mask_O2])
E7 = edges_from_pairs(np.array([code_tp]),np.array([a_tp]))

report("E1  (L -> ok)",            E1)
report("E2  (ok -> orderkey)",     E2)
report("E3  (O ->  ok)",            E3)
report("E4  (O -> 'O')",           E4)
report("E5  ('O' -> o_status)",    E5)
report("E6  (O -> tp)",            E6)
report("E7  (tp -> o_totalprice)",      E7)

t1=time.time()
print(f"Edges created. {(t1-t0):.4f} seconds")

has_E5 = bool(E5.size)
has_E7 = bool(E7.size)

ok_has_E1 = np.zeros(nO, dtype=bool)  
ok_has_E2 = np.zeros(nO, dtype=bool) 
ok_has_E3 = np.zeros(nO, dtype=bool) 

if E1.size:
    ok_has_E1[E1[:,1]] = True
if E2.size:
    ok_has_E2[E2[:,0]] = True
if E3.size:
    ok_has_E3[E3[:,1]] = True
    
o_has_O   = np.zeros(nO, dtype=bool)         
o_has_ok  = np.zeros(nO, dtype=bool)          
o_ok_tok  = np.full(nO, -1, dtype=np.int64)  
o_has_tp  = np.zeros(nO, dtype=bool)          
o_tp_tok  = np.full(nO, -1, dtype=np.int64)
ok_has_O    = np.zeros(nO, dtype=bool)  
ok_has_tp   = np.zeros(nO, dtype=bool)

if E4.size:
    o_has_O[E4[:,0]] = True
if E3.size:
    o_has_ok[E3[:,0]] = True
    o_ok_tok[E3[:,0]] = E3[:,1]
if E6.size:
    o_has_tp[E6[:,0]] = True
    o_tp_tok[E6[:,0]] = E6[:,1]

if nO:
    rows_ok = np.flatnonzero(o_has_ok)
    if rows_ok.size:
        v_ok = o_ok_tok[rows_ok]
        ok_has_O[v_ok[o_has_O[rows_ok]]] = True
        ok_has_tp[v_ok[o_has_tp[rows_ok]]] = True

exists_Orow_with_O_and_ok = bool(np.any(o_has_O & o_has_ok))
exists_Orow_with_tp_and_ok = bool(np.any(o_has_tp & o_has_ok))

exists_Orow_O_with_L = False
if np.any(o_has_O & o_has_ok):
    rows = np.flatnonzero(o_has_O & o_has_ok)
    if rows.size:
        exists_Orow_O_with_L = bool(np.any(ok_has_E1[o_ok_tok[rows]]))
exists_Orow_tp_with_L = False
if np.any(o_has_tp & o_has_ok):
    rows = np.flatnonzero(o_has_tp & o_has_ok)
    if rows.size:
        exists_Orow_tp_with_L = bool(np.any(ok_has_E1[o_ok_tok[rows]]))
        

def pack_bits(b1,b2,b3,b4,b5,b6,b7):
    return (b1.astype(np.uint16)
         | (b2.astype(np.uint16)  << 1)
         | (b3.astype(np.uint16)  << 2)
         | (b4.astype(np.uint16)  << 3)
         | (b5.astype(np.uint16)  << 4)
         | (b6.astype(np.uint16)  << 5)
         | (b7.astype(np.uint16)  << 6))
    
signatures = {}   
bins       = {}
if E1.size:
    v = E1[:,1]
    b1  = np.ones(E1.shape[0], dtype=bool)
    b2  = ok_has_E2[v]
    b3  = ok_has_E3[v]
    b4  = ok_has_O[v]
    b5  = b4 & has_E5
    b6  = ok_has_tp[v]
    b7  = b6 & has_E7
    sig_E1 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E1'] = sig_E1
    
if E2.size:
    v = E2[:,0]
    b1  = ok_has_E1[v]
    b2  = np.ones(E2.shape[0], dtype=bool)
    b3  = ok_has_E3[v]
    b4  = ok_has_O[v]
    b5  = b4 & has_E5
    b6  = ok_has_tp[v]
    b7  = b6 & has_E7
    sig_E2 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E2'] = sig_E2

if E3.size:
    r = E3[:,0]
    v = E3[:,1]
    b1  = ok_has_E1[v]
    b2  = ok_has_E2[v]
    b3  = np.ones(E3.shape[0], dtype=bool)
    b4  = o_has_O[r]
    b5  = b4 & has_E5
    b6  = ok_has_tp[v]
    b7  = b6 & has_E7
    sig_E3 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E3'] = sig_E3
    
if E4.size:
    r = E4[:,0]
    v_r = o_ok_tok[r]
    has_v = (v_r >= 0)
    b1  = np.zeros(E4.shape[0], dtype=bool); b1[has_v]  = ok_has_E1[v_r[has_v]]
    b2  = np.zeros(E4.shape[0], dtype=bool); b2[has_v]  = ok_has_E2[v_r[has_v]]
    b3  = o_has_ok[r]
    b4  = np.ones(E4.shape[0], dtype=bool)
    b5  = np.ones(E4.shape[0], dtype=bool) & has_E5
    b6  = np.ones(E4.shape[0], dtype=bool)
    b7  = np.ones(E4.shape[0], dtype=bool) & has_E7
    sig_E4 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E4'] = sig_E4
    
if E5.size:
    m = E5.shape[0]
    b1  = np.full(m, exists_Orow_O_with_L, dtype=bool)
    b2  = np.full(m, exists_Orow_with_O_and_ok, dtype=bool) & has_E5
    b3  = np.full(m, exists_Orow_with_O_and_ok, dtype=bool)
    b4  = np.ones(m, dtype=bool)
    b5  = np.ones(m, dtype=bool) & has_E5
    b6  = np.ones(m, dtype=bool)
    b7  = np.ones(m, dtype=bool) & has_E7
    
    sig_E5 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E5'] = sig_E5


if E6.size:
    r = E6[:,0]
    v_r = o_ok_tok[r]
    has_v = (v_r >= 0)
    b1  = np.zeros(E6.shape[0], dtype=bool); b1[has_v]  = ok_has_E1[v_r[has_v]]
    b2  = np.zeros(E6.shape[0], dtype=bool); b2[has_v]  = ok_has_E2[v_r[has_v]]
    b3  = o_has_ok[r]
    b4  = np.ones(E6.shape[0], dtype=bool)
    b5  = np.ones(E6.shape[0], dtype=bool) & has_E5
    b6  = np.ones(E6.shape[0], dtype=bool)
    b7  = np.ones(E6.shape[0], dtype=bool) & has_E7
    sig_E6 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E6'] = sig_E6
    
if E7.size:
    m = E5.shape[0]
    b1  = np.full(m, exists_Orow_tp_with_L, dtype=bool)
    b2  = np.full(m, exists_Orow_with_tp_and_ok, dtype=bool) & has_E5
    b3  = np.full(m, exists_Orow_with_tp_and_ok, dtype=bool)
    b4  = np.ones(m, dtype=bool)
    b5  = np.ones(m, dtype=bool) & has_E5
    b6  = np.ones(m, dtype=bool)
    b7  = np.ones(m, dtype=bool) & has_E7
    
    sig_E5 = pack_bits(b1,b2,b3,b4,b5,b6,b7)
    signatures['E5'] = sig_E5
    
bins = {} 
for fam, sig in signatures.items():
    classes, buckets = bin_by_signature(sig)
    bins[fam] = buckets
    # print(f"[{fam}] nonempty classes: {classes.size}")
    # for cls in classes:
    #     print(f"  class {cls:04d} bits {cls:010b} -> {buckets[int(cls)].size} edges")
        
t1=time.time()
print(f"Edge classified, signatured and binned. {(t1-t0):.4f} seconds")
        
exists_p = np.zeros(1024, dtype=bool)
for sig in signatures.values():
    if sig.size:
        cls = np.unique(sig)
        exists_p[cls] = True
allowed_classes = np.flatnonzero(exists_p).tolist()

policy = AndN(AndN(X(1),X(2),X(3),X(4),X(5)),AndN(X(1),X(2),X(3),X(6),X(7)))

t_counter = count()

solver = Solver()

s_Xs = {}

for p in allowed_classes:
    Gp = create_constraint(p, policy, solver)  
    s = Bool(f"s_{p:04d}")
    s_Xs[p] = s
    solver.add(s == And(BoolVal(True), Gp))  

res = solver.check()
if res != sat:
    print("no signature class satisfies the policy")
    selected_classes = []
else:
    m = solver.model()
    selected_classes = [p for p in allowed_classes if m.eval(s_Xs[p], model_completion=True) == BoolVal(True)]
print(f"selected signature classes: {len(selected_classes)}, {selected_classes}")

t1=time.time()
print(f"SAT solved the policy. {(t1-t0):.4f} seconds")


output = Path("result.txt")
sel_e1_chunks = []
for p in selected_classes:
    bucket = bins.get('E1', {}).get(p, None)
    if bucket is not None and bucket.size:
        sel_e1_chunks.append(bucket)



sel_e1_idx = np.concatenate(sel_e1_chunks)

try:
    sel_l_rows = E1_src_rows[sel_e1_idx]
except NameError:
    sel_l_rows = sel_e1_idx


sel_l_rows = np.unique(sel_l_rows)

sel_ok_codes = l_ok_code[sel_l_rows]
sel_ln_codes = l_ln_code[sel_l_rows]
sel_ok_vals  = l_ok_val[sel_ok_codes]
sel_ln_vals  = l_ln_val[sel_ln_codes]

with open(output, "w") as f:
    for okv, lnv in zip(sel_ok_vals, sel_ln_vals):
        f.write(f"{okv},{lnv}\n")

t1=time.time()
print(f"Wrote the result. {(t1-t0):.4f} seconds")