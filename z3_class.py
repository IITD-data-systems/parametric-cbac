import json
import time
from pathlib import Path
import numpy as np

from z3 import Solver,Or,And, Bool, BoolVal, sat


t1 = time.time()
tables = Path("tables")

lineitem = tables/"lineitem"
orders = tables/"orders"

l_ok = "l_orderkey"
l_ln = "l_linenumber"
o_ok = "o_orderkey"
o_st = "o_orderstatus"

o_status = "O"



output = Path("result.txt")


def load_schema(dir):
    with open(dir/"schema.json","r") as f:
        return json.load(f)

l_sch = load_schema(lineitem)
o_sch = load_schema(orders)

def col_indx(schema,name):
    mp ={j["name"]: i for i, j in enumerate(schema)}
    return mp[name]

i_l_ok = col_indx(l_sch,l_ok)
i_l_ln = col_indx(l_sch,l_ln)
i_o_ok = col_indx(o_sch,o_ok)
i_o_st = col_indx(o_sch,o_st)

def load_values(dir,col):
    return np.load(dir/f"{col}.npy")

l_ok_val = load_values(lineitem,l_ok)
l_ln_val = load_values(lineitem,l_ln)
o_ok_val = load_values(orders,o_ok)
o_st_val = load_values(orders,o_st)

o_status_pos = None
for i, v in enumerate(o_st_val):
    if v == o_status:
        o_status_pos = i
        break
map_l = np.load(lineitem/"codes.npy", mmap_mode="r")[:,[i_l_ok,i_l_ln]]
map_o = np.load(orders/"codes.npy", mmap_mode="r")[:,[i_o_ok,i_o_st]]
nL, nO = map_l.shape[0], map_o.shape[0]
t2 = time.time()

print(f"Data loaded = {(t2-t1):.4f} secs")

o_ok_col= map_o[:,0].astype(np.int64)
# print(o_ok_col)
o_st_col= map_o[:,1].astype(np.int64)
# print(len(set(o_st_col)))

l_ok_col = map_l[:,0].astype(np.int64)
l_ln_col = map_l[:,1].astype(np.int64)

value_to_id = {}

l_col_to_id = np.empty(l_ok_val.shape[0], dtype=np.int64)
o_col_to_id = np.empty(o_ok_val.shape[0],dtype= np.int64)

for i, v in enumerate(l_ok_val):
    pv = v
    id = value_to_id.get(pv)
    if id is None:
        id = len(value_to_id)
        value_to_id[pv] = id
    l_col_to_id[i] = id
    
for i, v in enumerate(o_ok_val):
    pv = v
    id = value_to_id.get(pv)
    if id is None:
        id = len(value_to_id)
        value_to_id[pv] = id
    o_col_to_id[i] = id

# print(l_col_to_id)
# print(o_col_to_id)
n_ok = len(value_to_id)

# print(n_ok)

l_ok_id = l_col_to_id[l_ok_col]
o_ok_id = o_col_to_id[o_ok_col]

# print(len(l_ok_id))
# print(len(o_ok_id))

l_bit = np.zeros(n_ok,dtype=bool)
o_bit = np.zeros(n_ok,dtype=bool)



if l_ok_id.size:
    l_bit[l_ok_id]= True


if o_ok_id.size:
    mask = (o_st_col == o_status_pos)
    o_bit [o_ok_id[mask]] = True

# print(int(l_bit.sum()))
# print(int(o_bit.sum()))

sig_ok = (l_bit.astype(np.uint8)+ (o_bit.astype(np.int8) << 1))
# print(len(sig_ok))
pat_counts = np.bincount(sig_ok, minlength=4)
# print(pat_counts)
t3 = time.time()

print(f"Materializing and classifying edges {(t3-t2):.4f} seconds")

s_vars = [Bool(f"s_{p:02b}") for p in range(4)]
# print(s_vars)
exists_p = [BoolVal(pat_counts[p] > 0) for p in range(4)]
# print(exists_p)
condition_p = [And(BoolVal((p&1)!=0), BoolVal((p&2)!=0)) for p in range(4)]

# print(condition_p)

solver = Solver()
# print(solver)
for p in range(4):
    solver.add(s_vars[p] == And(exists_p[p], condition_p[p]))
# print(solver)
solver.add(Or(*s_vars))

# print(solver)

res = solver.check()

# print(res)

m = solver.model()

# print(m)

t4 = time.time()
print(f"Z3 solving in {(t4-t3):.4f} seconds")


selected_ps = [p for p in range(4) if m.eval(s_vars[p], model_completion=True) == BoolVal(True)]

# print(selected_ps)

selected_mask_by_p = np.zeros(4, dtype=bool)
for p in selected_ps:
    selected_mask_by_p[p] = True

# print(selected_mask_by_p)

row_sig_p = sig_ok[l_ok_id]
keep = selected_mask_by_p[row_sig_p]
sel_idx = np.flatnonzero(keep)
# print(len(sel_idx))

t5 = time.time()

print(f"getting l_rows in {(t5-t4):.4f} seconds")
print(f"Total time to solve {(t5-t1):.4f} seconds")

sel_ok_codes = l_ok_col[sel_idx]  
sel_ln_codes = l_ln_col[sel_idx]  
sel_ok_vals  = l_ok_val[sel_ok_codes]
sel_ln_vals  = l_ln_val[sel_ln_codes]


with open(output, "w") as f:
    for okv, lnv in zip(sel_ok_vals, sel_ln_vals):
        f.write(f"{okv},{lnv}\n")
        