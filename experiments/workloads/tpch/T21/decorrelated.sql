SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT d.l_orderkey AS key1, d.l_suppkey AS key2, 1 AS hit FROM (SELECT DISTINCT l_orderkey, l_suppkey FROM public.lineitem) d, public.orders o, public.customer c, public.supplier s, public.nation n, public.region r WHERE c.c_custkey = o.o_custkey AND s.s_nationkey = c.c_nationkey AND n.n_nationkey = s.s_nationkey AND r.r_regionkey = n.n_regionkey AND r.r_name = 'ASIA' AND d.l_orderkey = o.o_orderkey AND d.l_suppkey = s.s_suppkey) b1 ON lineitem.l_orderkey = b1.key1 AND lineitem.l_suppkey = b1.key2
WHERE b1.hit IS NOT NULL;
