SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT d.l_orderkey AS key1, d.l_suppkey AS key2, 1 AS hit FROM (SELECT DISTINCT l_orderkey, l_suppkey FROM public.lineitem) d, public.orders o, public.customer c, public.supplier s WHERE c.c_custkey = o.o_custkey AND s.s_nationkey = c.c_nationkey AND d.l_orderkey = o.o_orderkey AND d.l_suppkey = s.s_suppkey) b1 ON lineitem.l_orderkey = b1.key1 AND lineitem.l_suppkey = b1.key2
  LEFT JOIN (SELECT ps.ps_partkey AS key1, ps.ps_suppkey AS key2, min(ps.ps_availqty) AS agg FROM public.partsupp ps GROUP BY ps.ps_partkey, ps.ps_suppkey) b2 ON lineitem.l_partkey = b2.key1 AND lineitem.l_suppkey = b2.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c WHERE c.c_custkey = o.o_custkey AND c.c_acctbal < 0) x) b3 ON lineitem.l_orderkey = b3.key1
WHERE (b1.hit IS NOT NULL AND NOT COALESCE(lineitem.l_quantity > b2.agg, false) AND b3.hit IS NULL);
