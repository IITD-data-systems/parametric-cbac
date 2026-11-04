SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT d.l_orderkey AS key1, d.l_suppkey AS key2, 1 AS hit FROM (SELECT DISTINCT l_orderkey, l_suppkey FROM public.lineitem) d, public.orders o, public.customer c, public.supplier s, public.nation n WHERE c.c_custkey = o.o_custkey AND s.s_nationkey = c.c_nationkey AND n.n_nationkey = c.c_nationkey AND n.n_regionkey = 1 AND d.l_orderkey = o.o_orderkey AND d.l_suppkey = s.s_suppkey) b1 ON lineitem.l_orderkey = b1.key1 AND lineitem.l_suppkey = b1.key2
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ps.ps_partkey AS key1, ps.ps_suppkey AS key2 FROM public.partsupp ps WHERE ps.ps_availqty >= 5000) x) b2 ON lineitem.l_partkey = b2.key1 AND lineitem.l_suppkey = b2.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT p.p_partkey AS key1 FROM public.part p WHERE p.p_brand = 'Brand#12') x) b3 ON lineitem.l_partkey = b3.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT') x) b4 ON lineitem.l_orderkey = b4.key1
WHERE ((b3.hit IS NOT NULL AND b2.hit IS NOT NULL AND b1.hit IS NOT NULL) AND b4.hit IS NOT NULL);
