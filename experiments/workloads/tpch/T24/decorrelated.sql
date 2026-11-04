SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT p.p_partkey AS key1 FROM public.part p) x) b1 ON lineitem.l_partkey = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ps.ps_partkey AS key1, ps.ps_suppkey AS key2 FROM public.partsupp ps) x) b2 ON lineitem.l_partkey = b2.key1 AND lineitem.l_suppkey = b2.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT s.s_suppkey AS key1 FROM public.supplier s, public.nation n WHERE n.n_nationkey = s.s_nationkey AND n.n_regionkey = 3) x) b3 ON lineitem.l_suppkey = b3.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderdate >= '1995-01-01') x) b4 ON lineitem.l_orderkey = b4.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderstatus = 'O') x) b5 ON lineitem.l_orderkey = b5.key1
WHERE (NOT (b4.hit IS NOT NULL AND b3.hit IS NOT NULL AND b2.hit IS NOT NULL AND b1.hit IS NOT NULL) OR b5.hit IS NULL);
