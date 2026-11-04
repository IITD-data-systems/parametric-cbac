SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c, public.nation n WHERE c.c_custkey = o.o_custkey AND n.n_nationkey = c.c_nationkey AND n.n_regionkey = 2) x) b1 ON lineitem.l_orderkey = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderstatus = 'F') x) b2 ON lineitem.l_orderkey = b2.key1
WHERE (b1.hit IS NOT NULL AND b2.hit IS NULL);
