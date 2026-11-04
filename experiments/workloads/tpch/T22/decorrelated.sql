SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c, public.nation n, public.region r WHERE c.c_custkey = o.o_custkey AND n.n_nationkey = c.c_nationkey AND r.r_regionkey = n.n_regionkey AND r.r_name = 'AMERICA') x) b1 ON lineitem.l_orderkey = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT p.p_partkey AS key1 FROM public.part p WHERE p.p_type = 'ECONOMY ANODIZED STEEL') x) b2 ON lineitem.l_partkey = b2.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c WHERE c.c_custkey = o.o_custkey AND c.c_acctbal < 0) x) b3 ON lineitem.l_orderkey = b3.key1
WHERE ((b2.hit IS NOT NULL AND b1.hit IS NOT NULL) AND b3.hit IS NULL);
