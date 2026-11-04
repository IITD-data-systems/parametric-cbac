SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c, public.nation n, public.region r WHERE c.c_custkey = o.o_custkey AND n.n_nationkey = c.c_nationkey AND r.r_regionkey = n.n_regionkey AND r.r_name = 'AFRICA') x) b1 ON lineitem.l_orderkey = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderdate AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT' AND o.o_totalprice > 450000) x) b2 ON lineitem.l_shipdate = b2.key1
WHERE (b1.hit IS NOT NULL OR b2.hit IS NULL);
