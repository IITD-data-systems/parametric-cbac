SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT max(s.s_acctbal) AS agg FROM public.supplier s WHERE s.s_nationkey = 7) b1 ON true
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c WHERE c.c_custkey = o.o_custkey AND c.c_acctbal < 0) x) b2 ON lineitem.l_orderkey = b2.key1
WHERE (COALESCE(lineitem.l_extendedprice <= b1.agg, false) OR b2.hit IS NULL);
