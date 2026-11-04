SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderdate AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT' AND o.o_totalprice > 450000) x) b1 ON lineitem.l_shipdate = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT s.s_suppkey AS key1 FROM public.supplier s, public.nation n WHERE n.n_nationkey = s.s_nationkey AND n.n_name = 'JAPAN') x) b2 ON lineitem.l_suppkey = b2.key1
WHERE (b1.hit IS NOT NULL OR b2.hit IS NOT NULL);
