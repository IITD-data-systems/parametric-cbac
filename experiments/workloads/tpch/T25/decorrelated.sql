SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderstatus = 'F') x) b1 ON lineitem.l_orderkey = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT s.s_suppkey AS key1 FROM public.supplier s, public.nation n WHERE n.n_nationkey = s.s_nationkey AND n.n_name = 'SAUDI ARABIA') x) b2 ON lineitem.l_suppkey = b2.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT s.s_suppkey AS key1 FROM public.supplier s WHERE s.s_nationkey = 20) x) b3 ON lineitem.l_suppkey = b3.key1
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ps.ps_partkey AS key1, ps.ps_suppkey AS key2 FROM public.partsupp ps, public.part p WHERE p.p_partkey = ps.ps_partkey AND p.p_size >= 45 AND ps.ps_availqty < 2000) x) b4 ON lineitem.l_partkey = b4.key1 AND lineitem.l_suppkey = b4.key2
WHERE ((b2.hit IS NOT NULL AND b1.hit IS NOT NULL AND COALESCE(lineitem.l_receiptdate > lineitem.l_commitdate, false)) AND NOT (b4.hit IS NOT NULL AND b3.hit IS NOT NULL));
