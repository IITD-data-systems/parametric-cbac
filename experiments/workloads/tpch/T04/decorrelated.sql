SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT') x) b1 ON lineitem.l_orderkey = b1.key1
WHERE b1.hit IS NOT NULL;
