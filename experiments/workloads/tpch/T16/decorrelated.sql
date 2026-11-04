SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderdate AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT' AND o.o_totalprice > 450000) x) b1 ON lineitem.l_receiptdate = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderkey AS key1 FROM public.orders o, public.customer c WHERE c.c_custkey = o.o_custkey AND c.c_acctbal < 0) x) b2 ON lineitem.l_orderkey = b2.key1
WHERE (b1.hit IS NULL AND b2.hit IS NULL);
