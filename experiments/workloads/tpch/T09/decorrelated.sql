SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT o.o_orderdate AS key1 FROM public.orders o WHERE o.o_orderpriority = '1-URGENT' AND o.o_totalprice > 450000) x) b1 ON lineitem.l_receiptdate = b1.key1
WHERE (lineitem.l_shipinstruct = 'DELIVER IN PERSON' OR b1.hit IS NULL);
