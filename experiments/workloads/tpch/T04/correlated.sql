SELECT count(*) FROM public.lineitem lineitem WHERE EXISTS (SELECT 1 FROM public.orders o WHERE o.o_orderkey = lineitem.l_orderkey AND o.o_orderpriority = '1-URGENT');
