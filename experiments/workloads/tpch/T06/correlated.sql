SELECT count(*) FROM public.lineitem lineitem WHERE l_returnflag = 'N' AND NOT EXISTS (SELECT 1 FROM public.orders o WHERE o.o_orderkey = lineitem.l_orderkey AND o.o_orderstatus = 'O');
