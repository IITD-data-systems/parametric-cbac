SELECT count(*) FROM public.lineitem lineitem WHERE l_returnflag = 'R' AND l_receiptdate > l_commitdate;
