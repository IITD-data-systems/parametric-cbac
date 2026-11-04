SELECT count(*) FROM public.lineitem lineitem
WHERE (lineitem.l_returnflag = 'R' AND lineitem.l_receiptdate > lineitem.l_commitdate);
