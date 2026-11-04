SELECT count(*) FROM public.lineitem lineitem
WHERE (lineitem.l_discount >= 0.09 AND lineitem.l_quantity >= 45);
