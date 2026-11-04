SELECT count(*) FROM public.lineitem lineitem WHERE EXISTS (SELECT 1 FROM public.part p WHERE p.p_partkey = lineitem.l_partkey AND p.p_brand = 'Brand#23' AND p.p_container = 'MED BOX');
