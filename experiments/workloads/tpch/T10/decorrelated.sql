SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT p.p_partkey AS key1 FROM public.part p WHERE p.p_brand = 'Brand#23' AND p.p_container = 'MED BOX') x) b1 ON lineitem.l_partkey = b1.key1
WHERE b1.hit IS NOT NULL;
