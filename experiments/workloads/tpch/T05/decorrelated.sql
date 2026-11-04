SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ps.ps_partkey AS key1, ps.ps_suppkey AS key2 FROM public.partsupp ps WHERE ps.ps_availqty < 3000) x) b1 ON lineitem.l_partkey = b1.key1 AND lineitem.l_suppkey = b1.key2
WHERE b1.hit IS NULL;
