SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT mc.movie_id AS key1 FROM public.company_type ct, public.movie_companies mc WHERE ct.id = mc.company_type_id AND ct.kind = 'production companies' INTERSECT SELECT mi_idx.movie_id AS key1 FROM public.info_type it, public.movie_info_idx mi_idx WHERE it.id = mi_idx.info_type_id AND it.info = 'top 250 rank') x) b1 ON title.id = b1.key1
WHERE b1.hit IS NOT NULL;
