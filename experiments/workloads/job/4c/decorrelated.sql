SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT mi_idx.movie_id AS key1 FROM public.info_type it, public.movie_info_idx mi_idx WHERE it.id = mi_idx.info_type_id AND it.info = 'rating' INTERSECT SELECT mk.movie_id AS key1 FROM public.keyword k, public.movie_keyword mk WHERE k.id = mk.keyword_id) x) b1 ON title.id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year > 1990, false));
