SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT mi.movie_id AS key1 FROM public.movie_info mi WHERE (mi.info = 'Drama' OR mi.info = 'Horror' OR mi.info = 'Western' OR mi.info = 'Family')) x) b1 ON title.id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year >= 2000 AND title.production_year <= 2010, false));
