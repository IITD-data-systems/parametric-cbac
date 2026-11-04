SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT mi.movie_id AS key1 FROM public.movie_info mi WHERE (mi.info = 'Sweden' OR mi.info = 'Norway' OR mi.info = 'Germany' OR mi.info = 'Denmark' OR mi.info = 'Swedish' OR mi.info = 'Denish' OR mi.info = 'Norwegian' OR mi.info = 'German' OR mi.info = 'English')) x) b1 ON title.id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year >= 1950 AND title.production_year <= 2010, false));
