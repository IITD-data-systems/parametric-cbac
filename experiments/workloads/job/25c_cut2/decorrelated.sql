SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT mi.movie_id AS key1 FROM public.movie_info mi WHERE (mi.info = 'Horror' OR mi.info = 'Action' OR mi.info = 'Sci-Fi' OR mi.info = 'Thriller' OR mi.info = 'Crime' OR mi.info = 'War')) x) b1 ON title.id = b1.key1
WHERE b1.hit IS NOT NULL;
