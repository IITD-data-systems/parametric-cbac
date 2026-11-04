SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT mi.movie_id AS key1 FROM public.info_type it1, public.movie_info mi WHERE it1.id = mi.info_type_id AND it1.info = 'genres' AND (mi.info = 'Horror' OR mi.info = 'Action' OR mi.info = 'Sci-Fi' OR mi.info = 'Thriller' OR mi.info = 'Crime' OR mi.info = 'War') INTERSECT SELECT mi_idx.movie_id AS key1 FROM public.info_type it2, public.movie_info_idx mi_idx WHERE it2.id = mi_idx.info_type_id AND it2.info = 'votes') x) b1 ON title.id = b1.key1
WHERE b1.hit IS NOT NULL;
