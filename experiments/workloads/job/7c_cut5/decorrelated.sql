SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT ci.movie_id AS key1 FROM public.cast_info ci, public.name n WHERE ci.person_id = n.id AND n.name_pcode_cf >= 'A' AND n.name_pcode_cf <= 'F' INTERSECT SELECT ml.linked_movie_id AS key1 FROM public.link_type lt, public.movie_link ml WHERE lt.id = ml.link_type_id AND (lt.link = 'references' OR lt.link = 'referenced in' OR lt.link = 'features' OR lt.link = 'featured in')) x) b1 ON title.id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year >= 1980 AND title.production_year <= 2010, false));
