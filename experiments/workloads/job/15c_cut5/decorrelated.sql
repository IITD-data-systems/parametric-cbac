SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT mc.movie_id AS key1 FROM public.company_name cn, public.movie_companies mc WHERE cn.id = mc.company_id AND cn.country_code = '[us]' INTERSECT SELECT mi.movie_id AS key1 FROM public.info_type it1, public.movie_info mi WHERE it1.id = mi.info_type_id AND it1.info = 'release dates') x) b1 ON title.id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year > 1990, false));
