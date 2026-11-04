SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT mc.movie_id AS key1 FROM public.company_name cn, public.movie_companies mc WHERE cn.id = mc.company_id AND cn.country_code = '[us]' INTERSECT SELECT mk.movie_id AS key1 FROM public.keyword k, public.movie_keyword mk WHERE mk.keyword_id = k.id AND k.keyword = 'character-name-in-title') x) b1 ON title.id = b1.key1
WHERE b1.hit IS NOT NULL;
