SELECT count(*) FROM public.title title
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT kt.id AS key1 FROM public.kind_type kt WHERE (kt.kind = 'movie' OR kt.kind = 'tv movie' OR kt.kind = 'video movie' OR kt.kind = 'video game')) x) b1 ON title.kind_id = b1.key1
WHERE (b1.hit IS NOT NULL AND COALESCE(title.production_year > 1990, false));
