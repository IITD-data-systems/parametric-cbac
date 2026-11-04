SELECT count(*) FROM public.title title WHERE EXISTS (SELECT 1 FROM public.kind_type kt WHERE kt.id = title.kind_id AND (kt.kind = 'movie' OR kt.kind = 'episode') AND title.production_year > 2005);
