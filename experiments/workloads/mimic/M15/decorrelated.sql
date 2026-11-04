SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT ie.stay_id AS key1 FROM public.inputevents ie WHERE ie.itemid = 221906) x) b1 ON chartevents.stay_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT pe.stay_id AS key1 FROM public.procedureevents pe WHERE pe.itemid = 225792) x) b2 ON chartevents.stay_id = b2.key1
WHERE (b1.hit IS NOT NULL OR b2.hit IS NOT NULL);
