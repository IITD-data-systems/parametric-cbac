SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ie.caregiver_id AS key1, ie.stay_id AS key2 FROM public.inputevents ie WHERE ie.itemid = 221906) x) b1 ON chartevents.caregiver_id = b1.key1 AND chartevents.stay_id = b1.key2
WHERE b1.hit IS NOT NULL;
