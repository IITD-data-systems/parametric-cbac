SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ie.caregiver_id AS key1, ie.stay_id AS key2 FROM public.inputevents ie, public.d_items d WHERE d.itemid = ie.itemid AND d.category = 'Antibiotics') x) b1 ON chartevents.caregiver_id = b1.key1 AND chartevents.stay_id = b1.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT ie.stay_id AS key1 FROM public.inputevents ie WHERE ie.itemid = 222168) x) b2 ON chartevents.stay_id = b2.key1
WHERE (b1.hit IS NOT NULL AND b2.hit IS NULL);
