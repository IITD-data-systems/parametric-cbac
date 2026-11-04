SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT d.itemid AS key1 FROM public.d_items d WHERE d.category = 'Respiratory') x) b1 ON chartevents.itemid = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i WHERE i.first_careunit = 'Medical Intensive Care Unit (MICU)') x) b2 ON chartevents.stay_id = b2.key1
WHERE (b2.hit IS NOT NULL AND b1.hit IS NOT NULL);
