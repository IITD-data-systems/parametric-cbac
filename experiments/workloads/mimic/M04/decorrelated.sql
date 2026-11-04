SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT d.itemid AS key1 FROM public.d_items d WHERE d.category = 'Routine Vital Signs') x) b1 ON chartevents.itemid = b1.key1
WHERE (chartevents.warning = 1 OR b1.hit IS NOT NULL);
