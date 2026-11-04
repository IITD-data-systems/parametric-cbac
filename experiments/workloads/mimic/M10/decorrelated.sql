SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT d.charttime AS key1, d.stay_id AS key2, 1 AS hit FROM (SELECT DISTINCT charttime, stay_id FROM public.chartevents) d, public.inputevents ie WHERE ie.itemid = 222168 AND d.charttime >= ie.starttime AND d.charttime <= ie.endtime AND d.stay_id = ie.stay_id) b1 ON chartevents.charttime = b1.key1 AND chartevents.stay_id = b1.key2
WHERE b1.hit IS NULL;
