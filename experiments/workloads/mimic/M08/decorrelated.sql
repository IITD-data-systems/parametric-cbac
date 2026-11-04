SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT d.charttime AS key1, d.stay_id AS key2, 1 AS hit FROM (SELECT DISTINCT charttime, stay_id FROM public.chartevents) d, public.procedureevents pe WHERE pe.itemid = 225792 AND d.charttime >= pe.starttime AND d.charttime <= pe.endtime AND d.stay_id = pe.stay_id) b1 ON chartevents.charttime = b1.key1 AND chartevents.stay_id = b1.key2
WHERE (chartevents.valueuom = 'insp/min' AND b1.hit IS NOT NULL);
