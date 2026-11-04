SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT d.charttime AS key1, d.stay_id AS key2, 1 AS hit FROM (SELECT DISTINCT charttime, stay_id FROM public.chartevents) d, public.icustays i, public.transfers t WHERE t.hadm_id = i.hadm_id AND t.careunit = i.first_careunit AND d.charttime >= t.intime AND d.charttime <= t.outtime AND d.stay_id = i.stay_id) b1 ON chartevents.charttime = b1.key1 AND chartevents.stay_id = b1.key2
WHERE b1.hit IS NOT NULL;
