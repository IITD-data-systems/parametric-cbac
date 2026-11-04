SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a WHERE a.hospital_expire_flag = 1) x) b1 ON chartevents.hadm_id = b1.key1
WHERE (chartevents.warning = 1 OR b1.hit IS NULL);
