SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p WHERE p.subject_id = a.subject_id AND p.anchor_age >= 75) x) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a WHERE a.hospital_expire_flag = 1) x) b2 ON chartevents.hadm_id = b2.key1
WHERE (b1.hit IS NULL OR b2.hit IS NULL);
