SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT l.charttime AS key1, l.subject_id AS key2 FROM public.labevents l, public.d_labitems dl WHERE dl.itemid = l.itemid AND dl.category = 'Blood Gas') x) b1 ON chartevents.charttime = b1.key1 AND chartevents.subject_id = b1.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a WHERE a.hospital_expire_flag = 1) x) b2 ON chartevents.hadm_id = b2.key1
WHERE (b1.hit IS NULL AND b2.hit IS NULL);
