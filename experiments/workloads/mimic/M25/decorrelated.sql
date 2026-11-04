SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT l.charttime AS key1, l.subject_id AS key2 FROM public.labevents l, public.d_labitems dl WHERE dl.itemid = l.itemid AND dl.label = 'Potassium' AND dl.fluid = 'Blood' AND l.flag = 'abnormal') x) b1 ON chartevents.charttime = b1.key1 AND chartevents.subject_id = b1.key2
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p WHERE p.subject_id = a.subject_id AND p.anchor_age >= 65) x) b2 ON chartevents.hadm_id = b2.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i) x) b3 ON chartevents.stay_id = b3.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p WHERE p.subject_id = a.subject_id AND p.anchor_age >= 65) x) b4 ON chartevents.hadm_id = b4.key1
WHERE ((b3.hit IS NOT NULL AND b2.hit IS NOT NULL AND b1.hit IS NOT NULL) OR b4.hit IS NULL);
