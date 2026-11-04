SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i, public.admissions a WHERE a.hadm_id = i.hadm_id AND a.insurance = 'Medicaid') x) b1 ON chartevents.stay_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i WHERE i.first_careunit = 'Medical Intensive Care Unit (MICU)') x) b2 ON chartevents.stay_id = b2.key1
WHERE (b1.hit IS NOT NULL AND b2.hit IS NOT NULL);
