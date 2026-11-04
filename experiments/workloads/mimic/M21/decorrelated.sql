SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i, public.admissions a, public.patients p, public.diagnoses_icd d, public.d_icd_diagnoses dd WHERE a.hadm_id = i.hadm_id AND p.subject_id = a.subject_id AND p.anchor_age >= 50 AND d.hadm_id = a.hadm_id AND d.icd_code = 'N179' AND dd.icd_code = d.icd_code AND dd.icd_version = d.icd_version) x) b1 ON chartevents.stay_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT di.itemid AS key1 FROM public.d_items di WHERE di.category = 'Routine Vital Signs') x) b2 ON chartevents.itemid = b2.key1
WHERE (b1.hit IS NOT NULL AND b2.hit IS NOT NULL);
