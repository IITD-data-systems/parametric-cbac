SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p, public.diagnoses_icd d, public.d_icd_diagnoses dd WHERE p.subject_id = a.subject_id AND p.anchor_age >= 50 AND d.hadm_id = a.hadm_id AND d.icd_code = 'N179' AND dd.icd_code = d.icd_code AND dd.icd_version = d.icd_version) x) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.drgcodes g WHERE g.hadm_id = a.hadm_id AND g.drg_type = 'APR' AND g.drg_severity >= 4) x) b2 ON chartevents.hadm_id = b2.key1
WHERE (b1.hit IS NULL AND b2.hit IS NULL);
