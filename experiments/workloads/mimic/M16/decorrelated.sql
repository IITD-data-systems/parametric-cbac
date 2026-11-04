SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT d.hadm_id AS key1 FROM public.diagnoses_icd d, public.d_icd_diagnoses dd WHERE (d.icd_code = 'A419' OR d.icd_code = '0389' OR d.icd_code = 'R6520' OR d.icd_code = '99592') AND dd.icd_code = d.icd_code AND dd.icd_version = d.icd_version) x) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT d.hadm_id AS key1 FROM public.diagnoses_icd d WHERE d.icd_code = 'Z66') x) b2 ON chartevents.hadm_id = b2.key1
WHERE (b1.hit IS NOT NULL AND b2.hit IS NULL);
