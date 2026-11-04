SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT d.hadm_id AS key1 FROM public.diagnoses_icd d WHERE ((d.icd_version = 10 AND d.icd_code >= 'F' AND d.icd_code < 'G') OR (d.icd_version = 9 AND d.icd_code >= '29' AND d.icd_code < '32'))) x) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT ie.caregiver_id AS key1, ie.stay_id AS key2 FROM public.inputevents ie) x) b2 ON chartevents.caregiver_id = b2.key1 AND chartevents.stay_id = b2.key2
WHERE (b1.hit IS NULL OR b2.hit IS NOT NULL);
