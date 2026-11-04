SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT key1, 1 AS hit FROM (SELECT po.hadm_id AS key1 FROM public.poe po WHERE po.order_provider_id = 'P57YCB' INTERSECT SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p WHERE p.subject_id = a.subject_id AND p.anchor_age >= 40) x) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT i.stay_id AS key1 FROM public.icustays i, public.procedureevents pe, public.d_items di WHERE pe.stay_id = i.stay_id AND di.itemid = pe.itemid AND di.label = 'Invasive Ventilation') x) b2 ON chartevents.stay_id = b2.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.diagnoses_icd d WHERE d.hadm_id = a.hadm_id AND d.icd_code = 'Z66') x) b3 ON chartevents.hadm_id = b3.key1
WHERE ((b2.hit IS NOT NULL AND b1.hit IS NOT NULL) AND b3.hit IS NULL);
