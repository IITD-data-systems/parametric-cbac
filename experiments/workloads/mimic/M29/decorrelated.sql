SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT rx.hadm_id AS key1, min(e.charttime) AS agg FROM public.prescriptions rx, public.pharmacy ph, public.emar e WHERE rx.drug = 'Potassium Chloride' AND ph.pharmacy_id = rx.pharmacy_id AND e.pharmacy_id = ph.pharmacy_id AND e.event_txt = 'Administered' GROUP BY rx.hadm_id) b1 ON chartevents.hadm_id = b1.key1
  LEFT JOIN (SELECT DISTINCT key1, 1 AS hit FROM (SELECT a.hadm_id AS key1 FROM public.admissions a, public.patients p WHERE p.subject_id = a.subject_id AND p.anchor_age >= 40) x) b2 ON chartevents.hadm_id = b2.key1
WHERE (NOT COALESCE(chartevents.charttime >= b1.agg, false) OR b2.hit IS NULL);
