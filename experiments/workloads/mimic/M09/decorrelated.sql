SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT DISTINCT key1, key2, 1 AS hit FROM (SELECT l.charttime AS key1, l.subject_id AS key2 FROM public.labevents l) x) b1 ON chartevents.charttime = b1.key1 AND chartevents.subject_id = b1.key2
WHERE (chartevents.valueuom = 'mmHg' AND b1.hit IS NULL);
