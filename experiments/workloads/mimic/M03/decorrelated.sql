SELECT count(*) FROM public.chartevents chartevents
WHERE ((chartevents.valueuom = 'bpm' OR chartevents.valueuom = 'insp/min') AND chartevents.warning = 0);
