SELECT count(*) FROM public.chartevents chartevents
WHERE (chartevents.valueuom = 'mmHg' AND chartevents.valuenum >= 180);
