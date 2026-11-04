SELECT count(*) FROM public.chartevents chartevents WHERE (valueuom = 'bpm' OR valueuom = 'insp/min') AND warning = 0;
