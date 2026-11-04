SELECT count(*) FROM public.chartevents chartevents WHERE EXISTS (SELECT 1 FROM public.d_items d WHERE d.itemid = chartevents.itemid AND chartevents.valuenum > d.highnormalvalue);
