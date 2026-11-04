SELECT count(*) FROM public.chartevents chartevents WHERE (warning = 1 OR EXISTS (SELECT 1 FROM public.d_items d WHERE d.itemid = chartevents.itemid AND d.category = 'Routine Vital Signs'));
