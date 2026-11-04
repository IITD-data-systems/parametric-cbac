SELECT count(*) FROM public.chartevents chartevents
  LEFT JOIN (SELECT d.itemid AS key1, min(d.highnormalvalue) AS agg FROM public.d_items d GROUP BY d.itemid) b1 ON chartevents.itemid = b1.key1
WHERE COALESCE(chartevents.valuenum > b1.agg, false);
