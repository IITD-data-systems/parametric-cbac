SELECT count(*) FROM public.customer_m customer_m
WHERE customer_m.grp_2500 IN (
SELECT DISTINCT supplier_m.grp_2500 FROM public.supplier_m supplier_m
WHERE supplier_m.grp_5 = 0);
