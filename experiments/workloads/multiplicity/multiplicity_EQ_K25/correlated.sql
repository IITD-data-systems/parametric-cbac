SELECT count(*) FROM public.customer_m customer_m WHERE EXISTS (SELECT 1 FROM public.supplier_m supplier_m WHERE supplier_m.grp_25=customer_m.grp_25 AND supplier_m.grp_5 = 0);
