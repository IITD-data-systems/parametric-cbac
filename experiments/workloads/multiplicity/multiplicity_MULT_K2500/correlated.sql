SELECT count(*) FROM public.customer_m customer_m WHERE EXISTS (SELECT 1 FROM public.supplier_m supplier_m
WHERE supplier_m.grp_2500=customer_m.grp_2500
AND supplier_m.s_acctbal>=customer_m.c_acctbal
AND supplier_m.s_acctbal<=1455.96);
