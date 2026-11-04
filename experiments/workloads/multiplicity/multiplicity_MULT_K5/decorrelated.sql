SELECT count(*) FROM public.customer_m customer_m
WHERE (customer_m.grp_5,customer_m.c_acctbal) IN (
SELECT domain.grp_5,domain.c_acctbal
FROM (SELECT DISTINCT grp_5,c_acctbal FROM public.customer_m) domain
JOIN public.supplier_m supplier_m ON supplier_m.grp_5=domain.grp_5
WHERE supplier_m.s_acctbal>=domain.c_acctbal AND supplier_m.s_acctbal<=1201.92);
