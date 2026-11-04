SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT max(s.s_acctbal) AS agg FROM public.supplier s, public.nation n WHERE n.n_nationkey = s.s_nationkey AND n.n_regionkey = 3) b1 ON true
WHERE COALESCE(lineitem.l_extendedprice <= b1.agg, false);
