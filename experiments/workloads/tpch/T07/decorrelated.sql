SELECT count(*) FROM public.lineitem lineitem
  LEFT JOIN (SELECT max(s.s_acctbal) AS agg FROM public.supplier s WHERE s.s_nationkey = 7) b1 ON true
WHERE (lineitem.l_quantity <= 5 OR COALESCE(lineitem.l_extendedprice <= b1.agg, false));
