SELECT count(*) FROM public.lineitem l WHERE (((EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND l.l_shipmode != 'AIR' 
   AND l.l_discount != l.l_tax 
   AND o.o_totalprice > 25000 
   AND o.o_totalprice <= 288000 
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey != ps.ps_suppkey 
      AND s.s_nationkey <= c.c_nationkey 
      AND s.s_acctbal <= ps.ps_supplycost 
      AND s.s_acctbal < c.c_acctbal 
      AND EXISTS (
       SELECT 1 FROM public.nation n, public.region r
       WHERE n.n_nationkey = s.s_nationkey 
         AND r.r_regionkey = n.n_regionkey 
         AND r.r_name != 'EUROPE' 
      )
   )
)) OR (EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND o.o_orderstatus = 'O' 
   AND p.p_brand != 'Brand#11' 
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey = ps.ps_suppkey 
      AND s.s_nationkey < c.c_nationkey 
      AND s.s_acctbal >= ps.ps_supplycost 
      AND EXISTS (
       SELECT 1 FROM public.partsupp w
       WHERE w.ps_partkey = l.l_partkey 
         AND w.ps_supplycost < c.c_acctbal 
         AND w.ps_supplycost < ps.ps_supplycost 
         AND w.ps_availqty > ps.ps_availqty 
         AND w.ps_availqty > 4500 
         AND w.ps_availqty <= 9000 
      )
   )
))) AND NOT (EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND l.l_quantity != p.p_size 
   AND o.o_orderpriority != '5-LOW' 
   AND EXISTS (
    SELECT 1 FROM public.supplier actual
    WHERE actual.s_suppkey = l.l_suppkey 
      AND actual.s_acctbal > c.c_acctbal 
      AND actual.s_nationkey != c.c_nationkey 
      AND actual.s_acctbal > 1700 
      AND actual.s_acctbal <= 9700 
   )
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey <= ps.ps_suppkey 
      AND s.s_nationkey > c.c_nationkey 
      AND s.s_acctbal >= ps.ps_supplycost 
      AND s.s_acctbal < p.p_retailprice 
   )
))) OR (EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND c.c_acctbal < l.l_extendedprice 
   AND EXISTS (
    SELECT 1 FROM public.lineitem w
    WHERE w.l_partkey = l.l_partkey 
      AND w.l_suppkey != l.l_suppkey 
      AND w.l_receiptdate < l.l_receiptdate 
      AND w.l_discount < l.l_discount 
      AND w.l_tax > l.l_tax 
      AND w.l_discount >= 0.04 
      AND w.l_discount <= 0.05 
   )
   AND EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey > ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal >= ps.ps_supplycost 
   )
));
