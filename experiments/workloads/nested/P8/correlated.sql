SELECT count(*) FROM public.lineitem l WHERE (((EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND l.l_shipmode != 'AIR' 
   AND l.l_discount != l.l_tax 
   AND o.o_totalprice > 25000 
   AND o.o_totalprice <= 260000 
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey = ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal < ps.ps_supplycost 
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
      AND l.l_suppkey != ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal < ps.ps_supplycost 
      AND EXISTS (
       SELECT 1 FROM public.partsupp w
       WHERE w.ps_partkey = l.l_partkey 
         AND w.ps_supplycost < c.c_acctbal 
         AND w.ps_supplycost < ps.ps_supplycost 
         AND w.ps_availqty > ps.ps_availqty 
         AND w.ps_availqty > 4000 
         AND w.ps_availqty <= 9500 
      )
   )
))) OR ((EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND p.p_retailprice < c.c_acctbal 
   AND p.p_mfgr != 'Manufacturer#1' 
   AND EXISTS (
    SELECT 1 FROM public.orders w
    WHERE w.o_custkey = o.o_custkey 
      AND w.o_orderstatus != o.o_orderstatus 
      AND w.o_totalprice < o.o_totalprice 
      AND w.o_orderpriority != o.o_orderpriority 
      AND w.o_orderdate > '1993-01-01' 
      AND w.o_orderdate <= '1998-01-01' 
   )
   AND EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey = ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal > ps.ps_supplycost 
   )
)) OR NOT (EXISTS (
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
      AND actual.s_acctbal > 1000 
      AND actual.s_acctbal <= 9700 
   )
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey != ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal > ps.ps_supplycost 
      AND s.s_acctbal < p.p_retailprice 
   )
)))) AND (((l.l_returnflag != 'A' 
 AND EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND l.l_shipdate > l.l_commitdate 
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey = ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal > ps.ps_supplycost 
      AND EXISTS (
       SELECT 1 FROM public.customer w
       WHERE w.c_nationkey = c.c_nationkey 
         AND w.c_acctbal < c.c_acctbal 
         AND w.c_mktsegment = c.c_mktsegment 
         AND w.c_custkey < c.c_custkey 
         AND w.c_acctbal > 5000 
         AND w.c_acctbal <= 5500 
      )
   )
)) AND (EXISTS (
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
      AND w.l_discount >= 0.01 
      AND w.l_discount <= 0.07 
   )
   AND NOT EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey != ps.ps_suppkey 
      AND s.s_nationkey = c.c_nationkey 
      AND s.s_acctbal > ps.ps_supplycost 
   )
))) OR ((l.l_shipinstruct != 'COLLECT COD' 
 AND EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND EXISTS (
    SELECT 1 FROM public.part w
    WHERE w.p_brand = p.p_brand 
      AND w.p_size < p.p_size 
      AND w.p_retailprice > p.p_retailprice 
      AND w.p_container = p.p_container 
      AND w.p_size < l.l_quantity 
      AND w.p_retailprice > 1100 
      AND w.p_retailprice <= 1600 
   )
   AND EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey = ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal > ps.ps_supplycost 
   )
)) OR (EXISTS (
 SELECT 1 FROM public.orders o, public.customer c, public.part p
 WHERE o.o_orderkey = l.l_orderkey 
   AND c.c_custkey = o.o_custkey 
   AND p.p_partkey = l.l_partkey 
   AND EXISTS (
    SELECT 1 FROM public.lineitem w
    WHERE w.l_orderkey = l.l_orderkey 
      AND w.l_shipmode != l.l_shipmode 
      AND w.l_quantity < l.l_quantity 
      AND w.l_extendedprice < l.l_extendedprice 
      AND w.l_returnflag = l.l_returnflag 
      AND w.l_tax > 0 
      AND w.l_tax <= 0.07 
   )
   AND EXISTS ( 
    SELECT 1 FROM public.partsupp ps, public.supplier s
    WHERE ps.ps_partkey = p.p_partkey 
      AND s.s_suppkey = ps.ps_suppkey 
      AND l.l_suppkey != ps.ps_suppkey 
      AND s.s_nationkey != c.c_nationkey 
      AND s.s_acctbal < ps.ps_supplycost 
      AND s.s_acctbal < c.c_acctbal 
   )
))));
