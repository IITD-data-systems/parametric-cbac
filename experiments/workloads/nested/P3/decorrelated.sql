WITH B1 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey,c.c_acctbal c__c_acctbal FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE l.l_shipmode != 'AIR' AND l.l_discount != l.l_tax AND o.o_totalprice > 25000 AND o.o_totalprice <= 260000),
v0 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey,s.s_acctbal s__s_acctbal FROM public.partsupp ps, public.supplier s, public.nation n, public.region r WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal < ps.ps_supplycost AND n.n_nationkey = s.s_nationkey AND r.r_regionkey = n.n_regionkey AND r.r_name != 'EUROPE'),
d0 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,c__c_acctbal FROM base),
r0 AS (SELECT DISTINCT d0.p__p_partkey,d0.l__l_suppkey,d0.c__c_nationkey,d0.c__c_acctbal FROM d0 JOIN v0 ON v0.ps__ps_partkey = d0.p__p_partkey WHERE d0.l__l_suppkey != v0.ps__ps_suppkey AND v0.s__s_nationkey != d0.c__c_nationkey AND v0.s__s_acctbal < d0.c__c_acctbal)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.p__p_partkey=r0.p__p_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.c__c_nationkey=r0.c__c_nationkey AND b.c__c_acctbal=r0.c__c_acctbal),
B2 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey,l.l_partkey l__l_partkey,c.c_acctbal c__c_acctbal FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE o.o_orderstatus = 'O' AND p.p_brand != 'Brand#11'),
v0 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey,ps.ps_supplycost ps__ps_supplycost,ps.ps_availqty ps__ps_availqty FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal > ps.ps_supplycost),
d0 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,l__l_partkey,c__c_acctbal FROM base),
r0 AS (SELECT DISTINCT d0.p__p_partkey,d0.l__l_suppkey,d0.c__c_nationkey,d0.l__l_partkey,d0.c__c_acctbal FROM d0 JOIN v0 ON v0.ps__ps_partkey = d0.p__p_partkey AND d0.l__l_suppkey = v0.ps__ps_suppkey
 JOIN (SELECT ps_partkey,ps_supplycost,ps_availqty FROM (SELECT ps_partkey,ps_supplycost,ps_availqty,max(ps_availqty) OVER (PARTITION BY ps_partkey ORDER BY ps_supplycost ASC ROWS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING) prev FROM (SELECT ps_partkey,ps_supplycost,max(ps_availqty) ps_availqty FROM public.partsupp w WHERE w.ps_availqty > 5000 AND w.ps_availqty <= 9500 GROUP BY ps_partkey,ps_supplycost)) WHERE prev IS NULL OR ps_availqty > prev) w ON w.ps_partkey = d0.l__l_partkey WHERE v0.s__s_nationkey != d0.c__c_nationkey AND w.ps_supplycost < d0.c__c_acctbal AND w.ps_supplycost < v0.ps__ps_supplycost AND w.ps_availqty > v0.ps__ps_availqty)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 ANTI JOIN r0 ON b.p__p_partkey=r0.p__p_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.c__c_nationkey=r0.c__c_nationkey AND b.l__l_partkey=r0.l__l_partkey AND b.c__c_acctbal=r0.c__c_acctbal),
B3 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,o.o_custkey o__o_custkey,o.o_orderstatus o__o_orderstatus,o.o_totalprice o__o_totalprice,o.o_orderpriority o__o_orderpriority,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE p.p_retailprice < c.c_acctbal AND p.p_mfgr != 'Manufacturer#1'),
d0 AS (SELECT DISTINCT o__o_custkey,o__o_orderstatus,o__o_totalprice,o__o_orderpriority FROM base),
r0 AS (SELECT DISTINCT d0.o__o_custkey,d0.o__o_orderstatus,d0.o__o_totalprice,d0.o__o_orderpriority FROM d0 JOIN (SELECT o_custkey,o_orderstatus,o_orderpriority,max(o_totalprice) o_totalprice FROM public.orders w WHERE w.o_orderdate > '1994-01-01' AND w.o_orderdate <= '1996-01-01' GROUP BY o_custkey,o_orderstatus,o_orderpriority) w ON w.o_custkey = d0.o__o_custkey WHERE w.o_orderstatus != d0.o__o_orderstatus AND w.o_totalprice > d0.o__o_totalprice AND w.o_orderpriority != d0.o__o_orderpriority),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal > ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey AND d1.l__l_suppkey = v1.ps__ps_suppkey WHERE v1.s__s_nationkey != d1.c__c_nationkey)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.o__o_custkey=r0.o__o_custkey AND b.o__o_orderstatus=r0.o__o_orderstatus AND b.o__o_totalprice=r0.o__o_totalprice AND b.o__o_orderpriority=r0.o__o_orderpriority
 SEMI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey),
B4 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,l.l_suppkey l__l_suppkey,c.c_acctbal c__c_acctbal,c.c_nationkey c__c_nationkey,p.p_partkey p__p_partkey,p.p_retailprice p__p_retailprice FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE l.l_quantity != p.p_size AND o.o_orderpriority != '5-LOW'),
d0 AS (SELECT DISTINCT l__l_suppkey,c__c_acctbal,c__c_nationkey FROM base),
r0 AS (SELECT DISTINCT d0.l__l_suppkey,d0.c__c_acctbal,d0.c__c_nationkey FROM d0 JOIN (SELECT s_suppkey,s_nationkey,max(s_acctbal) s_acctbal FROM public.supplier actual WHERE actual.s_acctbal > 1000 AND actual.s_acctbal <= 9700 GROUP BY s_suppkey,s_nationkey) actual ON actual.s_suppkey = d0.l__l_suppkey WHERE actual.s_acctbal > d0.c__c_acctbal AND actual.s_nationkey != d0.c__c_nationkey),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey,s.s_acctbal s__s_acctbal FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal > ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,p__p_retailprice FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey,d1.p__p_retailprice FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey WHERE d1.l__l_suppkey != v1.ps__ps_suppkey AND v1.s__s_nationkey != d1.c__c_nationkey AND v1.s__s_acctbal < d1.p__p_retailprice)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.l__l_suppkey=r0.l__l_suppkey AND b.c__c_acctbal=r0.c__c_acctbal AND b.c__c_nationkey=r0.c__c_nationkey
 ANTI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey AND b.p__p_retailprice=r1.p__p_retailprice),
B5 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey,c.c_acctbal c__c_acctbal,c.c_mktsegment c__c_mktsegment,c.c_custkey c__c_custkey FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE l.l_returnflag != 'A' AND l.l_shipdate > l.l_commitdate),
v0 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal < ps.ps_supplycost),
d0 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,c__c_acctbal,c__c_mktsegment,c__c_custkey FROM base),
r0 AS (SELECT DISTINCT d0.p__p_partkey,d0.l__l_suppkey,d0.c__c_nationkey,d0.c__c_acctbal,d0.c__c_mktsegment,d0.c__c_custkey FROM d0 JOIN v0 ON v0.ps__ps_partkey = d0.p__p_partkey
 JOIN (SELECT c_nationkey,c_mktsegment,c_acctbal,c_custkey FROM (SELECT c_nationkey,c_mktsegment,c_acctbal,c_custkey,max(c_custkey) OVER (PARTITION BY c_nationkey,c_mktsegment ORDER BY c_acctbal DESC ROWS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING) prev FROM (SELECT c_nationkey,c_mktsegment,c_acctbal,max(c_custkey) c_custkey FROM public.customer w WHERE w.c_acctbal > 5000 AND w.c_acctbal <= 6000 GROUP BY c_nationkey,c_mktsegment,c_acctbal)) WHERE prev IS NULL OR c_custkey > prev) w ON w.c_nationkey = d0.c__c_nationkey AND w.c_mktsegment = d0.c__c_mktsegment WHERE d0.l__l_suppkey != v0.ps__ps_suppkey AND v0.s__s_nationkey != d0.c__c_nationkey AND w.c_acctbal > d0.c__c_acctbal AND w.c_custkey > d0.c__c_custkey)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 ANTI JOIN r0 ON b.p__p_partkey=r0.p__p_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.c__c_nationkey=r0.c__c_nationkey AND b.c__c_acctbal=r0.c__c_acctbal AND b.c__c_mktsegment=r0.c__c_mktsegment AND b.c__c_custkey=r0.c__c_custkey),
B6 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,l.l_partkey l__l_partkey,l.l_suppkey l__l_suppkey,l.l_receiptdate l__l_receiptdate,l.l_discount l__l_discount,l.l_tax l__l_tax,p.p_partkey p__p_partkey,c.c_nationkey c__c_nationkey FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE c.c_acctbal < l.l_extendedprice),
d0 AS (SELECT DISTINCT l__l_partkey,l__l_suppkey,l__l_receiptdate,l__l_discount,l__l_tax FROM base),
r0 AS (SELECT DISTINCT d0.l__l_partkey,d0.l__l_suppkey,d0.l__l_receiptdate,d0.l__l_discount,d0.l__l_tax FROM d0 JOIN (SELECT DISTINCT l_partkey,l_suppkey,l_receiptdate,l_discount,l_tax FROM public.lineitem w WHERE w.l_discount >= 0.01 AND w.l_discount <= 0.07) w ON w.l_partkey = d0.l__l_partkey WHERE w.l_suppkey != d0.l__l_suppkey AND w.l_receiptdate < d0.l__l_receiptdate AND w.l_discount < d0.l__l_discount AND w.l_tax > d0.l__l_tax),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal > ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey AND v1.s__s_nationkey = d1.c__c_nationkey WHERE d1.l__l_suppkey != v1.ps__ps_suppkey)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.l__l_partkey=r0.l__l_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.l__l_receiptdate=r0.l__l_receiptdate AND b.l__l_discount=r0.l__l_discount AND b.l__l_tax=r0.l__l_tax
 ANTI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey),
B7 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,p.p_brand p__p_brand,p.p_size p__p_size,p.p_retailprice p__p_retailprice,p.p_container p__p_container,l.l_quantity l__l_quantity,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE l.l_shipinstruct != 'COLLECT COD'),
d0 AS (SELECT DISTINCT p__p_brand,p__p_size,p__p_retailprice,p__p_container,l__l_quantity FROM base),
r0 AS (SELECT DISTINCT d0.p__p_brand,d0.p__p_size,d0.p__p_retailprice,d0.p__p_container,d0.l__l_quantity FROM d0 JOIN (SELECT p_brand,p_container,p_size,p_retailprice FROM (SELECT p_brand,p_container,p_size,p_retailprice,max(p_retailprice) OVER (PARTITION BY p_brand,p_container ORDER BY p_size ASC ROWS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING) prev FROM (SELECT p_brand,p_container,p_size,max(p_retailprice) p_retailprice FROM public.part w WHERE w.p_retailprice > 1200 AND w.p_retailprice <= 1450 GROUP BY p_brand,p_container,p_size)) WHERE prev IS NULL OR p_retailprice > prev) w ON w.p_brand = d0.p__p_brand AND w.p_container = d0.p__p_container WHERE w.p_size < d0.p__p_size AND w.p_retailprice > d0.p__p_retailprice AND w.p_size < d0.l__l_quantity),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal < ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey WHERE d1.l__l_suppkey != v1.ps__ps_suppkey AND v1.s__s_nationkey != d1.c__c_nationkey)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.p__p_brand=r0.p__p_brand AND b.p__p_size=r0.p__p_size AND b.p__p_retailprice=r0.p__p_retailprice AND b.p__p_container=r0.p__p_container AND b.l__l_quantity=r0.l__l_quantity
 ANTI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey),
B8 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,l.l_orderkey l__l_orderkey,l.l_shipmode l__l_shipmode,l.l_quantity l__l_quantity,l.l_extendedprice l__l_extendedprice,l.l_returnflag l__l_returnflag,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey,c.c_acctbal c__c_acctbal FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey),
d0 AS (SELECT DISTINCT l__l_orderkey,l__l_shipmode,l__l_quantity,l__l_extendedprice,l__l_returnflag FROM base),
r0 AS (SELECT DISTINCT d0.l__l_orderkey,d0.l__l_shipmode,d0.l__l_quantity,d0.l__l_extendedprice,d0.l__l_returnflag FROM d0 JOIN (SELECT l_orderkey,l_returnflag,l_shipmode,l_quantity,l_extendedprice FROM (SELECT l_orderkey,l_returnflag,l_shipmode,l_quantity,l_extendedprice,min(l_extendedprice) OVER (PARTITION BY l_orderkey,l_returnflag,l_shipmode ORDER BY l_quantity ASC ROWS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING) prev FROM (SELECT l_orderkey,l_returnflag,l_shipmode,l_quantity,min(l_extendedprice) l_extendedprice FROM public.lineitem w WHERE w.l_tax > 0 AND w.l_tax <= 0.07 GROUP BY l_orderkey,l_returnflag,l_shipmode,l_quantity)) WHERE prev IS NULL OR l_extendedprice < prev) w ON w.l_orderkey = d0.l__l_orderkey AND w.l_returnflag = d0.l__l_returnflag WHERE w.l_shipmode != d0.l__l_shipmode AND w.l_quantity < d0.l__l_quantity AND w.l_extendedprice < d0.l__l_extendedprice),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey,s.s_acctbal s__s_acctbal FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal > ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,c__c_acctbal FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey,d1.c__c_acctbal FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey AND d1.l__l_suppkey = v1.ps__ps_suppkey WHERE v1.s__s_nationkey != d1.c__c_nationkey AND v1.s__s_acctbal < d1.c__c_acctbal)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.l__l_orderkey=r0.l__l_orderkey AND b.l__l_shipmode=r0.l__l_shipmode AND b.l__l_quantity=r0.l__l_quantity AND b.l__l_extendedprice=r0.l__l_extendedprice AND b.l__l_returnflag=r0.l__l_returnflag
 SEMI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey AND b.c__c_acctbal=r1.c__c_acctbal)
SELECT count(*) FROM public.lineitem t
 LEFT JOIN B1 ON B1.l_orderkey=t.l_orderkey AND B1.l_linenumber=t.l_linenumber
 LEFT JOIN B2 ON B2.l_orderkey=t.l_orderkey AND B2.l_linenumber=t.l_linenumber
 LEFT JOIN B3 ON B3.l_orderkey=t.l_orderkey AND B3.l_linenumber=t.l_linenumber
 LEFT JOIN B4 ON B4.l_orderkey=t.l_orderkey AND B4.l_linenumber=t.l_linenumber
 LEFT JOIN B5 ON B5.l_orderkey=t.l_orderkey AND B5.l_linenumber=t.l_linenumber
 LEFT JOIN B6 ON B6.l_orderkey=t.l_orderkey AND B6.l_linenumber=t.l_linenumber
 LEFT JOIN B7 ON B7.l_orderkey=t.l_orderkey AND B7.l_linenumber=t.l_linenumber
 LEFT JOIN B8 ON B8.l_orderkey=t.l_orderkey AND B8.l_linenumber=t.l_linenumber
WHERE (((B1.l_orderkey IS NOT NULL) OR (B2.l_orderkey IS NOT NULL)) OR ((B3.l_orderkey IS NOT NULL) AND (B4.l_orderkey IS NOT NULL))) AND (((B5.l_orderkey IS NOT NULL) OR (B6.l_orderkey IS NOT NULL)) OR ((B7.l_orderkey IS NOT NULL) OR NOT (B8.l_orderkey IS NOT NULL)));
