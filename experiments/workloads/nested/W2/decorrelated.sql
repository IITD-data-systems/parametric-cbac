WITH B1 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,p.p_partkey p__p_partkey,l.l_suppkey l__l_suppkey,c.c_nationkey c__c_nationkey,c.c_acctbal c__c_acctbal FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE l.l_shipmode != 'AIR' AND l.l_discount != l.l_tax AND o.o_totalprice > 25000 AND o.o_totalprice <= 215000),
v0 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey,s.s_acctbal s__s_acctbal FROM public.partsupp ps, public.supplier s, public.nation n, public.region r WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal <= ps.ps_supplycost AND n.n_nationkey = s.s_nationkey AND r.r_regionkey = n.n_regionkey AND r.r_name != 'EUROPE'),
d0 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey,c__c_acctbal FROM base),
r0 AS (SELECT DISTINCT d0.p__p_partkey,d0.l__l_suppkey,d0.c__c_nationkey,d0.c__c_acctbal FROM d0 JOIN v0 ON v0.ps__ps_partkey = d0.p__p_partkey WHERE d0.l__l_suppkey != v0.ps__ps_suppkey AND v0.s__s_nationkey <= d0.c__c_nationkey AND v0.s__s_acctbal < d0.c__c_acctbal)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 ANTI JOIN r0 ON b.p__p_partkey=r0.p__p_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.c__c_nationkey=r0.c__c_nationkey AND b.c__c_acctbal=r0.c__c_acctbal),
B6 AS (WITH base AS (SELECT l.l_orderkey,l.l_linenumber,l.l_partkey l__l_partkey,l.l_suppkey l__l_suppkey,l.l_receiptdate l__l_receiptdate,l.l_discount l__l_discount,l.l_tax l__l_tax,p.p_partkey p__p_partkey,c.c_nationkey c__c_nationkey FROM public.lineitem l JOIN public.orders o ON o.o_orderkey=l.l_orderkey
 JOIN public.customer c ON c.c_custkey=o.o_custkey JOIN public.part p ON p.p_partkey=l.l_partkey
 WHERE c.c_acctbal < l.l_extendedprice),
d0 AS (SELECT DISTINCT l__l_partkey,l__l_suppkey,l__l_receiptdate,l__l_discount,l__l_tax FROM base),
r0 AS (SELECT DISTINCT d0.l__l_partkey,d0.l__l_suppkey,d0.l__l_receiptdate,d0.l__l_discount,d0.l__l_tax FROM d0 JOIN (SELECT DISTINCT l_partkey,l_suppkey,l_receiptdate,l_discount,l_tax FROM public.lineitem w WHERE w.l_discount >= 0.01 AND w.l_discount <= 0.05) w ON w.l_partkey = d0.l__l_partkey WHERE w.l_suppkey != d0.l__l_suppkey AND w.l_receiptdate < d0.l__l_receiptdate AND w.l_discount < d0.l__l_discount AND w.l_tax > d0.l__l_tax),
v1 AS MATERIALIZED (SELECT DISTINCT ps.ps_partkey ps__ps_partkey,ps.ps_suppkey ps__ps_suppkey,s.s_nationkey s__s_nationkey FROM public.partsupp ps, public.supplier s WHERE s.s_suppkey = ps.ps_suppkey AND s.s_acctbal >= ps.ps_supplycost),
d1 AS (SELECT DISTINCT p__p_partkey,l__l_suppkey,c__c_nationkey FROM base),
r1 AS (SELECT DISTINCT d1.p__p_partkey,d1.l__l_suppkey,d1.c__c_nationkey FROM d1 JOIN v1 ON v1.ps__ps_partkey = d1.p__p_partkey WHERE d1.l__l_suppkey > v1.ps__ps_suppkey AND v1.s__s_nationkey != d1.c__c_nationkey)
SELECT b.l_orderkey,b.l_linenumber FROM base b
 SEMI JOIN r0 ON b.l__l_partkey=r0.l__l_partkey AND b.l__l_suppkey=r0.l__l_suppkey AND b.l__l_receiptdate=r0.l__l_receiptdate AND b.l__l_discount=r0.l__l_discount AND b.l__l_tax=r0.l__l_tax
 SEMI JOIN r1 ON b.p__p_partkey=r1.p__p_partkey AND b.l__l_suppkey=r1.l__l_suppkey AND b.c__c_nationkey=r1.c__c_nationkey)
SELECT count(*) FROM public.lineitem t
 LEFT JOIN B1 ON B1.l_orderkey=t.l_orderkey AND B1.l_linenumber=t.l_linenumber
 LEFT JOIN B6 ON B6.l_orderkey=t.l_orderkey AND B6.l_linenumber=t.l_linenumber
WHERE (B1.l_orderkey IS NOT NULL) OR (B6.l_orderkey IS NOT NULL);
