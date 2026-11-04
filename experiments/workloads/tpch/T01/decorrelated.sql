SELECT count(*) FROM public.lineitem lineitem
WHERE (lineitem.l_shipmode = 'AIR' OR lineitem.l_shipmode = 'REG AIR');
