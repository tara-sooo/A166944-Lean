#!/usr/bin/env python3
"""Independent direct integer-by-integer witness checker for 13 possible LOW7+q refiring primes."""
from math import gcd
W={
11:(2309,1508,2310,2332),13:(2729,430,2730,2771),17:(3569,698,3570,3638),
19:(3989,2338,3990,4049),23:(4829,4210,4830,4876),29:(1681,1306,1682,1771),
31:(2946,2386,2947,3009),37:(4848,6326,4849,4884),41:(7789,862,7790,7833),
43:(1117,904,1118,1204),101:(18686,7776,18687,18786),103:(11022,5252,11023,11124),
107:(5563,5458,5564,5673)
}
for q,(t,c,first,second) in W.items():
    ps=(3,5,7,q);hits=[];ev=[]
    for n in range(t+1,second+1):
        raw=gcd(n,c-1) if n%2==0 else gcd(n-2,c+1)
        d=1
        for p in ps:
            if raw%p==0:d*=p
        if d>1:
            c+=d-1;ev.append((n,d))
            if d%q==0:hits.append(n)
    assert hits==[first,second],(q,hits,first,second)
    print('LOW7_LITERAL_Q_REHIT_PASS',q,'hits',hits,'events',ev)
