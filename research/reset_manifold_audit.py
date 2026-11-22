# Exhaustive 2310-residue reset-state restricted-wheel check.
from math import isqrt
P = 3*5*7*11
PRIMES = (3,5,7,11)
def run(t,z):
    C = 2*t-z
    growth=0
    steps=0
    maxz=z
    start=t
    while True:
        clocks=[]
        for p in PRIMES:
            if (C-1)%p==0: r=0
            elif (C+1)%p==0:r=p+2
            else:continue
            dt=(r-t)%(2*p)
            clocks.append((dt or 2*p,p))
        if not clocks: break
        delta=min(x[0] for x in clocks)
        d=1
        for dt,p in clocks:
            if dt==delta:d*=p
        t+=delta;C+=d-1;growth+=d-1;steps+=1
        assert steps<=22
        maxz=max(maxz,2*t-C)
    return steps,growth,maxz,t-start
for z in (0,6):
    vals=[run(t,z) for t in range(2*P)]
    maxima=tuple(max(a[i] for a in vals) for i in range(4))
    print(z,maxima)
    assert maxima[:3]==((19,100,146) if z==0 else (18,100,146))
