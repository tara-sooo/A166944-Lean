#!/usr/bin/env python3
"""Independent literal 133-step low-only wheel check of inverse-degree 39.
This checker does NOT use C++ prime-clock jumps.
"""
from collections import Counter
from math import gcd
P=3*5*7*11
L=2*P

def literal(t,c):
    for n in range(t+1,t+134):
        raw=gcd(n if n%2==0 else n-2,c-1 if n%2==0 else c+1)
        d=1
        for p in (3,5,7,11):
            if raw%p==0:d*=p
        c+=d-1
    assert gcd(c-1,P)==1 and gcd(c+1,P)==1
    return c

def main():
    for r in (0,1,17,100,1840,2309):
        t=10*L+r
        outputs=[]
        for k in range(P):
            c=20*L+2*k
            out=literal(t,c)
            outputs.append(out%L)
            assert literal(t,c+L)==out+L if k in (0,101,1154) else True
        histogram=Counter(outputs)
        maxdeg=max(histogram.values())
        target=2028 if r==1840 else None
        if r==1840:
            assert histogram[target]==39,(r,histogram[target])
            assert maxdeg==39
            # The sharp L^2 ratio is attained by placing unit mass on
            # exactly the 39 distinct input classes mapping to this output.
            inverse_fibre=[k for k,out in enumerate(outputs) if out==target]
            assert len(inverse_fibre)==39
            pre_l2=len(inverse_fibre)
            post_l2=pre_l2**2
            assert post_l2==39*pre_l2
            print('SHARP_LOW_L2_PASS','inL2',pre_l2,'outL2',post_l2,'normSquare',post_l2/pre_l2)
        assert maxdeg<=39,(r,maxdeg)
        print('LOW_TERMINAL_LITERAL_PASS','tmod',r,'maxFibre',maxdeg,'target2028',histogram.get(target,0) if target is not None else 'na')

if __name__=='__main__':main()
