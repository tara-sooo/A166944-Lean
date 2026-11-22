#!/usr/bin/env python3
"""Exact reset-event and excitation recovery budget checks for A166944.

Reproduces elementary paper lemmas on actual recurrence and synthetic starts.
Python 3 stdlib only. Does NOT prove Cap B or infinitely many twin primes.
"""
from collections import Counter
from math import gcd, isqrt


def prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    for p in range(3, isqrt(n)+1, 2):
        if n % p == 0: return False
    return True


def inc(r, C):
    return gcd(r if r%2==0 else r-2, C-1 if r%2==0 else C+1)


def distinct_large_prime_factors(n):
    """Distinct odd prime factors at least 5 (the factor 3 is excluded)."""
    result=[]
    f=3
    while f*f<=n:
        if n%f==0:
            if f>=5:result.append(f)
            while n%f==0:n//=f
        f+=2
    if n>=5:result.append(n)
    return result


def directional_recharge(p, first_parity, later_parity):
    """Sharp minimal EVEN intervening growth modulo p."""
    assert p>=5 and prime(p)
    return p + {(0,0):1,(0,1):-1,(1,0):3,(1,1):1}[(first_parity,later_parity)]


def classify(s, C, r, e):
    x=2*s-C
    assert x in (0,6) and e >= 9 and inc(r,C)==e
    g=r-s
    u=2*g+x+(1 if r%2==0 else -5)
    assert u>0 and u%e==0
    k=u//e
    assert k in (1,3)
    assert 3*e-7<=2*g if k==3 else True
    after=2*r-(C+e-1)
    assert after==(k-1)*e + (0 if r%2==0 else 6)
    assert prime(e) or (k==1 and e in (9,15,25))
    return k, g


def run(s0,C0,end):
    assert s0>=2 and C0%2==0 and C0<=2*s0
    C=C0
    last=(s0,C0)
    modes=Counter()
    excursions=[]
    opened=None
    total_exc_gap=0
    total_exc_weight=0
    first_exc=None
    all_events=0
    previous_factors={}
    directional_counts=Counter()
    sharp_recharges=[]
    for n in range(s0+1,end+1):
        xpre=2*(n-1)-C
        e=inc(n,C)
        if e>1:
            all_events+=1
            U=xpre+(3 if n%2==0 else -3)
            primitive=(U>0 and e==U)
            for p in distinct_large_prime_factors(e):
                if p in previous_factors:
                    old_postC, oldpar, oldr=previous_factors[p]
                    needed=directional_recharge(p,oldpar,n%2)
                    actual_growth=C-old_postC
                    assert actual_growth>=needed,(p,n,actual_growth,needed)
                    directional_counts[(oldpar,n%2)]+=1
                    if actual_growth==needed:
                        sharp_recharges.append((oldr,n,p,needed))
                previous_factors[p]=(C+e-1,n%2,n)
            if opened is not None and n!=opened['start']:
                opened['growth']+=e-1
                if primitive:
                    opened['f']=e;opened['end']=n
                    m=opened['proper']
                    y=opened['X0']-6
                    assert y >= 12
                    assert opened['f']>=5
                    assert (opened['f']-3)*3**m >= y*2**m
                    assert opened['growth']>=2*m+e-1
                    assert (opened['growth']-2*m-2)*3**m >= y*2**m
                    if e % opened['e']==0:
                        needed=directional_recharge(opened['e'],opened['start']%2,n%2)
                        assert opened['proper_growth']>=needed
                        assert opened['growth']>=needed+(e-1)
                        opened['reuse_recharge_min']=needed
                        modes['close_same_p']+=1
                    excursions.append(opened)
                    opened=None
                else:
                    assert U>e and U>0 and xpre>=8
                    assert 3*(xpre+3-e-6)>=2*(xpre-6)
                    opened['proper']+=1
                    opened['proper_growth']+=e-1
            s,oldC=last
            if 2*s-oldC in (0,6) and e>=9:
                k,g=classify(s,oldC,n,e)
                modes['k'+str(k)]+=1
                if not prime(e):modes['composite_'+str(e)]+=1
                if k==3:
                    assert opened is None
                    total_exc_gap+=g
                    total_exc_weight+=3*e-7
                    opened={'start':n,'e':e,'X0':2*n-(C+e-1),
                            'proper':0,'proper_growth':0,'growth':0,
                            'prev_s':s,'gap':g}
                    if first_exc is None:first_exc=(s,n,e,g)
            last=(n,C+e-1)
        C+=e-1
        if n>=3:
            assert 2*n-C>=0,('X negative',s0,n,C)
    assert total_exc_weight <=2*total_exc_gap<=2*(end-s0)
    certified_growth=sum(x['growth'] for x in excursions)
    assert certified_growth<=C-C0
    return {'events':all_events,'modes':dict(modes),'completed':len(excursions),
            'unfinished':opened,'exc_gap_sum':total_exc_gap,
            'exc_weight_sum':total_exc_weight,'discharge_growth':certified_growth,
            'total_growth':C-C0,'first_exc':first_exc, 'excursions':excursions,
            'directional_counts':dict(directional_counts),'sharp_recharges':sharp_recharges}


def direct_exception(s,C,r,e):
    for j in range(s+1,r):
        assert inc(j,C)==1
    assert inc(r,C)==e
    k,g=classify(s,C,r,e)
    assert k==1
    print('Composite reset witness:',s,C,'->',r,'increment',e,'gap',g)


def main():
    direct_exception(17,28,18,9)
    direct_exception(26,46,30,15)
    direct_exception(141,276,150,25)
    original=run(2,2,2_500_000)
    assert original['events']==249
    assert original['modes']=={'k1':36,'k3':10,'composite_9':7,'composite_25':3}
    assert original['completed']==9 and original['unfinished']['e']==11
    assert sum(original['directional_counts'].values())==125
    assert len(original['sharp_recharges'])==14
    assert original['first_exc']==(318,340,17,22)
    print('Original recurrence 2.5M:',{k:v for k,v in original.items() if k not in ('excursions','unfinished','sharp_recharges')})
    for M in (367,100549,101119):
        K=(7*M-1)//4
        x=run(M+2,2*M-2,K)
        print('Synthetic canonical-shaped M=',M,'modes',x['modes'],
              'completed',x['completed'],'open',bool(x['unfinished']),
              'charged growth',x['discharge_growth'],'total growth',x['total_growth'])
        if M==101119:
            assert any(v['e']==13 and v['f']==39 and v['proper']==1 and
                       v['proper_growth']==16 and v['reuse_recharge_min']==16
                       for v in x['excursions'])
            print('Sharp excitation recharging:',next((v for v in x['excursions']
                  if v['e']==13 and v['f']==39),None))
    print('PASS: disjoint excursion charges + reset-primality and fuel reuse; global Cap B still open')


if __name__=='__main__':
    main()
