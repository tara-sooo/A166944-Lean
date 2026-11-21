#!/usr/bin/env python3
"""A166944 paper-certificate audit: sharp 35% long-H drift, rough horizons,
synthetic arbitrarily-large direct-low long-H primes, and mixed excursions.

Python 3 standard library. Local moving-horizon first hits are not automatically
actual attained-record states. Cap B and twin-prime infinitude are not proved.
"""
from math import gcd, isqrt
from cap_b_interleaved_return_audit import CASES


def primes_to(n):
    sieve=bytearray(b'\x01')*(n+1)
    sieve[0:2]=b'\x00\x00'
    for q in range(2,isqrt(n)+1):
        if sieve[q]:sieve[q*q:n+1:q]=b'\x00'*((n-q*q)//q+1)
    return [q for q in range(2,n+1) if sieve[q]]


def factors(n):
    ans=[]
    for q in range(2,isqrt(n)+1):
        while n%q==0:
            ans.append(q);n//=q
        if n==1:break
    if n>1:ans.append(n)
    return ans


def d(r,C):
    return gcd(r if r%2==0 else r-2,C-1 if r%2==0 else C+1)


def exact_first(s,C,g,e):
    assert s>=2 and 0<=2*s-C and s+g<=C
    assert all(d(j,C)==1 for j in range(s+1,s+g))
    assert d(s+g,C)==e
    return (2*s-C,2*(s+g)-(C+e-1))


def step_drift_certificate():
    count=0
    for p in primes_to(1000):
        for g in range(11,2*p+1):
            if p-1<3*(g+1):
                assert 40*g>=13*(p-1),(p,g)
                count+=1
    assert exact_first(479,780,13,41)==(178,164)
    # Exact modular brake: successive long first hits require the first
    # increment to be 1 mod 3, as each long-start horizon is 0 mod 3.
    s,C=27543,55080
    for g,e in ((6,13),(18,37),(14,29)):
        assert C%3==0
        assert exact_first(s,C,g,e)==(6,6)
        s+=g;C+=e-1
    assert C%3==1
    assert d(s+1,C)==3
    assert 40*13==13*(41-1)
    print('PASS long-H prime drift: 40*g>=13*(p-1) for all',count,
          'small-prime/gap parameter pairs; exact sharp p=41/g=13 first hit')


def almost_prime_direct_examples():
    M=45_895_573;K=(7*M-1)//4;Cmin=2*M-2;Cmax=2*K
    assert K==80_317_252
    # p=2203, both +/- sides are semiprime, even direct low return
    for s,C,g,p,pre,post,sign,other in (
        (45_918_234,91_836_462,1098,2203,6,0,-1,41687),
        (46_198_014,92_396_022,1101,2203,6,6,+1,41941),
    ):
        assert Cmin<=C<=Cmax
        assert exact_first(s,C,g,p)==(pre,post)
        A=factors(C-1);B=factors(C+1)
        assert len(A)<=2 and len(B)<=2
        side=C+sign
        assert factors(side)==sorted((p,other))
        assert all(q**3>C+1 for q in A+B)
        assert g**3>8*(C+1)
        assert other%4==(3 if sign==-1 else 1)
        print('PASS near-cutoff synthetic direct long-H p=',p,
              'C=',C,'X:',pre,'->',post,'factors C-1:',A,'C+1:',B)
    for s,C,g,p,final in (
        (45_896_517,91_793_028,1103,2213,0),
        (46_093_527,92_187_048,1107,2221,0),
    ):
        assert s % 6 == 3 and C % 12 == 0 and p % 4 == 1
        assert exact_first(s,C,g,p)==(6,final)
        assert len(factors(C-1))==2 and len(factors(C+1))<=2
        assert all(q**3>C+1 for q in factors(C-1)+factors(C+1))
        sp=s+g; Cp=C+p-1
        assert Cp%3==(0 if p%3==1 else 1)
        if p%3==2:
            assert any(d(sp+j,Cp)>1 for j in range(1,7))
        print('PASS canonical-residue synthetic semiprime direct return: p=',p,
              'p%12=',p%12,'pre-index=',s,'pre-horizon=',C)
    # If p>=2189 and low X, direct landing => g>2*cuberoot(C+1).
    assert (2189-11)**3>64*(Cmax+1)
    print('PASS official-cutoff algebra: direct-low p>=2189 -> both C+/-1 at most semiprime')


def crt_join(a,L,b,m):
    assert gcd(L,m)==1
    t=((b-a)*pow(L,-1,m))%m
    return (a+L*t)%(L*m), L*m


def flat_offset_family():
    for p in (37,41,61,73,97,109,157):
        assert p in primes_to(p) and p%4==1
        a,L=1,6
        for q in primes_to(p+4):
            if q>=5 and q!=p:
                a,L=crt_join(a,L,0,q)
        a,L=crt_join(a,L,(p+1)//2,p)
        M=a
        if M<p+20:M+=L*((p+20-M+L-1)//L)
        assert M%6==1 and (2*M-1)%p==0
        s,C=M+2,2*M-2
        g=(p-1)//2
        assert exact_first(s,C,g,p)==(6,6)
        assert p-1<3*(g+1) and g>10
        print('PASS unbounded direct-low CRT family: p=',p,'M decimal digits=',len(str(M)),
              'g=',g,'H=',p-1,'post offset=6')


def interleaved_ledger():
    for M,word in CASES.items():
        s,C=M+2,2*M-2
        arr=[]
        for g,e in word:
            pre,post=exact_first(s,C,g,e)
            isH=e-1<3*(g+1)
            if isH and g>10:
                assert 20*(post-pre)+7*(e-1)>=0
            elif isH:
                assert 2*(post-pre)+(e-1)>=0
            else:
                assert post-pre>=-(e-1)
            arr.append((pre,post,g,e,isH))
            s+=g;C+=e-1
        G=sum(e-1 for x,y,g,e,h in arr)
        Hs=sum(e-1 for x,y,g,e,h in arr if h and g<=10)
        Hl=sum(e-1 for x,y,g,e,h in arr if h and g>10)
        N=J=0;i=0
        while i<len(arr):
            x,y,g,e,h=arr[i]
            if x<=10 and h and g>10 and e>=13 and y>=2*e:
                N+=1;J+=e-1
                j=next((j for j in range(i+1,len(arr)) if arr[j][1]<=10),len(arr)-1)
                i=j+1
            else:i+=1
        terminal=2*s-C
        LHS=47*J
        RHS=20*G-10*Hs-13*Hl+160*N+20*max(0,terminal-10)
        assert LHS<=RHS,(M,LHS,RHS)
        print('PASS mixed jump ledger: M=',M,'N=',N,'J=',J,
              'Hs=',Hs,'Hl=',Hl,'lhs=',LHS,'rhs=',RHS,'margin=',RHS-LHS)


def main():
    step_drift_certificate()
    almost_prime_direct_examples()
    flat_offset_family()
    interleaved_ledger()
    print('Cap B remains OPEN; finite witnesses and paper lemmas only.')

if __name__=='__main__':main()
