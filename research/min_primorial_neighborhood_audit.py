# Requires Python 3.11+ and sympy. Run from any directory.
from collections import deque
from functools import lru_cache
from math import gcd
from sys import set_int_max_str_digits
from sympy import factorint, isprime, primerange, nextprime
set_int_max_str_digits(0)

@lru_cache(None)
def factors(n):
    return tuple(sorted(int(q) for q in factorint(abs(n)))) if abs(n)>1 else ()

def low(u,v,S):
    a=[]
    for e in (1,-1):
        for p in factors(u-e):
            if p<=S:
                n0=0 if e==1 else p+2
                w=(n0-v)%(2*p) or 2*p
                a.append((w,p,e))
    return min(a) if a else None

def shadow(S):
    u,v=4,5
    path=[]
    maxd,maxh=6,0
    while u<=S*S-2:
        a=low(u,v,S)
        if a is None:
            assert isprime(u-1) and isprime(u+1) and u-1>S
            return u,v,path,maxd,maxh,'rough'
        w,p,e=a
        maxh=max(maxh,2*(v+w)-u+1)
        path.append((u,v,w,p))
        u+=p-1
        v+=w
        assert 2*v>=u
        maxd=max(maxd,2*v-u)
    return u,v,path,maxd,maxh,'cross'

def allow(c,q,r):
    if q not in c:return True
    a,b=c[q]
    return (a is None or a==r) and r not in b

def forbid(c,q,r):
    if q not in c:
        c[q]=(None,frozenset([r]))
        return True
    a,b=c[q]
    if a==r:return False
    b=b|{r}
    if a is None and len(b)==q:return False
    c[q]=(a,b)
    return True

def solve(S):
    # BFS for a rough pre-horizon in the window, not minimum crossing length.
    # All candidate primes are eligible in a sufficiently large lift.
    q=deque([(4,5,{},[])])
    seen=0
    while q:
        u,v,c,path=q.popleft()
        seen+=1
        if seen>100000:raise RuntimeError('state cap')
        if u>S*S-2:continue
        if all(p>S for e in (-1,1) for p in factors(u+e)):
            assert isprime(u-1) and isprime(u+1) and u-1>S
            return len(path),u,v,seen,path,c
        c=c.copy()
        for n in range(v+1,v+2*S+1):
            h=2*n-u+(1 if n%2==0 else -5)
            r0=-n+(2 if n%2 else 0)
            for p in factors(h):
                r=r0%p
                if p<=S:
                    if r==0:
                        q.append((u+p-1,n,c.copy(),path+[(p,n-v)]))
                        c=None
                        break
                elif allow(c,p,r):
                    cp=c.copy()
                    cp[p]=(r,cp.get(p,(None,frozenset()))[1])
                    q.append((u+p-1,n,cp,path+[(p,n-v)]))
                    if not forbid(c,p,r):
                        c=None
                        break
            if c is None:break
    return None

def replay(S):
    u,v,path,_,_,kind=shadow(S)
    assert kind=='rough' and 2*(len(path)+1)<=S
    p=int(nextprime(S*S+2*v+20))
    while (p+u-1)%4:p=int(nextprime(p))
    R,mod=0,2
    for q in primerange(3,p+1):
        if q<=S:r=0
        elif q==p:r=(1-u)*pow(2,-1,q)%q
        else:
            forbidden={(e-a)*pow(2,-1,q)%q for a in [x[0] for x in path]+[u] for e in [-1,1]}
            r=next(i for i in range(q) if i not in forbidden)
        R+=mod*((r-R)*pow(mod,-1,q)%q)
        mod*=q
    R+=mod*max(1,(p*p-2*R+2*mod-1)//(2*mod))
    J=2*R
    assert J%4==0 and J+5>=p*p
    h,t=J+4,R+5
    out=[]
    ticks=0
    for n in range(1,2*p+v+10):
        t+=1
        g=gcd(t if t%2==0 else t-2,h-1 if t%2==0 else h+1)
        ticks+=1
        if g>1:
            label=min(factorint(g))
            assert label*label<=h+1
            out.append((h-J,label,t-R))
            h+=label-1
            if h-J>S*S-2:break
    expected=[(a,k,b+w) for a,b,w,k in path]+[(u,p,(u+p-1)//2)]
    assert out==expected and h-J>S*S-2
    assert isprime(u-1) and isprime(u+1)
    return len(out),u,p,ticks,len(str(J))

if __name__=='__main__':
    for S in [10,20,30,50,100,200,500,1000,2000,5000,10000,20000,50000,100000,200000,500000,1000000,2000000,5000000,10000000,100000000,1000000000,10000000000,100000000000,1000000000000]:
        u,v,path,maxd,maxh,kind=shadow(S)
        print('SHADOW',S,u,v,len(path),maxd,maxh,kind)
    for S in [5,7,10,20,30,50,70,100,150,200,300,500,1000,2000]:
        a=solve(S)
        print('BFS',S,a[:4], 'high',[(p,w) for p,w in a[4] if p>S])
    for S in [10,20,30,50,70,100]:
        print('REPLAY',S,replay(S))
