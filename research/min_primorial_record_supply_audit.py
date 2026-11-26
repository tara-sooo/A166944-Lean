"""Exact finite audits of the reset displacement theorem.
Run: python min_primorial_record_supply_audit.py [seed bound] [ray cap]
Requires sympy. The seed scan starts at every genuine twin-derived reset,
not only states reachable on the distinguished universal ray.
"""
from math import isqrt
from array import array
from functools import lru_cache
from sys import argv
from sympy import factorint, isprime

@lru_cache(None)
def big_factors(n):
    return tuple(sorted(map(int, factorint(n))))

def spf_table(limit):
    a=array('I', [0])*(limit+1)
    for p in range(3,isqrt(limit)+1,2):
        if a[p]==0:
            for n in range(p*p,limit+1,2*p):
                if a[n]==0:a[n]=p
    return a

def factors(n,a):
    if n>=len(a):return big_factors(n)
    out=[]
    while n>1:
        p=a[n] or n
        out.append(p)
        while n%p==0:n//=p
    return out

def step(u,v,a):
    return min((((0 if e==1 else p+2)-v)%(2*p) or 2*p,p,e)
               for e in (1,-1) for p in factors(u-e,a))

def block(r,a,cap=100000):
    X=2*r-2;u=X;v=r+2;m=0;maxd=6;maxratio=(0,1);prev=None
    while m<cap:
        w,p,e=step(u,v,a);d=2*v-u;G=u-X
        assert 3*(d-6)<=13*G
        if G and (d-6)*maxratio[1]>maxratio[0]*G:maxratio=(d-6,G)
        if p>r:
            twin=len(factors(u-1,a))==1 and (a[u-1]==0 if u-1<len(a) else isprime(u-1)) and len(factors(u+1,a))==1 and (a[u+1]==0 if u+1<len(a) else isprime(u+1))
            if not twin:
                assert p==u+1 or 3*p<=u+1
                if p==u+1:
                    assert d>=u-2*isqrt(u-1)-2
                    # 10G >= 3X - 6sqrt(u-1)-24, using floor sqrt
                    assert 10*G>=3*X-6*isqrt(u-1)-24
                else:assert G>=r+7
                assert 16*(m+1)**2*(2*r-1)>=(r-5)**2
                A,B,c=4*r-3,2*r+5,2*(m+1)
                if A>B+c*c:assert (A-B-c*c)**2<=4*c*c*B
            return (r,m+1,G,u,p,bool(twin),maxd,maxratio)
        A,B=2*(v+w)+1,2*v+1
        if A>B+4:assert (A-B-4)**2<16*B
        if p==3 and w==6:assert prev is not None and prev>=5
        prev=p
        u+=p-1;v+=w;m+=1;maxd=max(maxd,2*v-u)
    return None

def main(seed_limit,ray_cap):
    a=spf_table(4*seed_limit+10000)
    seeds=[];incomplete=0
    for r in range(7,seed_limit+1,6):
        if a[r]==0 and a[r-2]==0:
            row=block(r,a)
            if row is None:incomplete+=1
            else:seeds.append(row)
    print('seed limit',seed_limit,'complete',len(seeds),'incomplete',incomplete,'non-twin records',sum(not x[5] for x in seeds))
    print('seed first false records',[x for x in seeds if not x[5]][:10])
    print('seed max event count',max(seeds,key=lambda x:x[1]))
    for cutoff in [7,1000,10000,100000]:
        rows=[x for x in seeds if x[0]>=cutoff]
        if rows:
            print('seed min r',cutoff,'max relative progress',max(rows,key=lambda x:x[2]/(2*x[0]-2)),'max m/sqrt(r)',max(rows,key=lambda x:x[1]/x[0]**.5))
    u,v=4,5;record=0;records=[];events=0
    while u<=ray_cap:
        w,p,e=step(u,v,a)
        if p>record:
            if record>=7 and records[-1][1]==records[-1][0]+1:
                z=block(record,a)
                assert z is not None and z[3]==u and z[4]==p
                records[-1]=records[-1]+(z,)
            records.append((u,p,events));record=p
        u+=p-1;v+=w;events+=1
    blocks=[x[3] for x in records if len(x)==4]
    print('ray cap',ray_cap,'events',events,'records',len(records),'complete reset blocks',len(blocks),'false',sum(not x[5] for x in blocks))
    print('ray last block',blocks[-1])
    print('ray max m',max(blocks,key=lambda x:x[1]))
    print('ray max ratio from r>=1000',max((x for x in blocks if x[0]>=1000),key=lambda x:x[2]/(2*x[0]-2)))
    print('ray last 8',blocks[-8:])

if __name__=='__main__':main(int(argv[1]) if len(argv)>1 else 10**6,int(argv[2]) if len(argv)>2 else 10**18)
