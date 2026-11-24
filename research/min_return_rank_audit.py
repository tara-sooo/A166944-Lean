from math import isqrt, ceil, log, gcd
from collections import Counter
import sys


def rank(A,k):
    A=[r[:] for r in A]; i=0; prev=1
    for j in range(k):
        b=next((b for b in range(i,len(A)) if A[b][j]),None)
        if b is None: continue
        A[i],A[b]=A[b],A[i]; p=A[i][j]
        for b in range(i+1,len(A)):
            for c in range(j+1,k):
                a=A[b][c]*p-A[b][j]*A[i][c]
                assert a%prev==0
                A[b][c]=a//prev
            A[b][j]=0
        prev=p; i+=1
        if i==len(A): break
    return i


def run(X):
    B=isqrt(7*X-1)+1; Q=ceil(B/log(B)**.125); mid=isqrt(B-1)+1
    spf=list(range(7*X+4))
    for p in range(2,isqrt(len(spf)-1)+1):
        if spf[p]==p:
            for j in range(p*p,len(spf),p):
                if spf[j]==j: spf[j]=p
    def hit(t,C,K):
        best=(K+1,0)
        for s in (-1,1):
            n=C+s
            while n>1:
                p=spf[n]
                if p>B: break
                a=0 if s==-1 else p+2
                u=t+1+(a-t-1)%(2*p)
                best=min(best,(u,p))
                while n%p==0: n//=p
        return best
    def literal(t,C,K):
        for u in range(t+1,K+1):
            g=gcd(u-2 if u%2 else u,C+1 if u%2 else C-1)
            if g>1 and spf[g]<=B: return u,spf[g]
        return K+1,0
    R=0; E=0; H=0; mass=Counter(); stats={}; cover={}
    cuts=(11,mid,Q); lengths=(5,8,16,32)
    for n in lengths:
        for q in cuts: stats[n,q]=Counter(); cover[n,q]=set()
    for M in range(X+1,2*X,2):
        t=M+2; C=2*M-2; K=(7*M-1)//4; v=[]; h=[]
        while True:
            u,p=hit(t,C,K)
            if X<=1024: assert (u,p)==literal(t,C,K)
            if not p: break
            r=min(spf[C-1],spf[C+1]); s=1 if u%2 else -1
            assert (C+s)%p==0 and u-t<=2*r
            mass[C]+=r; R+=r; E+=1
            if p>7: h.append(len(v)); H+=1
            v.append((C,p,s)); t=u; C+=p-1; assert C<=2*t
        for n in lengths:
            for a in range(len(h)-n+1):
                w=[v[h[j]] for j in range(a,a+n)]; ps=list(dict.fromkeys(x[1] for x in w)); k=len(ps); lo=min(ps)
                ids=[ps.index(x[1]) for x in w]; last={}; rows=[]; reach=[1<<i for i in range(k)]
                for j,i in enumerate(ids):
                    if i in last:
                        l=last[i]; row=[0]*k
                        for z in ids[l:j]: row[z]+=1; reach[i]|=1<<z
                        d=w[j][0]-w[l][0]+w[j][2]-w[l][2]; assert d%ps[i]==0
                        row[i]-=d//ps[i]; rows.append(row)
                    last[i]=j
                for i in range(k):
                    for j in range(k):
                        if reach[j]>>i&1: reach[j]|=reach[i]
                sinks=sum(all(not(reach[i]>>j&1) or reach[j]>>i&1 for j in range(k)) and all(not(reach[i]>>j&1 and reach[j]>>i&1) for j in range(i)) for i in range(k))
                r=rank(rows,k); assert r<=min(k,n-k)
                good=k>=2 and r>=k-1; one=k>=2 and sinks==1
                for q in cuts:
                    if lo<q: continue
                    c=stats[n,q]; c['windows']+=1; c['highrank']+=good; c['fullrank']+=r==k; c['no_repeat']+=not rows
                    c['singleton_le1']+=sum(f==1 for f in Counter(ids).values())<=1
                    c['one_sink']+=one; c['one_sink_highrank']+=one and good
                    if good: cover[n,q].update(v[j][0] for j in range(h[a],h[a+n-1]+1))
    print(f'X={X} B={B} Q={Q} mid={mid} R={R} events={E} high={H}',flush=True)
    for (n,q),c in stats.items():
        print(n,q,dict(c), 'horizons',len(cover[n,q]),'union_R',sum(mass[C] for C in cover[n,q]),flush=True)


if __name__=='__main__':
    for arg in sys.argv[1:]: run(int(arg))
