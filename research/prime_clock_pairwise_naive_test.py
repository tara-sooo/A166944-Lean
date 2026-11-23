#!/usr/bin/env python3
"""Check whether a naive sum of exact two-prime stopping times is Lyapunov."""
from itertools import combinations

def graph(ps):
    P=1
    for p in ps:P*=p
    N=2*P*P
    nxt=[-1]*N; gaps=[0]*N
    for t in range(2*P):
        for h in range(P):
            C=2*h
            w=[]
            for p in ps:
                if (C-1)%p==0:r=0
                elif (C+1)%p==0:r=p+2
                else:continue
                w.append(((r-t)%(2*p) or 2*p,p))
            if not w:continue
            g=min(x[0] for x in w)
            d=1
            for z,p in w:
                if z==g:d*=p
            i=t*P+h
            nxt[i]=((t+g)%(2*P))*P+((h+(d-1)//2)%P)
            gaps[i]=g
    status=bytearray(N);dur=[0]*N
    for x in range(N):
        if status[x]:continue
        path=[];z=x
        while z!=-1 and status[z]==0:
            status[z]=1;path.append(z);z=nxt[z]
        assert z==-1 or status[z]==2,"cycle"
        for u in reversed(path):
            dur[u]=gaps[u]+(dur[nxt[u]] if nxt[u]!=-1 else 0)
            status[u]=2
    return P,nxt,gaps,dur

def main():
    ps=(3,5,7)
    pairs={pq:graph(pq) for pq in combinations(ps,2)}
    P,nxt,gaps,dur=graph(ps)
    def pot(i):
        t,h=divmod(i,P)
        return sum(pair[3][(t%(2*pair[0]))*pair[0]+h%pair[0]] for pair in pairs.values())
    count=0;worst=0;witness=None
    for i,j in enumerate(nxt):
        if j<0:continue
        loss=pot(i)-pot(j)
        deficit=gaps[i]-loss
        if deficit>0:
            count+=1
            if deficit>worst:worst=deficit;witness=(divmod(i,P), gaps[i], loss, divmod(j,P), dur[i])
    print('PAIR_EXACT_TIME_FAIL states=',2*P*P,'live=',sum(j>=0 for j in nxt),'violations=',count,'maxDeficit=',worst,'witness=',witness)
    assert count==5183 and worst==32
if __name__=='__main__':main()
