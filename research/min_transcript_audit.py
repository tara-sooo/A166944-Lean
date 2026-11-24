from math import isqrt
from collections import defaultdict
import sys

def audit(X):
    B=isqrt(7*X-1)+1
    primes=[p for p in range(3,B+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]
    sources=list(range(X+1,2*X,2))
    def next_clock(M,G,s,p):
        C=2*M-2+G; t=M+2+s
        if (C-1)%p==0: r=0
        elif (C+1)%p==0: r=p+2
        else: return None
        return s+1+(r-t-1)%(2*p)
    def run(M):
        G=s=0; word=[]
        for _ in range(8):
            candidates=[(v,p) for p in primes if (v:=next_clock(M,G,s,p)) is not None]
            if not candidates: break
            v,p=min(candidates)
            if M+2+v>(7*M-1)//4: break
            word.append((v,p)); G+=p-1;s=v
        return tuple(word)
    paths={M:run(M) for M in sources}
    total=0; maxsize=0
    for j in (1,2,4,8):
        cells=defaultdict(set)
        for M,w in paths.items():
            if len(w)>=j: cells[w[:j]].add(M)
        for word,actual in cells.items():
            A={p:set(range(p)) for p in primes};G=s=0
            seen=set()
            for v,q in word:
                for p in primes:
                    old=A[p].copy()
                    for a in old:
                        M=a if a%2 else a+p
                        w=next_clock(M,G,s,p)
                        if p==q:
                            if w!=v:A[p].remove(a)
                        elif w is not None and (w,p)<(v,q):A[p].remove(a)
                    if p!=q:assert len(old)-len(A[p])<=2
                seen.add(q);G+=q-1;s=v
            assert all(len(A[p])==1 for p in seen)
            assert all(len(A[p])>=max(0,p-2*j) for p in primes if p not in seen)
            predicted={M for M in sources if 3*M>=9+4*s and all(M%p in A[p] for p in primes)}
            assert actual==predicted,(X,j,word,actual,predicted)
            total+=1;maxsize=max(maxsize,len(actual))
        print(f'X={X} j={j} cells={len(cells)} sources={sum(map(len,cells.values()))}')
    print(f'X={X} checked={total} max_cell={maxsize}')

if __name__=='__main__':
    for arg in sys.argv[1:]:audit(int(arg))
