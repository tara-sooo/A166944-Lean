from math import gcd, isqrt, lcm, sqrt
from functools import lru_cache

def prime(n):
 if n<2:return False
 if n%2==0:return n==2
 return all(n%p for p in range(3,isqrt(n)+1,2))
def factors(n):
 out=[];p=3
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=2
 if n>1:out.append(n)
 return out

def inc(n,C):return gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)

def run_can(M):
 s=M+2; K=(7*M-1)//4; C=2*M-2; hits=[]; gaps=[]; previous=s
 for n in range(s+1,K+1):
  e=inc(n,C)
  if e>1:
   gaps.append((n-previous,previous,C));previous=n
   C+=e-1;hits.append((n,e,C))
 gaps.append((K-previous,previous,C))
 bad=not (prime(C-1) and prime(C+1))
 h=isqrt(2*K+1)
 L=sqrt(M)/4
 k=sum(g>=L for g,_,_ in gaps)
 if bad:
  assert all(g<=2*h for g,_,_ in gaps)
  T=K-s
  assert T<=2*h*k+L*(len(gaps)-k)+1e-9
  assert k>=max(0,(T-L*len(gaps))/(2*h-L))-1e-9
  assert len(gaps)>=T/(2*h)-1e-9
 for g,st,c in gaps:
  if g<=0:continue
  pf=factors(c-1)+factors(c+1)
  assert all(p*2>=g for p in pf),(M,g,st,c,pf)
  if bad and M>=4_000_000 and g>=L:
   assert all(p>=sqrt(M)/8 for p in pf)
   assert len(factors(c-1))<=2 and len(factors(c+1))<=2
 return bad,len(hits),len(gaps),k,C

badcases=[]
for M in range(7,2001,2):
 bad,N,m,rough,C=run_can(M)
 if bad:badcases.append((M,N,m,rough,C))
assert [x[0] for x in badcases]==[11,13,23,25,39,41,43,45,305],badcases
print('All synthetic M<=2000: exact BAD gap packing & prime clock roughness pass; BAD',badcases)

# A large synthetic GOOD start: the roughness test also applies to quiet tails.
large_result=run_can(4_000_001)
assert not large_result[0] and large_result[1]==12 and large_result[3]>=1
print('Large synthetic M=4,000,001: GOOD, N=',large_result[1], 'long gaps=',large_result[3])

# Original full trace
C=1;ev=[]
for n in range(2,2500001):
 e=inc(n,C)
 if e>1:
  C+=e-1
  ev.append((n,e,C))
assert len(ev)==250 and C==2860770
E={n:(e,c) for n,e,c in ev}
assert E[356268][1]==712530 and E[356624][0]==719
assert all(inc(n,712530)==1 for n in range(356269,356624))
assert inc(356624,712530)==719
assert factors(712529)==[719,991]
assert factors(712531)==[712531]
assert all((x-1)%3 !=0 and (x+1)%3!=0 for x in [712530])

@lru_cache(None)
def wheelmod(h):
 r=1
 for e in range(1,h+2,2):r=lcm(r,e)
 return r

def wheel(s,C,v,h):
 mod=wheelmod(h); tot=0; seq=[]
 for n in range(s+1,v+1):
  e=gcd(inc(n,C),mod)
  if e>1:C+=e-1;tot+=e-1;seq.append((n,e))
 return tot,seq
assert wheel(356268,712530,356624,8)==(0,[])
assert wheel(66,132,150,58)==(6,[(79,7)])
assert wheel(66,132,150,168)==(168,[(79,7),(141,139),(150,25)])
print('Witness: 356268,C=712530, first hit 356624 e=719; h=8 wheel remains 0; 66..150 CRT small-budget false')

# Second genuine CRT + forced large first-hit certificate.
assert E[1339][1]==2658 and E[2661][0]==2659 and E[2674][1]==5334
assert prime(2657) and prime(2659)
assert all(inc(n,2658)==1 for n in range(1340,2661))
assert inc(2661,2658)==2659
assert wheel(1339,2658,2674,16)==(0,[])
assert (2676-16)%70==0 and 2676<=2690
print('Genuine [1339,2674]: CRT 16(mod 70), wheel16=0, first hit e=2659, forced H=2676')
print('PASS: BAD-path multiscale gap sieve and first-hit/CRT certificates')
