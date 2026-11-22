#!/usr/bin/env python3
"""Exact BAD-terminal last-event clock, Lucas twin-prime and 500-step audits.
Standard library only. No claim of original a(1)=2 reachability or Cap B.
"""
from math import gcd, isqrt, prod

M=12783268038291131701
R=22370719067009480454
GAP=22
K=R+GAP
C=2*R
PRE_INDEX=22370719067009479976
PRE_C=44741434510218131142
LUCAS_CERTS=(
 (M,6,{2:2,3:2,5:2,11:1,17:1,773:1,49411:1,1988633:1}),
 (M-2,2,{2:1,19:1,131:1,167:1,199:1,313:1,246872729:1}),
)

def prime_trial(n):
 if n<2:return False
 if n%2==0:return n==2
 return all(n%p for p in range(3,isqrt(n)+1,2))

def lucas(n,base,fs):
 # Complete elementary Lucas order certificate, not a probable-prime test.
 assert prod(q**k for q,k in fs.items())==n-1
 assert all(prime_trial(q) for q in fs)
 assert pow(base,n-1,n)==1
 assert all(gcd(pow(base,(n-1)//q,n)-1,n)==1 for q in fs)

def inc(n,prior):
 return gcd(n if n%2==0 else n-2,prior-1 if n%2==0 else prior+1)

def factors(n):
 out=[];p=3
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p+=2
 if n>1:out.append(n)
 return out

def frozen_last(K,C):
 times=[]
 for p in factors(C-1):
  n=2*p*(K//(2*p))
  if n>=3:times.append(n)
 for p in factors(C+1):
  n=p+2+2*p*((K-p-2)//(2*p))
  if n>=3:times.append(n)
 r=max(times,default=2)
 assert all(inc(n,C)==1 for n in range(r+1,K+1))
 if r>=3:assert inc(r,C)>1
 return r

def odd_divisors(n):
 while n%2==0:n//=2
 d=[1];p=3
 while p*p<=n:
  if n%p==0:
   powers=[1];a=1
   while n%p==0:n//=p;a*=p;powers.append(a)
   d=[x*y for x in d for y in powers]
  p+=2
 if n>1:d += [x*n for x in d]
 return d

def preds(n,post):
 u=n%2; A=n-2*u; B=post+2*u
 return [(post-e+1,e) for e in odd_divisors(gcd(A,B))
         if post-e+1>=2 and gcd(A//e,B//e-1)==1]

def skeleton(K,C):
 s=frozen_last(K,C)
 return s,[(r,e,pre) for r in range(max(3,s),K+1)
           for pre,e in preds(r,C) if e>1]

def canonical(m):
 K=(7*m-1)//4; C=2*m-2; history={m+2:C}
 for n in range(m+3,K+1):
  C+=inc(n,C)-1;history[n]=C
 return K,C,history

def check_controls():
 for m,k,c,expected,last,count in (
  (13,22,40,18,20,1),(43,75,132,65,66,5),
  (305,533,852,518,527,3)):
  kk,cc,h=canonical(m)
  assert (kk,cc)==(k,c)
  s,branches=skeleton(k,c)
  event_last=max(n for n in range(m+3,k+1)
                 if inc(n,h[n-1])>1)
  assert (s,event_last,len(branches))==(expected,last,count)
  assert any(r==last and pre==h[last-1] for r,e,pre in branches)
 for m,k,c,swant,e in ((101119,176958,236004,176957,3),
                        (100549,175960,241340,175955,5)):
  s,branches=skeleton(k,c)
  assert (s,branches)==(swant,[(k,e,c-e+1)])
 print('PASS five true / impossible BAD last-clock skeleton controls')

def check_lucas_and_local():
 for n,a,fs in LUCAS_CERTS:lucas(n,a,fs)
 assert K==(7*M-1)//4 and 2*M-2<=C<=2*K
 assert R%6==0 and inc(R,C-2)==3
 assert all(inc(n,C)==1 for n in range(R+1,K+1))
 assert (C-1)%47==0 and C-1>47 and (C+1)%53==0 and C+1>53
 assert all(inc(K+j,C)==1 for j in range(1,7))
 assert inc(K+7,C)==53
 assert inc(K-46,C)==47
 assert all(inc(n,C)==1 for n in range(K-45,K+1))
 print('PASS fully proven twin primes; BAD neighbors, 22-unit reset tail, J=K+7')

 h=PRE_C;events=[]
 assert K-PRE_INDEX==500 and 2*PRE_INDEX-PRE_C==3623800828810
 for n in range(PRE_INDEX+1,K+1):
  e=inc(n,h)
  assert e<=M
  if e>1:events.append((n-K,e))
  h+=e-1
  assert 2*M-2<=h<=2*n
 assert h==C and C-PRE_C==3623800829766
 assert events==[(-49,3623800829707),(-34,37),(-29,5),
                 (-28,9),(-26,5),(-22,3),(-8,7)]
 print('PASS independent 500-index genuine-gcd suffix into same artificial BAD cutoff')

def crt(pairs):
 x,Q=0,1
 for p,a in pairs:
  assert gcd(Q,p)==1
  x+=Q*((a-x)*pow(Q,-1,p)%p)
  Q*=p
 return x%Q,Q

def modular_family(g):
 # For all g >=22, g ==1 mod21, there is a CRT-constructed BAD LOCAL
 # cutoff with aligned e=3 reset, g quiet steps, and all input prime
 # tests modulo primes <=2*g+1 admissible. No full input primality claim.
 assert g>=22 and g%21==1
 B=2*g+1
 q1=next(p for p in range(B+1,B+1000) if prime_trial(p))
 q2=next(p for p in range(q1+1,q1+1000) if prime_trial(p))
 z=[(2,0)]
 r7=next(v for v in range(0,49,7)
         if ((4*(v+g)+3)//7)%7 not in (0,2))
 z.append((49,r7))
 for p in range(3,B+1,2):
  if p==7 or not prime_trial(p):continue
  valid=[v for v in range(p)
         if (2*v-1)%p and (2*v+1)%p
         and ((4*(v+g)+3)*pow(7,-1,p)%p) not in (0,2)]
  assert valid,(p,g)
  z.append((p,valid[0]))
 z.extend([(q1,pow(2,-1,q1)),(q2,-pow(2,-1,q2))])
 r,Q=crt(z)
 if r==0:r+=Q
 while r<100*g:r+=Q
 k=r+g; m=(4*k+3)//7; c=2*r
 assert k==(7*m-1)//4 and 2*m-2<=c<=2*k
 assert inc(r,c-2)==3
 assert all(inc(n,c)==1 for n in range(r+1,k+1))
 assert (c-1)%q1==0 and c-1>q1 and (c+1)%q2==0 and c+1>q2
 assert all(m%p not in (0,2) for p in range(3,B+1,2)
            if prime_trial(p))
 print('PASS CRT modular BAD family g',g,'digits(K)',len(str(k)),
       'screened primes <=',B)

if __name__=='__main__':
 check_controls()
 check_lucas_and_local()
 for g in (22,43,106):modular_family(g)
 print('PASS all finite certificates; Cap B and infinitude OPEN')
