#!/usr/bin/env python3
"""Tests interleaving-robust low-offset high-prime-return bounds on exact gcd paths.
Mathematical proof needs only offset identity and first-hit divisibility;
this is a finite audit, not a proof of universal Cap B.
"""
from math import gcd

CASES={
 45895573: ((2,5),(1,3),(106,73),(15,19),(147,151),(34,53),(4,3),(3,5),(3,3),(30,17),(6,3),(3,77),(3,3),(8,5),(4,3),(4,23),(2,3),(10,5),(2,3),(7,13),(2,7),(2,11),(1,3),(90,47),(6,3),(3,13),(338,229),(19,31),(3,7),(7,5),(2,3),(68,83),(4,3),(2,53),(4,3),(11,977),(1,3)),
 5875882249: ((9,5),(6,3),(39,103),(2,5),(1,9),(2,5),(4,3),(106,73),(1,11),(1,3),(8,5),(4,3),(9,13),(4,5),(5,177),(5,5),(1,3),(45145,30097),(7,5),(4,9),(43,29),(3,5),(1,3),(1,3),(5,5),(1,3))
}

def at(r,C):return gcd(r if r%2==0 else r-2,C-1 if r%2==0 else C+1)

def audit(M,word):
 s,C=M+2,2*M-2; arr=[]
 K=(7*M-1)//4
 for i,(g,e) in enumerate(word,1):
  r=s+g;before=2*s-C;after=2*r-(C+e-1)
  assert r<=C and r<=K and after>=0 and e%2==1
  assert at(r,C)==e,(M,i,r,C,e)
  for j in range(s+1,r):assert at(j,C)==1,(M,i,j,C)
  h=e-1<3*(g+1)
  if h:assert e-1<=4*g
  assert after == before+2*g-e+1
  if e>=13 and g>10 and h and before<=10:
   assert after in (0,6,2*e,2*e+6),(M,i,e,before,after)
  arr.append(dict(i=i,g=g,e=e,x=before,y=after,h=h,r=r,C=C))
  s,C=r,C+e-1
 G=sum(z['e']-1 for z in arr);H=sum((z['e']-1) for z in arr if z['h'])
 assert C==2*M-2+G
 i=0;jump=0;groups=[]
 while i<len(arr):
  a=arr[i]
  if a['x']<=10 and a['g']>10 and a['h'] and a['e']>=13 and a['y']>=2*a['e']:
   p=a['e'];j=next((j for j in range(i+1,len(arr)) if arr[j]['y']<=10),None)
   if j is None:
    groups.append((a['i'],p,'unfinished',a['x'],a['y']))
    break
   tail=arr[i+1:j+1]
   ft=sum(z['e']-1 for z in tail if not z['h'])
   ht=sum(z['e']-1 for z in tail if z['h'])
   assert 2*ft+ht>=2*(2*p-10),(M,p,ft,ht)
   groups.append((a['i'],p,arr[j]['i'],ft,ht))
   jump+=p-1
   i=j+1
  else:i+=1
 complete=[z for z in groups if z[2]!='unfinished'];N=len(complete)
 assert 5*jump<=2*G-H+16*N
 print('M',M,'events',len(arr),'G',G,'H',H,'completed low-high-return groups',complete,'unfinished', [z for z in groups if z[2]=='unfinished'])
 print(' completed jump-H',jump,'global budget',2*G-H+16*N,'<= check',5*jump)
 return arr

def low_prime_branch_bounds(M):
 K=(7*M-1)//4;Cmax=2*K
 high=max(p for p in range(13,32000,2) if p*(3*p-11)<=4*(Cmax+1))
 low=max(p for p in range(13,40000,2) if p*(p-11)<=4*(Cmax+1))
 assert (M,K,high,low)==(45895573,80317252,14635,25353)
 print('threshold M',M,'K',K,'low-X long H high-branch p<=',high,'low-branch p<=',low)

def main():
 for M,word in CASES.items():audit(M,word)
 low_prime_branch_bounds(45895573)
 print('PASS: local gcd, branch normal form, all completed excursions and global ledger.')
 print('Global bound on H/Cap B still OPEN.')
if __name__=='__main__':main()
