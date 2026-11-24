#!/usr/bin/env python3
from math import gcd, isqrt, ceil, log
import sys

def run(X):
    B=isqrt(7*X-1)+1;Q=ceil(B/log(B)**(1/3))
    spf=list(range(7*X+4))
    for p in range(2,isqrt(len(spf)-1)+1):
        if spf[p]==p:
            for z in range(p*p,len(spf),p):
                if spf[z]==z:spf[z]=p
    paths=[];sample=None;res=dict(reversal=0,far=0,weightedFar=0,samePrev=0,samePrevFar=0,large=0,largeFar=0)
    for M in range(X+1,2*X,2):
        t,C,K=M+2,2*M-2,(7*M-1)//4;v=[]
        while True:
            hit=None
            for n in range(t+1,K+1):
                g=gcd(n if n%2==0 else n-2,C-1 if n%2==0 else C+1)
                if g>1 and spf[g]<=B:hit=(n,spf[g]);break
            if hit is None:break
            n,p=hit;v.append((C,t,p,n));t=n;C+=p-1
        paths.append(v)
    for i,a in enumerate(paths):
        aa={x[0]:j for j,x in enumerate(a) if 0<j<len(a)-1}
        for l in range(i+1,len(paths)):
            b=paths[l];bb={x[0]:j for j,x in enumerate(b) if 0<j<len(b)-1};far=2*(l-i)>B
            for C in aa.keys()&bb.keys():
                j,k=aa[C],bb[C]
                x,y=a[j],b[k];xx,yy=a[j+1],b[k+1]
                if x[2]!=y[2] or xx[2]!=yy[2]:continue
                h=y[1]-x[1];h1=y[3]-x[3];h2=yy[3]-xx[3]
                if h==0 or h1==h or h2!=h:continue
                assert h*h1>0
                res['reversal']+=2
                if far:
                    res['far']+=2;res['weightedFar']+=2*(min(spf[C-1],spf[C+1])+min(spf[xx[0]-1],spf[xx[0]+1]))
                if a[j-1][2]==b[k-1][2]:
                    res['samePrev']+=2
                    if far:res['samePrevFar']+=2
                    if a[j-1][2]>=Q and xx[2]>=Q:
                        assert abs(h)<2*Q*Q and a[j-1][2]==xx[2]
                        res['large']+=2
                        if far:res['largeFar']+=2
                if sample is None:sample=(X+1+2*i,X+1+2*l,C,h,h1,h2,x[2],xx[2])
    print(X,res,'sample(M,M2,C,h,h1,h2,p,q)=',sample)
if __name__=='__main__':
    for x in map(int,sys.argv[1:]):run(x)
