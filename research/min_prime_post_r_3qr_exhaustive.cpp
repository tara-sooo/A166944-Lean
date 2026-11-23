// Exhaust ALL post-r clock-residue states of MIN wheel {3,q,r}, 3<q<r.
// State count is 18*q*q, independent of r: post-r time must be an r calendar
// slot and post-r C mod r is 0 (even time) or -2 (odd time).
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_post_r_3qr_exhaustive.cpp -o /tmp/postr
// /tmp/postr 101 103
#include <algorithm>
#include <climits>
#include <cstdlib>
#include <iostream>
using namespace std;
struct Result{int events=0,high=0,rhits=0,qhits=0,time=0;bool guard=false;};
int main(int argc,char**argv){
 if(argc<3)return 2;
 const int q=atoi(argv[1]),r=atoi(argv[2]);if(q<=3||r<=q||r%2==0||q%2==0)return 2;
 const int ps[3]={3,q,r};int T[3],C[3];Result peak;
 long long count=0,twiceR=0,thriceQ=0,guards=0;int witnessK=0,witnessH=0;
 for(int parity=0;parity<2;parity++)for(int k=0;k<3*q;k++){
  const int t0=(parity==0?0:r+2)+2*r*k;
  for(int h=0;h<3*q;h++){
   T[0]=t0%6;T[1]=t0%(2*q);T[2]=t0%(2*r);
   C[0]=(2*h)%3;C[1]=(2*h)%q;C[2]=parity==0?0:r-2;
   Result z;
   for(int step=0;step<500;step++){
    int g=INT_MAX,choose=-1;
    for(int j=0;j<3;j++){
     int p=ps[j],target=C[j]==1?0:C[j]==p-1?p+2:-1;
     if(target<0)continue;
     int dt=(target-T[j]+2*p)%(2*p);if(dt==0)dt=2*p;
     if(dt<g||(dt==g&&j<choose)){g=dt;choose=j;}
    }
    if(choose<0)break;
    z.events++;z.time+=g;
    if(choose){z.high++;if(choose==1)z.qhits++;else z.rhits++;}
    for(int j=0;j<3;j++){
     C[j]=(C[j]+ps[choose]-1)%ps[j];T[j]=(T[j]+g)%(2*ps[j]);
    }
    if(step==499)z.guard=true;
   }
   count++;if(z.rhits>=2)twiceR++;if(z.qhits>=3)thriceQ++;if(z.guard)guards++;
   if(z.high>peak.high||(z.high==peak.high&&z.time>peak.time)){
    peak=z;witnessK=k;witnessH=h;
   }
  }
 }
 cout<<"MIN_POST_R_EXACT q="<<q<<" r="<<r<<" states="<<count
  <<" guard500="<<guards<<" statesWith2FurtherR="<<twiceR
  <<" statesWith3Q="<<thriceQ<<" maxEvents="<<peak.events
  <<" maxHigh="<<peak.high<<" maxAdditionalR="<<peak.rhits
  <<" maxQ="<<peak.qhits<<" maxTime="<<peak.time
  <<" witnessK="<<witnessK<<" witnessH="<<witnessH<<"\n";
 if(count!=18LL*q*q)return 3;
 return guards?4:0;
}
