// Exact squarefree clipped parity-GCD: minimal-prime event ownership/time ledger.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_minimum_clock_audit.cpp -o /tmp/min_clock
// /tmp/min_clock 256 512 1024 4096 16384 65536 262144
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int>spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
static void factor(int n,vector<int>&f){f.clear();while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}}
static int clock_gap(ll t,int p,int r){int v=int((r-t)%(2LL*p));return v>0?v:v+2*p;}
struct Stats {ll W=0,events=0,travel=0,firstGap=0,repeatGap=0;
 ll minFirstP=0,minRepeatP=0,allFirstP=0,allRepeatP=0;
 ll minFirstPminus1=0,minRepeatPminus1=0,maxGap=0,maxGapRatioP=0;
 ll good=0,bad=0,terminalCertified=0,lowMin3Repeat=0,compositeEvents=0;
 ll minZ=0,minZreturn=0,minF=0,maxMinHits=0,minZ3=0;
};
static void audit(int X){
 int B=int(ceill(sqrtl(7.L*X)));
 Stats z;vector<int>f,minHits(B+1,0),allHits(B+1,0),minTouched,allTouched;
 for(int M=X+1;M<2*X;M+=2){
   ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4,S=t;
   minTouched.clear();allTouched.clear();
   while(t<K){
     ll n=K+1;
     factor(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,0));
     factor(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));
     if(n>K)break;
     const int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
     factor(raw,f);
     int d=1,least=0,omega=0;
     for(int p:f)if(p<=B){if(!least)least=p;d*=p;++omega;
       if(allHits[p]++==0)allTouched.push_back(p);
     }
     if(d<=1||least<3)throw runtime_error("event mismatch");
     const ll gap=n-t;
     if(gap>2LL*least)throw runtime_error("minimum-prime clock exceeded");
     z.maxGap=max(z.maxGap,gap);z.maxGapRatioP=max(z.maxGapRatioP,1000*gap/least);
     z.events++;z.compositeEvents+=omega>=2;
     z.travel+=gap;
     if(minHits[least]++==0){minTouched.push_back(least);
       z.minFirstP+=least;z.minFirstPminus1+=least-1;z.firstGap+=gap;
     }else{z.minRepeatP+=least;z.minRepeatPminus1+=least-1;z.repeatGap+=gap;
       if(least==3)++z.lowMin3Repeat;
     }
     z.W+=d-1;
     C+=d-1;t=n;S=n;
     if(C>2*n)throw runtime_error("horizon invariant");
   }
   for(int p:allTouched){z.allFirstP+=p;z.allRepeatP+=ll(p)*(allHits[p]-1);allHits[p]=0;}
   for(int p:minTouched){
     const ll count=minHits[p];z.minZ+=count*count;z.minZreturn+=(count-1)*(count-1);++z.minF;
     if(p==3)z.minZ3+=count*count;
     z.maxMinHits=max(z.maxMinHits,count);
     minHits[p]=0;
   }
   if(S-(M+2)>3*(C-(2LL*M-2)))throw runtime_error("old growth clock bound");
   const bool twin=(spf.at(int(C-1))==C-1&&spf.at(int(C+1))==C+1);
   z.good+=twin;z.bad+=!twin;
   if(K-S>=2*B){
     if(!twin)throw runtime_error("sqrt terminal twin certificate false");
     ++z.terminalCertified;
   }
 }
 if(z.minZreturn!=z.minZ-2*z.events+z.minF||
    z.travel!=z.firstGap+z.repeatGap||z.travel>2*(z.minFirstP+z.minRepeatP)||
    z.minRepeatP>z.allRepeatP||z.good+z.bad!=X/2)throw runtime_error("min clock ledger mismatch");
 const ll horizon=9LL*X*X/16-5LL*X/4;
 if(horizon<z.travel)throw runtime_error("last event after cutoff");
 cout<<"MIN_CLOCK_PASS X="<<X<<" B="<<B<<" events="<<z.events
   <<" W="<<z.W<<" travel="<<z.travel<<" horizon="<<horizon
   <<" firstMinP="<<z.minFirstP<<" repeatMinP="<<z.minRepeatP
   <<" firstMinPminus1="<<z.minFirstPminus1
   <<" repeatMinPminus1="<<z.minRepeatPminus1
   <<" firstTime="<<z.firstGap<<" repeatTime="<<z.repeatGap
   <<" allFirstP="<<z.allFirstP<<" allRepeatP="<<z.allRepeatP
   <<" good="<<z.good<<" bad="<<z.bad<<" certified="<<z.terminalCertified
   <<" min3RepeatedEvents="<<z.lowMin3Repeat
   <<" composites="<<z.compositeEvents
   <<" minF="<<z.minF<<" minZ="<<z.minZ<<" minZreturn="<<z.minZreturn<<" minZ3="<<z.minZ3
   <<" maxMinHits="<<z.maxMinHits
   <<" minZoverXB="<<double(z.minZ)/(double(X)*B)
   <<" minZoverXBLogB="<<double(z.minZ)/(double(X)*B*log(double(B)))
   <<" minZreturnOverXBLogB="<<double(z.minZreturn)/(double(X)*B*log(double(B)))
   <<" repeatMinOverX2="<<double(z.minRepeatP)/(double(X)*X)
   <<" repeatTimeOverX2="<<double(z.repeatGap)/(double(X)*X)
   <<" maxGap="<<z.maxGap<<" maxGapPerPtimes1000="<<z.maxGapRatioP<<"\n";
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 int maxX=0;for(int i=1;i<argc;i++){
   const int X=atoi(argv[i]);if(X<256||X>262144||X%4)return 2;
   maxX=max(maxX,X);
 }
 sieve(8*maxX+1000);
 for(int i=1;i<argc;i++)audit(atoi(argv[i]));
}