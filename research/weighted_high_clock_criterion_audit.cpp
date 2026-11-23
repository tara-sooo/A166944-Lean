// Exact parity-specific original squarefree-GCD high event clock-cost audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror weighted_high_clock_criterion_audit.cpp -o audit
// ./audit 4096 16384 65536 262144 1048576
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
static void sieve(int z){spf.resize(z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<z;p++)if(spf[p]==p)for(int x=p*p;x<z;x+=p)if(spf[x]==x)spf[x]=p;}
static void factors(int n,vector<int>&v){v.clear();while(n>1){int q=spf.at(n);v.push_back(q);do{n/=q;}while(n%q==0);}}
static ll clock_gap(ll t,int q,int r){ll d=(r-t)%(2LL*q);if(d<=0)d+=2*q;return d;}
static ll direct_growth(int M,int B){ll c=2LL*M-2,c0=c,K=(7LL*M-1)/4;vector<int>f;for(ll n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(g,f);int d=1;for(int p:f)if(p<=B)d*=p;c+=d-1;}return c-c0;}
static ll jump_growth(int M,int B){ll c=2LL*M-2,c0=c,t=M+2,K=(7LL*M-1)/4;vector<int>f;while(t<K){ll n=K+1;factors(int(c-1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,0));factors(int(c+1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));if(n>K)break;int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(g,f);int d=1;for(int p:f)if(p<=B)d*=p;c+=d-1;t=n;}return c-c0;}
static void run(int X){
 const int B=int(ceill(sqrtl(7.L*X)));
 ll T=0,P=0,allPrimeWeight=0,Hsum=0,fullSink=0,maxCost=0,W=0;
 ll jumpGapMax=0,sourceCount=0;
 array<ll,5> bandEvents{},bandPrimeMass{};
 vector<int>f;
 for(int M=X+1;M<2*X;M+=2){
   const ll start=M+2,K=(7LL*M-1)/4;ll c=2LL*M-2,t=start,lastHigh=start;
   ll ownT=0,ownP=0;
   Hsum+=K-start;
   while(t<K){
     ll n=K+1;
     factors(int(c-1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,0));
     factors(int(c+1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));
     if(n>K)break;
     const int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));
     factors(g,f);int d=1,pMin=B+1;ll factorWeight=0;
     for(int p:f)if(p<=B){d*=p;if(p>=13){pMin=min(pMin,p);factorWeight+=p;}}
     if(d==1)throw runtime_error("event expected nonunit");
     // The cutoff at n-1 is an actual no-sink prefix: C is frozen and the n-th clock is active.
     // Check the stronger global time bound on every prefix using only high events BEFORE n.
     const ll prefixEnd=n-1;
     if(prefixEnd-start>133*ownT+2*ownP+133+2LL*B)
       throw runtime_error("weighted no-sink PREFIX clock budget fails");
     if(pMin<=B){
       const ll elapsed=n-lastHigh;
       if(elapsed>133+2LL*pMin)throw runtime_error("weighted high-to-high gap failed");
       lastHigh=n;ownT++;ownP+=pMin;
       T++;P+=pMin;allPrimeWeight+=factorWeight;
       const int band=(pMin<=B/16?0:pMin<=B/8?1:pMin<=B/4?2:pMin<=B/2?3:4);
       bandEvents[band]++;bandPrimeMass[band]+=pMin;
       jumpGapMax=max(jumpGapMax,elapsed);
     }
     W+=d-1; c+=d-1;t=n;
   }
   maxCost=max(maxCost,133*ownT+2*ownP);
   factors(int(c-1),f);bool active=false;for(int p:f)if(p<=B)active=true;
   factors(int(c+1),f);for(int p:f)if(p<=B)active=true;
   if(!active)fullSink++;
   else if(K-start>133*ownT+2*ownP+133+2LL*B)
     throw runtime_error("weighted no-sink original cutoff fails");
   sourceCount++;
 }
 if(sourceCount!=X/2)throw runtime_error("source count");
 const ll expected=9LL*X*X/16-5LL*X/4;
 if(Hsum!=expected)throw runtime_error("exact dyadic horizon sum wrong");
 if((X==4096&&W!=399142)||(X==16384&&W!=2915326)||(X==65536&&W!=19826998))throw runtime_error("GCD growth regression failed");
 const ll known[] = {0,7675,45343,224221,1198498,5516751};
 const int sizes[]={0,4096,16384,65536,262144,1048576};
 for(int j=1;j<=5;j++)if(sizes[j]==X&&T!=known[j])throw runtime_error("high-event regression failed");
 cout<<"WEIGHTED_PASS X="<<X<<" B="<<B<<" starts="<<sourceCount
     <<" high="<<T<<" primeMinSum="<<P<<" allPrimeSum="<<allPrimeWeight
     <<" weightedClockCost="<<(133*T+2*P)
     <<" costOverX2="<<double(133*T+2*P)/(double(X)*X)
     <<" primeOverX2="<<double(P)/(double(X)*X)
     <<" highOverXB="<<double(T)/(double(X)*B)<<" originalW="<<W<<" growthOverX2="<<double(W)/(double(X)*X)
     <<" maxSourceClockCost="<<maxCost<<" maxGap="<<jumpGapMax<<" fullSinkStarts="<<fullSink
     <<" actualHorizonSum="<<Hsum<<" expectedHorizonSum="<<expected;
 for(int b=0;b<5;b++)cout<<" band"<<b<<"_count="<<bandEvents[b]<<" band"<<b<<"_primeMass="<<bandPrimeMass[b];
 cout<<"\n";
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 vector<int>xs;int maxX=0;
 for(int j=1;j<argc;j++){int X=atoi(argv[j]);if(X<256||X%4||X>2000000)return 2;xs.push_back(X);maxX=max(maxX,X);}
 sieve(8*maxX+1000);
 for(int M=7;M<=119;M+=2)if(direct_growth(M,41)!=jump_growth(M,41))throw runtime_error("literal-step parity/GCD mismatch");
 for(int X:xs)run(X);
}
