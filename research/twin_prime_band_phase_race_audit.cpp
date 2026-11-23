// ORIGINAL final parity-GCD squarefree wheel and full-horizon q-deleted ghost,
// restarted after EVERY actual q-bearing event (not just the first).
// Reconstructs the exact next actual q-hit; measures shifted phase WIN sets.
// Shifted controls are counterfactual and NOT a uniform-source probability law.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_band_phase_race_audit.cpp -o /tmp/phase_race
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int>spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
static void fac(int n,vector<int>&f){f.clear();while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}}
static int gap(ll t,int p,int r){ll g=(r-t)%(2LL*p);return int(g>0?g:g+2*p);}
struct Event{int q,t,C,nextT;bool isFirst;};
struct Stats{double rotatedExpected=0,rotatedExpectedFirst=0; ll rotatedWinnerTotal=0,tagged=0,firstReturn=0; ll nextReturnLowAlive=0,nextReturnLowDead=0;ll donorClasses[4]{}; ll sources=0,first=0,second=0,ret=0,protectedCount=0,unprotected=0,unprotectedRet=0,zeroGrowth=0,tailEvents=0,activePlateaus=0,lowActive=0,lowDead=0,lowClockEarly=0,lowClockLate=0,foreignPreempts=0,ghostGain=0,ghostTailMax=0; int maxRatioNum=0,maxRatioDen=1;};
static void shadow(int q,ll t,ll C,ll K,int B,ll&gain,int&nextHit,int&nevents,int&active,int&lowActive,int&lowDead,int&lowClockEarly,int&lowClockLate,int&foreignPreempts,int&rotatedWinners,bool&nextLowAlive,int&nextDonors,vector<int>&stamp,int epoch) {
 vector<int>f; int highCount=0;nextDonors=-1;gain=0;nextHit=0;nevents=0;active=0;lowActive=0;lowDead=0;lowClockEarly=0;lowClockLate=0;foreignPreempts=0;rotatedWinners=0;nextLowAlive=false;
 while(t<K){
  ll no=K+1,nq=K+1,nlow=K+2*B+1;
  fac(int(C-1),f);
  for(int p:f)if(p<=B){ll z=t+gap(t,p,0);if(p==q)nq=min(nq,z);else {no=min(no,z);if(p<=7)nlow=min(nlow,z);}}
  fac(int(C+1),f);
  for(int p:f)if(p<=B){ll z=t+gap(t,p,p+2);if(p==q)nq=min(nq,z);else {no=min(no,z);if(p<=7)nlow=min(nlow,z);}}
  if(nevents>0){
    int cm=int(C%q);
    auto mark=[&](int x){if(stamp[x]!=epoch){stamp[x]=epoch;rotatedWinners++;}};
    if(t+gap(t,q,0)<=no && t+gap(t,q,0)<=K) mark((cm+q-1)%q);
    if(t+gap(t,q,q+2)<=no && t+gap(t,q,q+2)<=K) mark((cm+1)%q);
  }
  if(nq<=K){
    active++;
    if(nlow<K+2*B+1){lowActive++; if(nq<=nlow)lowClockEarly++;else lowClockLate++;}
    else {lowDead++;if(no<nq)foreignPreempts++;}
    if(nextHit==0 && nq<=no){nextHit=int(nq);nextLowAlive=(nlow<K+2*B+1);nextDonors=highCount;}
  }
  if(no>K)break;
  int raw=int(gcd((no&1)?no-2:no,(no&1)?C+1:C-1));
  fac(raw,f);int d=1;for(int p:f)if(p<=B && p!=q)d*=p;
  if(d<=1)throw runtime_error("q-free first-hit mismatch");
  for(int p:f)if(p!=q && p<=B && p>=11){highCount++;break;}
  C+=d-1;gain+=d-1;t=no;nevents++;
 }
}
static void run(int X){
 int B=int(ceill(sqrtl(7.L*X)));Stats S[3];vector<int>f;
 vector<int>stamp(B+1,0);int epoch=0;
 for(int M=X+1;M<2*X;M+=2){
  ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
  vector<Event> tagged;vector<int>lastTag(B+1,-1);
  while(t<K){
   ll n=K+1;
   fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));
   fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));
   if(n>K)break;
   int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));fac(raw,f);int d=1;
   for(int p:f)if(p<=B)d*=p;
   if(d<=1)throw runtime_error("full hit mismatch");
   C+=d-1;t=n;
   for(int p:f)if(p>=11 && p<=B){
    int band=4*p<B?0:2*p<B?1:2;
    if(band>=1){
      int prev=lastTag[p];
      if(prev!=-1)tagged[prev].nextT=int(t);
      tagged.push_back({p,int(t),int(C),0,prev==-1});
      lastTag[p]=int(tagged.size())-1;
    }
   }
  }
  for(const auto &e:tagged){
    int band=2*e.q<B?1:2;
    Stats &z=S[band];z.tagged++;if(e.isFirst)z.first++;ll G=0;int next=0,nEvents=0,active=0,lowActive=0,lowDead=0,lowClockEarly=0,lowClockLate=0,foreignPreempts=0,rotatedWinners=0,nextDonors=-1;bool nextLowAlive=false;rotatedWinners=0;
    shadow(e.q,e.t,e.C,K,B,G,next,nEvents,active,lowActive,lowDead,lowClockEarly,lowClockLate,foreignPreempts,rotatedWinners,nextLowAlive,nextDonors,stamp,++epoch);
    if(next!=e.nextT){
      cerr<<"SHADOW_MISMATCH M="<<M<<" q="<<e.q<<" first="<<e.t<<" predicted="<<next<<" observed="<<e.nextT<<"\n";
      throw runtime_error("shadow match");
    }
    const ll needed=((e.t%2)==0?e.q-1:e.q+1);
    if(G<needed){z.protectedCount++;if(next)throw runtime_error("protected return");}
    else {z.unprotected++;if(next)z.unprotectedRet++;}
    if(next){z.ret++;if(nextLowAlive)z.nextReturnLowAlive++;else z.nextReturnLowDead++;if(nextDonors<0)throw runtime_error("missing donor count");z.donorClasses[min(nextDonors,3)]++;if(e.isFirst)z.firstReturn++;}
    if(G==0)z.zeroGrowth++;
    if(1LL*rotatedWinners*e.q>K-e.t+2)throw runtime_error("q calendar slot bound");
    if(band==2 && 7LL*rotatedWinners>=6LL*e.q)throw runtime_error("6/7 phase contraction");
    z.rotatedExpected+=double(rotatedWinners)/e.q;if(e.isFirst)z.rotatedExpectedFirst+=double(rotatedWinners)/e.q;z.rotatedWinnerTotal+=rotatedWinners;z.ghostGain+=G;z.tailEvents+=nEvents;z.activePlateaus+=active;z.lowActive+=lowActive;z.lowDead+=lowDead;z.lowClockEarly+=lowClockEarly;z.lowClockLate+=lowClockLate;z.foreignPreempts+=foreignPreempts;
    if(G>z.ghostTailMax)z.ghostTailMax=G;
    if(G*z.maxRatioDen>ll(e.q)*z.maxRatioNum){z.maxRatioNum=int(G);z.maxRatioDen=e.q;}
  }
 }
 cout<<"PHASE_RACE_PASS X="<<X<<" B="<<B;
 for(int b=1;b<=2;b++){auto z=S[b];if(z.tagged!=z.first+z.ret)throw runtime_error("tagged ledger");cout<<" band="<<b<<" first="<<z.first<<" tagged="<<z.tagged<<" returns="<<z.ret<<" returnLowAlive="<<z.nextReturnLowAlive<<" returnLowDead="<<z.nextReturnLowDead<<" firstReturn="<<z.firstReturn<<" returnDonors0="<<z.donorClasses[0]<<" returnDonors1="<<z.donorClasses[1]<<" returnDonors2="<<z.donorClasses[2]<<" returnDonors3plus="<<z.donorClasses[3]
   <<" protected="<<z.protectedCount<<" unprotected="<<z.unprotected
   <<" unprotectedReturns="<<z.unprotectedRet<<" zeroGrowth="<<z.zeroGrowth
   <<" ghostGainPerTag="<<(z.first?double(z.ghostGain)/z.first:0.0)
   <<" ghostEventsPerTag="<<(z.first?double(z.tailEvents)/z.first:0.0)
   <<" activePerTag="<<(z.first?double(z.activePlateaus)/z.first:0.0) <<" lowActive="<<z.lowActive<<" lowDead="<<z.lowDead<<" lowQClockEarly="<<z.lowClockEarly<<" lowQClockLate="<<z.lowClockLate<<" foreignPreempts="<<z.foreignPreempts
   <<" shiftedPhaseExpectedAll="<<z.rotatedExpected<<" shiftedPhaseExpectedFirst="<<z.rotatedExpectedFirst <<" shiftedWinningPhaseMean="<<(z.tagged?double(z.rotatedWinnerTotal)/z.tagged:0.0) <<" discrepancyOverTags="<<(z.tagged?(double(z.ret)-z.rotatedExpected)/z.tagged:0.0)<<" phase1over8Finite="<<(double(z.ret)-z.rotatedExpected<=double(z.tagged)/8.0?1:0) <<" maxGhostGain="<<z.ghostTailMax<<" maxGOverQ="<<z.maxRatioNum<<"/"<<z.maxRatioDen;}
 cout<<"\n";
}
int main(int argc,char**argv){int mx=0;vector<int>xs;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X%4||X>1048576)return 2;xs.push_back(X);mx=max(mx,X);}if(xs.empty())return 2;sieve(8*mx+500);for(int X:xs)run(X);}