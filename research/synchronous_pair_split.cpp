// Compare synchronous q-clock pair energy by exact pre-event state equality.
// Builds as C++17: g++ -std=c++17 -O3 -Wall -Wextra -Werror ...
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
struct Hit{uint32_t q,n,c,M;};
static_assert(sizeof(Hit)==16,"packed hit");
static vector<int> spf;
static void sieve(int z){spf.resize(z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<z;p++)if(spf[p]==p)for(int x=p*p;x<z;x+=p)if(spf[x]==x)spf[x]=p;}
static void factors(int n,vector<int>&v){v.clear();while(n>1){int q=spf.at(n);v.push_back(q);do{n/=q;}while(n%q==0);}}
static int gap(ll t,int q,int r){int v=int((r-t)%(2LL*q));if(v<=0)v+=2*q;return v;}
static ll literal_growth(int M,int B){ll c=2LL*M-2,start=c,K=(7LL*M-1)/4;vector<int>f;for(ll n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(g,f);int d=1;for(int q:f)if(q<=B)d*=q;c+=d-1;}return c-start;}
static ll jump_growth(int M,int B){ll c=2LL*M-2,start=c,t=M+2,K=(7LL*M-1)/4;vector<int>f;while(t<K){ll n=K+1;factors(int(c-1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,0));factors(int(c+1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,q+2));if(n>K)break;int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(g,f);int d=1;for(int q:f)if(q<=B)d*=q;c+=d-1;t=n;}return c-start;}
static void run(int X){
  int B=int(ceill(sqrtl(7.L*X)));vector<Hit>hits;hits.reserve(size_t(X)*6);
  ll high=0,oldJ=0,join=0,off=0,weightedInc=0;ll maxHighPreZ=0,maxHighPostZ=0,maxHighPlateauZ=0;__int128 totalG2=0,priorGrowthWeighted=0;ll totalG=0;
  vector<int>f;size_t sourceCount=0;
  for(int M=X+1;M<2*X;M+=2){
    ll c=2LL*M-2,t=M+2,K=(7LL*M-1)/4;const ll c0=c;
    while(t<K){
      ll n=K+1;
      factors(int(c-1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,0));
      factors(int(c+1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,q+2));
      if(n>K)break;
      int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(raw,f);
      int d=1;bool highHere=false;
      for(int q:f)if(q<=B){d*=q;if(q>=13){highHere=true;hits.push_back({uint32_t(q),uint32_t(n),uint32_t(c),uint32_t(M)});weightedInc+=q;priorGrowthWeighted+=(__int128)q*(c-c0);}}
      if(d<=1)throw runtime_error("bad event");
      if(highHere){high++;maxHighPreZ=max(maxHighPreZ,2*n-c);maxHighPostZ=max(maxHighPostZ,2*n-(c+d-1));maxHighPlateauZ=max(maxHighPlateauZ,2*t-c);}
      c+=d-1;t=n;
    }
    sourceCount++;totalG+=c-c0;totalG2+=(__int128)(c-c0)*(c-c0);
  }
  if(sourceCount!=size_t(X/2))throw runtime_error("source count");
  if((X==4096&&high!=7675)||(X==16384&&high!=45343)||(X==65536&&high!=224221)||(X==262144&&high!=1198498)||(X==1048576&&high!=5516751))throw runtime_error("high count regression");
  sort(hits.begin(),hits.end(),[](const Hit&a,const Hit&b){if(a.q!=b.q)return a.q<b.q;if(a.n!=b.n)return a.n<b.n;if(a.c!=b.c)return a.c<b.c;return a.M<b.M;});
  ll diagonal=0, joinOffDiag=0, offOffDiag=0;int topQ=0,topN=0;ll maxClock=0,maxStateOcc=0;ll joinedKeys=0,uniqueKeys=0;ll maxDistinctHitStates=0;int maxDistinctHitPrime=0,maxDistinctHitTime=0;int maxOffQ=0;int maxOffN=0;ll maxOffPair=0;
  // prime bands: [13,B/16], ... [B/2,B]
  array<ll,5> Jband{},JoinBand{},OffBand{},HitsBand{};array<ll,5>maxRband{},maxMassband{};vector<ll>primeMaxMu(B+1,0),primeMaxR(B+1,0),primeMaxNodeMass(B+1,0);
  // Distinct clock aggregate metrics
  for(size_t i=0;i<hits.size();){
    size_t j=i+1;while(j<hits.size()&&hits[j].q==hits[i].q&&hits[j].n==hits[i].n)j++;
    ll mu=ll(j-i),q=hits[i].q,groupJ=q*mu*mu;
    ll groupJoin=0,numStates=0;
    for(size_t k=i;k<j;){size_t l=k+1;while(l<j&&hits[l].c==hits[k].c)l++;
      ll m=ll(l-k);groupJoin+=q*m*m;numStates++;maxStateOcc=max(maxStateOcc,m);k=l;
    }
    if(groupJoin>groupJ)throw runtime_error("joined >total");
    oldJ+=groupJ;join+=groupJoin;off+=groupJ-groupJoin;
    if(groupJ>groupJoin){maxOffQ=max(maxOffQ,int(q));if(groupJ-groupJoin>maxOffPair){maxOffPair=groupJ-groupJoin;maxOffN=hits[i].n;}}
    diagonal+=q*mu;joinOffDiag+=groupJoin-q*mu;offOffDiag+=groupJ-groupJoin;
    if(mu>maxClock){maxClock=mu;topQ=q;topN=hits[i].n;}
    if(numStates>1)joinedKeys++;
    if(numStates>maxDistinctHitStates){maxDistinctHitStates=numStates;maxDistinctHitPrime=int(q);maxDistinctHitTime=hits[i].n;}
    uniqueKeys++;
    int band=q<=B/16?0:q<=B/8?1:q<=B/4?2:q<=B/2?3:4;
    primeMaxMu[q]=max(primeMaxMu[q],mu);primeMaxR[q]=max(primeMaxR[q],numStates);
    maxRband[band]=max(maxRband[band],numStates);maxMassband[band]=max(maxMassband[band],mu);
    Jband[band]+=groupJ;JoinBand[band]+=groupJoin;OffBand[band]+=groupJ-groupJoin;HitsBand[band]+=mu;
    i=j;
  }
  if(oldJ!=join+off||join!=diagonal+joinOffDiag)throw runtime_error("energy split mismatch");
  if((__int128)2*joinOffDiag>priorGrowthWeighted)throw runtime_error("growth-charge coalescence inequality violated");
  if((__int128)24*priorGrowthWeighted>(__int128)13*totalG2)throw runtime_error("prime-weight integral inequality violated");
  ll sumPrimeMaxMu=accumulate(primeMaxMu.begin(),primeMaxMu.end(),0LL);
  ll maxPrimeCap=0;for(int q=13;q<=B;q++)if(spf[q]==q)maxPrimeCap=max(maxPrimeCap,primeMaxMu[q]);
  cout<<"PAIR_SPLIT_PASS X="<<X<<" B="<<B<<" sources="<<sourceCount<<" high="<<high
      <<" qHits="<<hits.size()<<" qMass="<<weightedInc
      <<" J="<<oldJ<<" joined="<<join<<" off="<<off
      <<" joinFrac="<<double(join)/oldJ<<" joinOffDiag="<<joinOffDiag<<" offOffDiag="<<offOffDiag
      <<" diagonal="<<diagonal<<" uniqueClocks="<<uniqueKeys<<" multipleStatesClocks="<<joinedKeys
      <<" maxClock="<<maxClock<<" topQ="<<topQ<<" topN="<<topN<<" maxHighPreZ="<<maxHighPreZ<<" maxHighPreZoverB="<<double(maxHighPreZ)/B<<" maxHighPostZ="<<maxHighPostZ<<" maxHighPlateauZ="<<maxHighPlateauZ<<" totalGrowth="<<totalG<<" sumG2="<<double(totalG2)<<" priorGrowthWeighted="<<double(priorGrowthWeighted)<<" joinChargeRatio="<<(priorGrowthWeighted?double(2*joinOffDiag)/double(priorGrowthWeighted):0)<<" primeMaxMuSum="<<sumPrimeMaxMu<<" primeMaxMuSumOverX="<<double(sumPrimeMaxMu)/X<<" maxPrimeCap="<<maxPrimeCap<<" maxDistinctHitStates="<<maxDistinctHitStates<<" maxDistinctHitPrime="<<maxDistinctHitPrime<<" maxDistinctHitTime="<<maxDistinctHitTime<<" maxStateOccupancy="<<maxStateOcc<<" maxOffQ="<<maxOffQ<<" maxOffWeightedGroup="<<maxOffPair<<" maxOffN="<<maxOffN
      <<" norm="<<double(oldJ)/(double(X)*B*B*(size_t(0)+1))<<"\n";
  for(int b=0;b<5;b++)cout<<"BAND X="<<X<<" band="<<b<<" hits="<<HitsBand[b]<<" J="<<Jband[b]<<" joined="<<JoinBand[b]<<" off="<<OffBand[b]
        <<" fracJoined="<<(Jband[b]?double(JoinBand[b])/Jband[b]:0)<<" maxR="<<maxRband[b]<<" maxMu="<<maxMassband[b]<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;vector<int>xs;for(int i=1;i<argc;i++){int x=atoi(argv[i]);if(x<256||x%4||x>2000000)return 2;xs.push_back(x);maxX=max(maxX,x);}sieve(8*maxX+1000);for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=jump_growth(M,41))throw runtime_error("literal GCD mismatch");for(int x:xs)run(x);}
