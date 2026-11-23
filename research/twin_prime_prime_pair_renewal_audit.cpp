// Exact parity-specific squarefree B wheel; same-prime and simultaneous-prime-pair renewal.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_prime_pair_renewal_audit.cpp -o /tmp/pair_renewal
// Run: /tmp/pair_renewal 256 512 1024 4096 16384 65536 262144
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using namespace std;
using ll=long long;
static vector<int>spf;
static void sieve(int n) {spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;++p)if(spf[p]==p)for(int v=p*p;v<n;v+=p)if(spf[v]==v)spf[v]=p;}
static void factors(int n,vector<int>&out) {out.clear();while(n>1){int p=spf.at(n);out.push_back(p);do{n/=p;}while(n%p==0);}}
static int clock_gap(ll t,int p,int residue) {int k=int((residue-t)%(2LL*p));return k>0?k:k+2*p;}
struct Seen {int count=0,last_postC=0,last_time=0,last_parity=0;};
struct Stats {ll W=0,events=0,pairInc=0,pairFirst=0,pairRepeat=0,pairWeight=0,pairWeightRepeat=0;
  ll qInc=0,qRepeats=0,qOddPostReturns=0,pairOddPostReturns=0;
  ll pairRepeatAboveXdiv2=0,pairRepeatAboveXdiv4=0,pairRepeatAboveX=0,largePairFirst=0;
  ll maxPairProductRepeat=0,maxPairProduct=0,maxRepeatMultiplicity=0,maxPairGap=0;
  ll triEvents=0,pairCoincidentTripleWeight=0;
  ll priorEvenQReturns=0,priorOddQReturns=0;
  ll largeResetEvents=0,largeCompositeResetEvents=0,largePairHitsOverK6=0,largePairHitsOverK4=0;
  ll witnessM=0,witnessP=0,witnessQ=0,witnessN0=0,witnessN1=0,witnessRecharge=0;
};
static void audit(int X) {
  int B=int(ceill(sqrtl(7.L*X)));
  Stats z;vector<int>f,labels,usedPrimes,counts(B+1,0),postC(B+1,0),postT(B+1,0),postParity(B+1,0);
  unordered_map<int,Seen>pairStates;
  for(int M=X+1;M<2*X;M+=2) {
    ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4,G=0;usedPrimes.clear();pairStates.clear();
    while(t<K) {
      ll n=K+1;
      factors(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,0));
      factors(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));
      if(n>K)break;
      const ll before=C;
      const int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
      factors(raw,f);labels.clear();int d=1;
      for(int p:f)if(p<=B){labels.push_back(p);d*=p;}
      if(d<3)throw runtime_error("invalid clock event");
      const int quotient=int(((n&1)?n-2:n)/d);
      if(n&1){if(quotient<3||quotient%2==0)throw runtime_error("odd quotient lower bound fails");}
      else if(quotient<2||quotient%2)throw runtime_error("even quotient lower bound fails");
      if(4LL*d>K){
        const ll deficit=2*n-(C+d-1);
        if(quotient!=((n&1)?3:2)||deficit!=((n&1)?6:0))
          throw runtime_error("large increment reset failed");
        ++z.largeResetEvents;
        if(labels.size()>=2)++z.largeCompositeResetEvents;
      }
      if(n&1){if((n-2)%d!=0||(C+1)%d!=0)throw runtime_error("odd modular fail");}
      else if(n%d!=0||(C-1)%d!=0)throw runtime_error("even modular fail");
      ++z.events;if(labels.size()>=3)++z.triEvents;
      for(int p:labels){
        ++z.qInc;
        if(counts[p]>0){
          if(p>=5){const ll recharge=before-postC[p];
            if(recharge<(p-1)||recharge%2)throw runtime_error("prime return recharge fail");
            if(postParity[p]&&recharge<p+1)throw runtime_error("odd-post prime recharge fail");
            if(n-postT[p]<p-2)throw runtime_error("prime return time gap fail");
            if(postParity[p])++z.priorOddQReturns;else ++z.priorEvenQReturns;
          }
          ++z.qRepeats;
        } else usedPrimes.push_back(p);
        ++counts[p];postC[p]=int(before+d-1);postT[p]=int(n);postParity[p]=int(n&1);
      }
      for(size_t i=0;i<labels.size();++i)for(size_t j=i+1;j<labels.size();++j){
        const int p=labels[i],q=labels[j],m=p*q;
        const ll charge=ll(p-1)*(q-1)*(d/m);
        if(6LL*m>K){if(d!=m)throw runtime_error("large pair has a third factor");++z.largePairHitsOverK6;}
        if(4LL*m>K){if(d!=m)throw runtime_error("large reset pair not semiprime");++z.largePairHitsOverK4;}
        z.pairWeight+=charge;++z.pairInc;z.maxPairProduct=max(z.maxPairProduct,ll(m));
        auto&h=pairStates[m];
        if(h.count){
          const ll recharge=before-h.last_postC;
          if(recharge<m-1||recharge%2)throw runtime_error("pair return recharge failed");
          if(h.last_parity&&recharge<m+1)throw runtime_error("odd-post pair recharge failed");
          if(n-h.last_time<m-2)throw runtime_error("pair return spacing failed");
          ++z.pairRepeat;z.pairWeightRepeat+=charge;
          if(!z.witnessM){z.witnessM=M;z.witnessP=p;z.witnessQ=q;
            z.witnessN0=h.last_time;z.witnessN1=n;z.witnessRecharge=recharge;}
          z.maxPairProductRepeat=max(z.maxPairProductRepeat,ll(m));
          z.maxPairGap=max(z.maxPairGap,n-h.last_time);
          if(h.last_parity)++z.pairOddPostReturns;
          if(m>X/2)++z.pairRepeatAboveXdiv2;
          if(m>X/4)++z.pairRepeatAboveXdiv4;
          if(m>X)++z.pairRepeatAboveX;
        } else {++z.pairFirst;if(m>X/2)++z.largePairFirst;}
        ++h.count;h.last_postC=int(before+d-1);h.last_time=int(n);h.last_parity=int(n&1);
        z.maxRepeatMultiplicity=max(z.maxRepeatMultiplicity,ll(h.count));
        if(labels.size()>=3)z.pairCoincidentTripleWeight+=charge;
      }
      z.W+=d-1;G+=d-1;C+=d-1;t=n;
      if(C>2*n)throw runtime_error("horizon invariant violated");
    }
    if(G>2*K-(2LL*M-2))throw runtime_error("growth cap failed");
    for(const auto&kv:pairStates) {
      const ll m=kv.first,k=kv.second.count;
      if((2*k-1)*(m-1)>G)throw runtime_error("pair energy packing violated");
      if(k>=2&&m>1+(2*K-(2LL*M-2))/3)throw runtime_error("pair return beyond max bound");
    }
    for(int p:usedPrimes){
      if(p>=5&&((2LL*counts[p]-1)*(p-1)>G))throw runtime_error("single prime packing violated");
      counts[p]=0;
    }
  }
  if(z.pairInc!=z.pairFirst+z.pairRepeat||z.pairRepeatAboveX>0||z.pairRepeatAboveXdiv2>0||z.pairWeightRepeat>z.pairWeight)throw runtime_error("aggregate mismatch");
  cout<<"PAIR_RENEWAL_PASS X="<<X<<" B="<<B<<" W="<<z.W<<" events="<<z.events
    <<" primeHits="<<z.qInc<<" primeReturns="<<z.qRepeats
    <<" pairHits="<<z.pairInc<<" pairFirst="<<z.pairFirst<<" pairReturns="<<z.pairRepeat
    <<" pairWeight="<<z.pairWeight<<" pairReturnWeight="<<z.pairWeightRepeat
    <<" pairReturnOverX4="<<z.pairRepeatAboveXdiv4
    <<" pairReturnOverX2="<<z.pairRepeatAboveXdiv2
    <<" bigPairFirstOverX2="<<z.largePairFirst
    <<" maxRepeatedPairProduct="<<z.maxPairProductRepeat
    <<" maxPairProduct="<<z.maxPairProduct
    <<" maxPairMultiplicity="<<z.maxRepeatMultiplicity
    <<" oddPriorPairReturns="<<z.pairOddPostReturns
    <<" multi3Events="<<z.triEvents<<" multi3PairWeight="<<z.pairCoincidentTripleWeight
    <<" largeReset="<<z.largeResetEvents<<" largeCompositeReset="<<z.largeCompositeResetEvents
    <<" largePairOverK6="<<z.largePairHitsOverK6<<" largePairOverK4="<<z.largePairHitsOverK4
    <<" firstPairReturnM="<<z.witnessM<<" firstPairReturnP="<<z.witnessP
    <<" firstPairReturnQ="<<z.witnessQ<<" firstPairReturnN0="<<z.witnessN0
    <<" firstPairReturnN1="<<z.witnessN1<<" firstPairReturnRecharge="<<z.witnessRecharge<<"\n";
}
int main(int argc,char**argv) {
 if(argc<2)return 2;
 int largest=0;
 for(int i=1;i<argc;++i){int X=atoi(argv[i]);if(X<256||X>262144||X%4)return 2;largest=max(largest,X);}
 sieve(8*largest+1000);
 for(int i=1;i<argc;++i)audit(atoi(argv[i]));
}