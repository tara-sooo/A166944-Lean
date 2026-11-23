// Original parity-clipped squarefree GCD, event-jump exact audit of high-event renewal types.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror renewal_operator_audit.cpp -o renewal_operator_audit
// ./renewal_operator_audit 4096 16384 65536 262144 1048576
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
#include <map>
#include <unordered_set>
using namespace std;
using ll=long long;
static vector<int> spf;
static ll gap(ll t,int p,ll residue){ll a=(residue-t)%(2LL*p);if(a<=0)a+=2LL*p;return a;}
static constexpr int LOW_L=2310;
static vector<int> sinkGrowth;
static void setup(int X){int n=8*X+1000;spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;++p)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
static void init_sink(){
 sinkGrowth.resize(2*LOW_L);
 for(int z:{0,6})for(int r=0;r<LOW_L;r++){
  ll t=r+4LL*LOW_L,C=2*t-z;ll initC=C;int count=0;
  while(true){ll n=INT64_MAX/4;int d=1;
    for(int p:{3,5,7,11}){
      if((C-1)%p==0)n=min(n,t+gap(t,p,0));
      else if((C+1)%p==0)n=min(n,t+gap(t,p,p+2));
    }
    if(n==INT64_MAX/4)break;
    for(int p:{3,5,7,11}){
      if((C-1)%p==0&&t+gap(t,p,0)==n)d*=p;
      else if((C+1)%p==0&&t+gap(t,p,p+2)==n)d*=p;
    }
    if(d==1)throw runtime_error("low sink clock invalid");
    C+=d-1;t=n;count++;
    if(count>22)throw runtime_error("low sink event cap");
  }
  if(C-initC>100)throw runtime_error("reset sink growth cap");
  sinkGrowth[r+(z==6?LOW_L:0)]=int(C-initC);
 }
}
static void fac(int n,vector<int>&v){v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}}
static ll literal(int M,int B){ll C=2LL*M-2,C0=C,K=(7LL*M-1)/4;vector<int>f;for(ll n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));fac(g,f);int d=1;for(int p:f)if(p<=B)d*=p;C+=d-1;}return C-C0;}
struct Count {ll runs=0,events=0,reset=0,charged=0,primeOnly=0,composite=0,chargedLarge=0,chargedSmall=0,firstAfterReset=0,firstP193=0,firstP193Charged=0,firstP193Reset=0,firstP193LowActive=0,firstP67Charged=0,firstP67ChargedLowActive=0,firstP193PlusSide=0,firstP193MinusSide=0,firstP193RewindRoots=0,firstP193NoActive=0,chargedNextReset=0,chargedNextResetComposite=0,chargedNextResetPrime=0,chargedNextCharged=0,chargedNextChargedComposite=0,chargedNextChargedPrime=0,chargedDied=0,chargedNextHigh=0,sinkCandidates=0,sinkCandidateWeight=0,initialSinkCount=0,initialSinkWeight=0,initialFirstP193=0,sinkAbsDiff=0,sinkSignedDiff=0,sinkTwinPrimes=0,postResetP193Confirmed=0,chargedAboveHalf=0,chargedAboveHalfPrimeReset=0,chargedAboveHalfCompositeReset=0,resetThenHigh=0,resetThenHighPure=0,resetThenHighCharged=0,resetThenHighReset=0,postResetChargedP149=0,chargedNextResetPureBound=0,maxChargedRun=0,maxHigh=0,lowEvents=0,maxLowGrowth=0,sumHigh=0;};
struct First{ll M,n,z,prez;int d,p,kind;int lowEvents=0,lowGrowth=0;bool fromReset=false,has=false;};
static void run(int X){int B=int(ceill(sqrtl(7.L*X)));Count total;vector<int>f,g,hi;vector<ll> sinkQCount(B+1,0);
 map<int,ll> chargeRunHistogram;vector<ll> highDepthHistogram(512,0);unordered_set<int> distinctTwinCenters;
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4,lowGrowth=0;ll anchorT=t;int anchorZ=6;int low=0,chargedRun=0,high=0;First prev{};bool previousHighReset=false;int postHighLow=0;ll postHighGrowth=0;
   const ll initialSinkC=2*t-6+sinkGrowth[int(t%LOW_L)+LOW_L];
   if(initialSinkC+1>=(ll)spf.size())throw runtime_error("initial sink out of sieve range");
   fac(int(initialSinkC-1),f);for(int q:f)if(q>=193&&q<=B){total.initialSinkCount++;total.initialSinkWeight+=q;}
   fac(int(initialSinkC+1),f);for(int q:f)if(q>=193&&q<=B){total.initialSinkCount++;total.initialSinkWeight+=q;}
   while(t<K){ll n=K+1;fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
    int g0=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));fac(g0,g);int d=1;hi.clear();for(int p:g)if(p<=B){d*=p;if(p>=13)hi.push_back(p);}if(d<=1)throw runtime_error("not next event");
    ll zpre=2*t-C,zpost=2*n-C-(d-1);bool isHi=!hi.empty();bool rst=(n%2==0?zpost==0:zpost==6);
    if(zpost<0)throw runtime_error("negative deficit");
    if(isHi){
       const bool afterReset=!prev.has||prev.kind==0;
       const bool lowActive=([&](){for(int q:{3,5,7,11})if((C-1)%q==0||(C+1)%q==0)return true;return false;})();
       if(afterReset){
          total.firstAfterReset++;
          if(zpre>146||hi.size()!=1)throw runtime_error("first-high since reset low finite bound failed");
          if(hi[0]>=59&&d!=hi[0])throw runtime_error("first-high >=59 must be prime-only");
          if(hi[0]>=193){
             if(!prev.has)total.initialFirstP193++;
             const int sinkCell=int(anchorT%LOW_L)+(anchorZ==6?LOW_L:0);
             const ll sinkC=2*anchorT-anchorZ+sinkGrowth[sinkCell];
             if((sinkC-1)%hi[0] && (sinkC+1)%hi[0])throw runtime_error("large first high p not a sink divisor");
             total.postResetP193Confirmed++;
             total.firstP193++;
             if(rst)total.firstP193Reset++;else total.firstP193Charged++;
             if(lowActive)total.firstP193LowActive++;
             else total.firstP193NoActive++;
             if((C-1)%hi[0]==0)total.firstP193MinusSide++;
             else if((C+1)%hi[0]==0)total.firstP193PlusSide++;
             else throw runtime_error("first-high factor not active");
             if(lowActive)throw runtime_error("high>=193 interrupted a low clock");
          }
          if(!rst&&hi[0]>=67){total.firstP67Charged++;
            if(lowActive){total.firstP67ChargedLowActive++;throw runtime_error("charged high>=67 interrupted a low clock");}
          }
       }
       total.events++;high++;total.sumHigh+=hi.size();
       if(n%2==0){if(zpost%(2LL*d))throw runtime_error("double-even carry");}
       else {if((zpost-6)%(2LL*d))throw runtime_error("double-odd carry");}
       if(rst)total.reset++;else total.charged++;
       if(d==hi[0]&&hi.size()==1)total.primeOnly++;else total.composite++;
       if(hi[0]>=149&&!prev.has){ if(zpre>146||d!=hi[0])throw runtime_error("first high seed bound");if(zpost!=0&&zpost!=6&&zpost!=2LL*d&&zpost!=2LL*d+6)throw runtime_error("first high binary carry");}
       if(prev.has){
         total.chargedNextHigh+=(prev.kind==1);
         if(prev.kind==1){
            if(rst){total.chargedNextReset++;if(d!=hi[0]||hi.size()!=1)total.chargedNextResetComposite++;else total.chargedNextResetPrime++;}
            else{total.chargedNextCharged++;if(d!=hi[0]||hi.size()!=1)total.chargedNextChargedComposite++;else total.chargedNextChargedPrime++;}
            if(prev.p>=149&&rst&&d==hi[0]&&hi.size()==1){if(hi[0]<2LL*prev.p-1159)throw runtime_error("next-high prime reset return barrier");total.chargedNextResetPureBound++;}
            if(prev.p>=149&&2LL*prev.p>B+1159&&rst&&d==hi[0]&&hi.size()==1)throw runtime_error("upper-half prime charged followed prime reset");
            if(prev.p>=149&&2LL*prev.p>B+1159&&rst&&d!=hi[0])total.chargedAboveHalfCompositeReset++;
            if(prev.p>=149&&2LL*prev.p>B+1159&&rst&&d==hi[0])total.chargedAboveHalfPrimeReset++;
         }
         if(prev.kind==0){total.resetThenHigh++;if(d==hi[0]&&hi.size()==1)total.resetThenHighPure++;if(rst)total.resetThenHighReset++;else total.resetThenHighCharged++;}
       }
       if(rst){
         const ll sinkC=2*n-zpost+sinkGrowth[int(n%LOW_L)+(zpost==6?LOW_L:0)];
         if(sinkC-1<2||sinkC+1>=(ll)spf.size())throw runtime_error("sink C out of sieve range");
         bool hasHigh=false;
         fac(int(sinkC-1),f);for(int q:f){if(q>=13&&q<=B)hasHigh=true;if(q>=193&&q<=B){sinkQCount[q]++;total.sinkCandidateWeight+=q;total.sinkCandidates++;}}
         fac(int(sinkC+1),f);for(int q:f){if(q>=13&&q<=B)hasHigh=true;if(q>=193&&q<=B){sinkQCount[q]++;total.sinkCandidateWeight+=q;total.sinkCandidates++;}}
         if(!hasHigh){
           if(spf[int(sinkC-1)]!=sinkC-1||spf[int(sinkC+1)]!=sinkC+1)
             throw runtime_error("sink without small factors is not a twin-prime pair");
           total.sinkTwinPrimes++;distinctTwinCenters.insert(int(sinkC));
         }
         anchorT=n;anchorZ=int(zpost);
         total.maxChargedRun=max(total.maxChargedRun,1LL*chargedRun);if(chargedRun)chargeRunHistogram[chargedRun]++;chargedRun=0;}
       else chargedRun++;
       prev={M,n,zpost,zpre,d,hi[0],rst?0:1,0,0,previousHighReset,true};
       previousHighReset=rst;postHighLow=0;postHighGrowth=0;
    }else{
      low++;lowGrowth+=d-1; if(prev.has){postHighLow++;postHighGrowth+=d-1; if(postHighGrowth>1156)throw runtime_error("low prefix cap exceeded");}
    }
    C+=d-1;t=n;
   }
   if(high>=int(highDepthHistogram.size()))throw runtime_error("depth histogram overflow");
   highDepthHistogram[high]++;
   total.maxHigh=max(total.maxHigh,1LL*high);total.maxChargedRun=max(total.maxChargedRun,1LL*chargedRun);
   if(chargedRun)chargeRunHistogram[chargedRun]++;
   if(prev.has&&prev.kind==1)total.chargedDied++;
   total.lowEvents+=low;total.maxLowGrowth=max(total.maxLowGrowth,lowGrowth);
 }
 int nHighQ=0;long double absError=0;for(int q=193;q<=B;q+=2)if(spf[q]==q){nHighQ++;absError+=llabs(1LL*q*sinkQCount[q]-2LL*total.reset);}
 total.sinkSignedDiff=total.sinkCandidateWeight-2LL*nHighQ*total.reset;
 total.sinkAbsDiff=llroundl(absError);
 if(X==4096&&total.events!=7675)throw runtime_error("historic 4096 high count mismatch");
 if(X==16384&&total.events!=45343)throw runtime_error("historic 16384 high count mismatch");
 if(X==65536&&total.events!=224221)throw runtime_error("historic 65536 high count mismatch");
 cout<<"REN X="<<X<<" B="<<B<<" starts="<<X/2<<" high="<<total.events<<" resets="<<total.reset<<" charged="<<total.charged<<" firstAfterReset="<<total.firstAfterReset<<" firstP193="<<total.firstP193<<" firstP193Reset="<<total.firstP193Reset<<" firstP193Charged="<<total.firstP193Charged<<" firstP193LowActive="<<total.firstP193LowActive<<" firstP67Charged="<<total.firstP67Charged<<" firstP67ChargedLowActive="<<total.firstP67ChargedLowActive<<" firstP193NoActive="<<total.firstP193NoActive<<" primeOnly="<<total.primeOnly<<" composite="<<total.composite<<" initialSinkCount="<<total.initialSinkCount<<" initialSinkWeight="<<total.initialSinkWeight<<" initialSinkExpectedWeight="<<1LL*X*nHighQ<<" initialFirstP193="<<total.initialFirstP193<<" sinkQcount="<<nHighQ<<" sinkCandidateCount="<<total.sinkCandidates<<" sinkCandidateWeight="<<total.sinkCandidateWeight<<" sinkExpectedWeight="<<2LL*nHighQ*total.reset<<" sinkSignedDiff="<<total.sinkSignedDiff<<" sinkAbsDiff="<<total.sinkAbsDiff<<" sinkAbsToExpected="<<(nHighQ?double(total.sinkAbsDiff)/(2.L*nHighQ*total.reset):0)<<" sinkTwinCandidate="<<total.sinkTwinPrimes<<" distinctTwinCenters="<<distinctTwinCenters.size()<<" sinkP193Checked="<<total.postResetP193Confirmed<<" highPrimeHits="<<total.sumHigh<<" maxHigh="<<total.maxHigh<<" maxChargedRun="<<total.maxChargedRun<<" chargedNextHigh="<<total.chargedNextHigh<<" chargedNextReset="<<total.chargedNextReset<<" chargedNextResetPrime="<<total.chargedNextResetPrime<<" chargedNextResetComposite="<<total.chargedNextResetComposite<<" chargedNextCharged="<<total.chargedNextCharged<<" chargedNextChargedPrime="<<total.chargedNextChargedPrime<<" chargedNextChargedComposite="<<total.chargedNextChargedComposite<<" chargedTerminal="<<total.chargedDied<<" halfChargedNextResetPrime="<<total.chargedAboveHalfPrimeReset<<" halfChargedNextResetComposite="<<total.chargedAboveHalfCompositeReset<<" lowEvents="<<total.lowEvents<<" maxAllLowGrowth="<<total.maxLowGrowth<<"\n";
 cout<<"HIGH_TAIL X="<<X;
 for(int k:{1,2,3,5,10,20,30,40,50,60,70,80,100}){
   ll above=0,above10=0;
   for(int j=k;j<(int)highDepthHistogram.size();j++)above+=highDepthHistogram[j];
   for(int j=k+10;j<(int)highDepthHistogram.size();j++)above10+=highDepthHistogram[j];
   cout<<" ge"<<k<<"="<<above<<" ratioPlus10="<<(above?double(above10)/above:0);
 }
 cout<<"\n";
 cout<<"RUN_DEPTH X="<<X;for(int a:{1,2,3,4,5,10,15,20,30,50,100}){ll f=0;for(auto [k,n]:chargeRunHistogram)if(k>=a)f+=n;cout<<" ge"<<a<<"="<<f;}cout<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;vector<int>xs;for(int j=1;j<argc;++j){int X=atoi(argv[j]);if(X<256||(X&1)||X>2000000)return 2;maxX=max(maxX,X);xs.push_back(X);}setup(maxX);init_sink();
 for(int M=7;M<=119;M+=2){int B=41;ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;vector<int> f,g;while(t<K){ll n=K+1;fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;int gd=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;fac(gd,g);for(int p:g)if(p<=B)d*=p;C+=d-1;t=n;}if(C-(2LL*M-2)!=literal(M,B))throw runtime_error("literal mismatch");}
 for(int X:xs)run(X);
}
