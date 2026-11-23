// Actual ORIGINAL parity-specific clipped-GCD event sieve: low-sink q-pulse residues.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror actual_low_sink_residue_audit.cpp -o audit
// ./audit 4096 16384 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
constexpr int P=1155,L=2310;
struct SinkHit{uint32_t n,c,d;};
static vector<int> spf;
void setup(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
void fac(int n,vector<int>&ps){ps.clear();while(n>1){int p=spf.at(n);ps.push_back(p);do{n/=p;}while(n%p==0);}}
ll clock_gap(ll t,int p,int r){ll v=(r-t)%(2LL*p);return v>0?v:v+2LL*p;}
bool low_inactive(ll c){return gcd(llabs(c-1),1LL*P)==1&&gcd(c+1,1LL*P)==1;}
static int goodUnits[1155];
void init_model(){int nc=0;
 for(int c=0;c<L;c+=2)if(low_inactive(c)){
   nc++;for(int d=1;d<L;d+=2)if(gcd(d,P)==1&&low_inactive(c+d-1))goodUnits[c/2]++;
 }
 if(nc!=135)throw runtime_error("135 sink residues expected");
}
void scan(int X){int B=int(ceill(sqrtl(7.L*X)));vector<SinkHit>hits;hits.reserve(size_t(X)*5);vector<int>ps;
 ll high=0,high17=0,only13=0,allEvents=0,weightedSink=0,W=0;
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,c=2LL*M-2,K=(7LL*M-1)/4,c0=c;
   while(t<K){ll n=K+1;
      fac(int(c-1),ps);for(int p:ps)if(p<=B)n=min(n,t+clock_gap(t,p,0));
      fac(int(c+1),ps);for(int p:ps)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));
      if(n>K)break;
      int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(raw,ps);
      int d=1;bool isHigh=false,isHigh17=false;
      for(int p:ps)if(p<=B){d*=p;if(p>=13)isHigh=true;if(p>=17)isHigh17=true;}
      if(d<=1)throw runtime_error("clock selected non-event");
      if(isHigh){high++;if(isHigh17)high17++;else only13++;if(low_inactive(c)){hits.push_back({uint32_t(n),uint32_t(c),uint32_t(d)});weightedSink++;if(gcd(d,P)!=1)throw runtime_error("low-inactive hit had low prime factor");}}
      c+=d-1;t=n;allEvents++;
   }
   W+=c-c0;
 }
 const auto cmp=[](const SinkHit&a,const SinkHit&b){if(a.n!=b.n)return a.n<b.n;if(a.c!=b.c)return a.c<b.c;return a.d<b.d;};
 sort(hits.begin(),hits.end(),cmp);
 ll unique=0,reactivated=0,weightedReact=0,weightedSurvive=0,uniqueMod3=0;ll unitCounts[2310]={},primeOnly=0,composite=0;long double modeledSurvive=0,modeledWeightedSurvive=0;
 for(size_t i=0;i<hits.size();){size_t j=i+1;while(j<hits.size()&&hits[j].n==hits[i].n&&hits[j].c==hits[i].c){if(hits[j].d!=hits[i].d)throw runtime_error("same pre-state has different full increment");j++;}
   const auto&h=hits[i];ll mass=ll(j-i);bool remain=low_inactive(ll(h.c)+h.d-1);
   unique++;unitCounts[h.d%L]++;
   if(h.d>1&&spf.at(int(h.d))==int(h.d))primeOnly++;else composite++;
   if(!remain){reactivated++;weightedReact+=mass;}else weightedSurvive+=mass;
   if(h.d%3==2)uniqueMod3++;
   const int model=goodUnits[(h.c%L)/2];
   if(model<64||model>135)throw runtime_error("uniform model root count range");
   modeledSurvive+=static_cast<long double>(model)/480;
   modeledWeightedSurvive+=static_cast<long double>(model)*mass/480;
   i=j;
 }
 if(weightedReact+weightedSurvive!=weightedSink)throw runtime_error("mass partition fail");
 if((X==4096&&high!=7675)||(X==16384&&high!=45343)||(X==65536&&high!=224221)||(X==262144&&high!=1198498)||(X==1048576&&high!=5516751))throw runtime_error("previous GCD high regression");
 if((X==4096&&W!=399142)||(X==16384&&W!=2915326)||(X==65536&&W!=19826998))throw runtime_error("previous GCD growth regression");
 long double totalDeviation=0;int minCount=1000000,maxCount=0;
 for(int d=1;d<L;d+=2)if(gcd(d,P)==1){ll cnt=unitCounts[d];
  totalDeviation+=fabsl(static_cast<long double>(cnt)/unique-1.0L/480)/2;
  minCount=min(minCount,int(cnt));maxCount=max(maxCount,int(cnt));
 }
 cout<<setprecision(9)<<"ACTUAL_SINK_PASS X="<<X<<" B="<<B<<" high="<<high<<" highAtLeast17="<<high17<<" high13Only="<<only13<<" high17Ratio="<<double(high17)/high<<" normHigh17="<<double(high17)/(double(X)*B)<<" lowSinkHighWeighted="<<weightedSink
     <<" distinctSinkHigh="<<unique<<" reactivatedUnique="<<reactivated<<" actualReactivation="<<double(reactivated)/unique
     <<" modelReactivation="<<1-double(modeledSurvive)/unique
     <<" signedReactivationDifference="<<(double(reactivated)/unique-(1-double(modeledSurvive)/unique))
     <<" weightedReactivated="<<weightedReact<<" weightedActualReactivation="<<double(weightedReact)/weightedSink
     <<" weightedModelReactivation="<<1-double(modeledWeightedSurvive)/weightedSink
     <<" primeOnlyUnique="<<primeOnly<<" compositeUnique="<<composite<<" unitClassTV="<<double(totalDeviation)<<" minUnitClassCount="<<minCount<<" maxUnitClassCount="<<maxCount<<" mod3ActivatedUnique="<<uniqueMod3<<" highGrowth="<<W<<" totalEvents="<<allEvents<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;vector<int>Xs;for(int k=1;k<argc;k++){int X=atoi(argv[k]);if(X<256||X%4||X>2000000)return 2;Xs.push_back(X);mx=max(mx,X);}setup(8*mx+1000);init_model();for(int X:Xs)scan(X);}
