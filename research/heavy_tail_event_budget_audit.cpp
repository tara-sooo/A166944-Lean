// Exact original parity-specific squarefree clipped-GCD high-initial-weight tail probe.
// Usage: ./heavy_tail_event_budget_audit X [X ...]; X even in [256,10000000].
// Deterministic finite data only: none of the asymptotic tail conjectures is proved.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror heavy_tail_event_budget_audit.cpp -o heavy_tail_event_budget_audit
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
static vector<int> spf;
inline void factor_distinct(int n,vector<int>&a){a.clear();while(n>1){int p=spf[n];a.push_back(p);do{n/=p;}while(n%p==0);}}
inline ll next_clock(ll at,int p,int residue){ll v=(residue-at)%(2LL*p);if(v<=0)v+=2LL*p;return at+v;}
struct Trace{ll G=0,excessOverB=0;int events=0,maxEvent=1,highEvents=0;};
Trace trajectory(int M,int B){
 ll at=M+2,lim=(7LL*M-1)/4,C=2LL*M-2;Trace out;
 vector<int> factors;
 while(at<lim){
   ll n=lim+1;
   factor_distinct(int(C-1),factors);
   for(int p:factors)if(p<=B)n=min(n,next_clock(at,p,0));
   factor_distinct(int(C+1),factors);
   for(int p:factors)if(p<=B)n=min(n,next_clock(at,p,p+2));
   if(n>lim)break;
   int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
   int d=1;factor_distinct(raw,factors);
   for(int p:factors)if(p<=B)d*=p;
   if(d<=1)throw runtime_error("clock mismatch");
   ++out.events;out.maxEvent=max(out.maxEvent,d);if(d-1>B){++out.highEvents;out.excessOverB+=d-1-B;}C+=d-1;at=n;
 }
 out.G=C-(2LL*M-2);return out;
}
ll literal(int M,int B){ll C=2LL*M-2,lim=(7LL*M-1)/4;vector<int> f;
 for(ll n=M+3;n<=lim;n++){
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));int d=1;factor_distinct(raw,f);
  for(int p:f){if(p<=B)d*=p;} C+=d-1;
 }return C-(2LL*M-2);
}
void setup(int maxX){int Z=8*maxX+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;
}
void scan(int X){
 int B=int(ceil(sqrt(7.L*X))),N=X/2;long double cut=logl((long double)X)*logl((long double)X);
 vector<int> f;ll R=0,W=0,small=0,high=0,heavyBad=0,lightBad=0,allBad=0,maxheavyRatioM=0;long double maxheavyRatio=0;
 ll totalEvents=0,totalExcessOverB=0,totalHighEvents=0;ll heavyW=0,lowW=0,heavyR=0,lightR=0, badTotalG=0,heavyBadGrowth=0;ll maxBadWeight=0; ll maxG=0,maxGM=0,maxEvents=0,maxEventD=0,maxEventM=0;ll pathsComposite=0; ll heavyEventsGtW=0,heavyHasHighD=0,heavyUnion=0,heavyEventsGtWAndHigh=0,lightEventsGtW=0;ll allEventsGtLog2=0, allDgtB=0, allUnion=0, allEgtBp75=0, allDgtBp12=0, allUnionPower=0;
 long double Zheavy=0,Zall=0;
 vector<tuple<ll,int,int,int,int>> worst;
 for(int M=X+1;M<2*X;M+=2){
  ll w=0; factor_distinct(2*M-3,f);for(int p:f)if(p<=B)w+=p-1;
  factor_distinct(2*M-1,f);for(int p:f)if(p<=B)w+=p-1;
  Trace t=trajectory(M,B);ll G=t.G;totalEvents+=t.events;totalExcessOverB+=t.excessOverB;totalHighEvents+=t.highEvents; if(G>maxG){maxG=G;maxGM=M;}maxEvents=max(maxEvents,(ll)t.events); if(t.maxEvent>maxEventD){maxEventD=t.maxEvent;maxEventM=M;} if(t.maxEvent>B)pathsComposite++;
  if(G<0||G>3LL*X||((G==0)!=(w==0)))throw runtime_error("horizon/support invariant failure");
  bool heavy=w>cut,bad=G>1LL*B*w; if(t.events>cut)allEventsGtLog2++;if(t.maxEvent>B+1)allDgtB++;if(t.events>cut||t.maxEvent>B+1)allUnion++; if(t.events>powl(B,.75L))allEgtBp75++;if(t.maxEvent>powl(B,1.2L))allDgtBp12++;if(t.events>powl(B,.75L)||t.maxEvent>powl(B,1.2L))allUnionPower++;
  R+=w;W+=G;
  if(heavy){++high;if(t.events>w)heavyEventsGtW++;if(t.maxEvent>B+1)heavyHasHighD++;if(t.events>w || t.maxEvent>B+1)heavyUnion++;if(t.events>w && t.maxEvent>B+1)heavyEventsGtWAndHigh++;heavyW+=G;heavyR+=w;Zheavy+=(long double)G*G/w; if(w>0 && (long double)G/(B*w)>maxheavyRatio){maxheavyRatio=(long double)G/(B*w);maxheavyRatioM=M;}}
  else {++small;if(t.events>w)lightEventsGtW++;lowW+=G;lightR+=w;}
  if(w>0)Zall+=(long double)G*G/w;
  if(bad){++allBad;badTotalG+=G;maxBadWeight=max(maxBadWeight,w);if(heavy){++heavyBad;heavyBadGrowth+=G;worst.push_back({G/(w? w:1),M,int(w),int(G),t.events});}else ++lightBad;}
 }
 sort(worst.rbegin(),worst.rend());
 cout<<fixed<<setprecision(8)<<"X="<<X<<" B="<<B<<" N="<<N<<" R="<<R<<" W="<<W<<" W/R="<<(double)W/R<<" lightN="<<small<<" heavyN="<<high<<" lowW="<<lowW<<" heavyW="<<heavyW
     <<" maxG="<<maxG<<" maxG_M="<<maxGM<<" maxG_div_Blog2="<<(double)(maxG/(B*cut))<<" maxEvents="<<maxEvents<<" maxEventD="<<maxEventD<<" maxEventM="<<maxEventM<<" paths_D_gt_B="<<pathsComposite<<" heavyEgtw="<<heavyEventsGtW<<" heavyLargeD="<<heavyHasHighD<<" heavyUnion="<<heavyUnion<<" heavyBoth="<<heavyEventsGtWAndHigh<<" lightEgtw="<<lightEventsGtW<<" totalE="<<totalEvents<<" meanE="<<(double)totalEvents/N<<" totalOversize="<<totalExcessOverB<<" oversizeWshare="<<(double)totalExcessOverB/W<<" highEvents="<<totalHighEvents<<" EgtLog2="<<allEventsGtLog2<<" DgtB="<<allDgtB<<" union="<<allUnion<<" EgtBp75="<<allEgtBp75<<" DgtBp12="<<allDgtBp12<<" unionPower="<<allUnionPower<<" bad="<<allBad<<" lightBad="<<lightBad<<" heavyBad="<<heavyBad<<" maxBadW="<<maxBadWeight<<" heavyMax_G_over_Bw="<<(double)maxheavyRatio<<" atM="<<maxheavyRatioM<<" heavyBadGrowth="<<heavyBadGrowth<<" weighted_energy_heavy_over_XB2="<<(double)(Zheavy/(X*1.L*B*B))<<"\n";
 for(int i=0;i<min(5,int(worst.size()));i++){auto [ratio,m,w,g,e]=worst[i];cout<<"  HEAVY_WITNESS M="<<m<<" w="<<w<<" G="<<g<<" events="<<e<<" ratio="<<(long double)g/(B*w)<<"\n";}
 if(X==4096&& (R!=149886||W!=399142||allBad!=29))throw runtime_error("X4096 regression");
 if(X==16384&& (R!=1072888||W!=2915326||allBad!=79))throw runtime_error("X16384 regression");
 if(X==65536&& (R!=7889844||W!=19826998||allBad!=219))throw runtime_error("X65536 regression");
 if(X==262144&& (R!=56172030||W!=138903880||allBad!=446))throw runtime_error("X262144 regression");
}
int main(int argc,char **argv){if(argc<2)return 2;vector<int> xs;int mx=0;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X%2||X>10000000)return 2;xs.push_back(X);mx=max(mx,X);}setup(mx);
 for(int M=7;M<=119;M+=2)if(trajectory(M,41).G!=literal(M,41))throw runtime_error("literal mismatch");
 for(int X:xs)scan(X);
}
