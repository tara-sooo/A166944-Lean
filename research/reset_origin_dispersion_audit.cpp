// A166944 squarefree clipped-parity GCD: genuine RESET origin residue dispersion.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror reset_origin_dispersion_audit.cpp -o /tmp/reset_origin_dispersion_audit
// /tmp/reset_origin_dispersion_audit 4096 16384 65536 262144
// Exact finite audit, not a proof of reset-origin equidistribution or twin primes.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using namespace std;
using ll=long long;
static constexpr int P=3*5*7*11, L=2*P;
static vector<int> spf,qs;
static void factors(int n,vector<int>&v){v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}}
static ll next_clock(ll t,int p,int r){ll d=(r-t)%(2LL*p);if(d<=0)d+=2LL*p;return t+d;}
static void setup(int X){int Z=8*X+1000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;}
static vector<int> low_prefix_growths(int r,int z){
 ll t=r+4LL*L,C=2*t-z;vector<int>v{0};
 while(true){ll n=INT64_MAX/4;int d=1;for(int p:{3,5,7,11}){
  int rem=(C-1)%p==0?0:(C+1)%p==0?p+2:-1;
  if(rem>=0)n=min(n,next_clock(t,p,rem));
 }if(n==INT64_MAX/4)break;
 for(int p:{3,5,7,11}){int rem=(C-1)%p==0?0:(C+1)%p==0?p+2:-1;if(rem>=0&&next_clock(t,p,rem)==n)d*=p;}
 if(d<=1)throw runtime_error("low clock mismatch");
 C+=d-1;t=n;v.push_back(v.back()+d-1);
 if(v.size()>23||v.back()>1156)throw runtime_error("low finite bound failed");
 }return v;
}
static int mod(int v,int p){v%=p;if(v<0)v+=p;return v;}
struct Record{int t,z,lastPrime;int M,depth,nextResetT=0,nextResetZ=0;vector<int> lastFactors,nextFactors;};
struct Stat{ll events=0,growth=0,reset=0,high=0,nextHigh=0;};
static vector<Record> collect(int X,int B,Stat&stats){
 vector<Record>records;records.reserve(X);
 vector<int> f,g,df;for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;int pending=-1,pendingReset=-1,depth=0;
  ll initialC=C;
  while(t<K){ll n=K+1;
   factors(int(C-1),f);for(int q:f)if(q<=B)n=min(n,next_clock(t,q,0));
   factors(int(C+1),f);for(int q:f)if(q<=B)n=min(n,next_clock(t,q,q+2));
   if(n>K)break;
   ll raw=gcd((n&1)?n-2:n,(n&1)?C+1:C-1);factors(int(raw),g);
   int d=1;for(int q:g)if(q<=B)d*=q;
   if(d<=1)throw runtime_error("actual next clock invalid");
   ++stats.events;factors(d,df);vector<int>hi;for(int q:df)if(q>=13)hi.push_back(q);
   ll zPost=2*n-(C+d-1);
   if(!hi.empty()){
    ++stats.high;
    if(pending>=0){records.at(pending).nextFactors=hi;++stats.nextHigh;pending=-1;}
    if(zPost==0||((n&1)!=0&&zPost==6)){
     if(!(zPost==(n&1?6:0)))throw runtime_error("spurious reset type");
     ++depth;if(pendingReset>=0){records.at(pendingReset).nextResetT=int(n);records.at(pendingReset).nextResetZ=int(zPost);}
     Record rec{int(n),int(zPost),int(hi.back()),M,depth,0,0,hi,{}};records.push_back(rec);pending=int(records.size())-1;pendingReset=int(records.size())-1;
     ++stats.reset;
    }
   }
   C+=d-1;t=n;
  }
  stats.growth+=C-initialC;
 }
 if(stats.reset!=(ll)records.size())throw runtime_error("record count mismatch");
 return records;
}
static vector<int> rootsets(int z,const vector<int>&pfx,int q){
 vector<int>roots;roots.reserve(pfx.size()*2);
 int inv2=(q+1)/2;
 for(int e:pfx){
  roots.push_back(int(1LL*inv2*mod(z-e+1,q)%q));
  roots.push_back(int(1LL*inv2*mod(z-e-1,q)%q));
 }
 sort(roots.begin(),roots.end());roots.erase(unique(roots.begin(),roots.end()),roots.end());
 return roots;
}
struct Band{ll reset=0,actualHits=0,candidates=0,selfCandidates=0,selfLast=0,distinctTested=0;
 long double expCandidates=0,expAll=0;ll weightedCandidates=0,weightedHits=0,weightedSelf=0;
 ll hitCandidates=0;};
static void run(int X){const int B=int(ceill(sqrtl(7.L*X)));
 qs.clear();for(int q=13;q<=B;q+=2)if(spf[q]==q)qs.push_back(q);
 Stat stats;vector<Record> recs=collect(X,B,stats);
 const struct{int X;ll high,reset,events,growth;} regressions[]={{4096,7675,2865,29349,399142},{16384,45343,14422,171428,2915326},{65536,224221,73941,795689,19826998},{262144,1198498,360413,4082904,138903880}};
 for(auto e:regressions)if(e.X==X&&(stats.high!=e.high||stats.reset!=e.reset||stats.events!=e.events||stats.growth!=e.growth))throw runtime_error("prior high/reset regression mismatch");
 unordered_map<int,int> multiplicity; multiplicity.reserve(recs.size());
 unordered_map<int,int> nextResetByState;nextResetByState.reserve(recs.size());
 ll knownNextReset=0,statesWithNextReset=0;
 for(const auto&r:recs){int id=r.t*2+(r.z==6);multiplicity[id]++;
  if(r.nextResetT){knownNextReset++;int target=r.nextResetT*2+(r.nextResetZ==6);
   auto [it,inserted]=nextResetByState.emplace(id,target);
   if(!inserted&&it->second!=target)throw runtime_error("same reset state has two different next reset states");}
 }
 statesWithNextReset=nextResetByState.size();
 ll distinct=0,collisionEnergy=0,maxMultiplicity=0;
 for(const auto&v:multiplicity){distinct++;collisionEnergy+=1LL*v.second*v.second;maxMultiplicity=max(maxMultiplicity,1LL*v.second);}
 vector<vector<int>> lowCache(2*L);
 for(int z:{0,6})for(int r=0;r<L;r++){
  int key=r+((z==6)?L:0);
  lowCache[key]=low_prefix_growths(r,z);
 }
 int maxStableWidth=0,minStableWidth=INT32_MAX;long double sumStableWidth=0;
 for(int z:{0,6})for(int r=0;r<L;r++){
  const auto&pref=lowCache[r+(z==6?L:0)];vector<int>w;
  for(int e:pref){w.push_back(e-1);w.push_back(e+1);}
  sort(w.begin(),w.end());w.erase(unique(w.begin(),w.end()),w.end());
  int count=int(w.size());maxStableWidth=max(maxStableWidth,count);
  minStableWidth=min(minStableWidth,count);sumStableWidth+=count;
  for(int q:{103,107,127})if(q<=B && spf[q]==q)
   if(rootsets(z,pref,q).size()!=w.size())throw runtime_error("stable root-width lemma violated");
 }
 if(maxStableWidth!=31||minStableWidth!=2)throw runtime_error("low-wheel root width regression mismatch");
 map<int,Band> band, depthBand;long double aggregateExpected=0;ll aggregateCandidates=0,aggregateHits=0,aggregateSelfCandidates=0;
 ll lastqActual=0,largeLastqCandidates=0,largeLastqActual=0;
 long double maxQRatio=0,minQRatio=1e30;int maxQ=0,minQ=0;
 long double weightedAbsDiscrepancy=0,weightedSignedDiscrepancy=0,weightedBaseline=0;
 long double weightedHighAbsDiscrepancy=0,weightedHighPhase=0;ll weightedHighCandidates=0;
 ll weightedObserved=0;ll totalDepth=0,depthMax=0;vector<ll>depthCount(64,0);
 for(const auto&r:recs){totalDepth+=r.depth;depthMax=max(depthMax,1LL*r.depth);if(r.depth>=int(depthCount.size()))throw runtime_error("unexpected reset depth");depthCount[r.depth]++;}
 // For fixed z,r,q, the root set is exact under a uniformly shifted origin t mod q.
 // The genuine reset t's are highly adaptive: this computes their deviations.
 for(int q:qs){
  int bandLo=13;while(bandLo*2<=q)bandLo*=2;
  auto&b=band[bandLo];
  // Precompute root sets for only occupied reset (r,z) residues rather than all 4620.
  unordered_map<int,vector<int>> rootsByCell;rootsByCell.reserve(1600);
  ll qCandidate=0;long double qExpected=0;ll qCandidateAll=0;long double qExpectedAll=0;
  for(const auto&r:recs){
   int cell=r.t%L+(r.z==6?L:0);
   auto it=rootsByCell.find(cell);
   if(it==rootsByCell.end())it=rootsByCell.emplace(cell,rootsets(r.z,lowCache[cell],q)).first;
   const auto&roots=it->second;
   const bool candidate=binary_search(roots.begin(),roots.end(),r.t%q);
   if(q>=103){qExpectedAll+=(long double)roots.size()/q;if(candidate)qCandidateAll++;}
   const bool self=find(r.lastFactors.begin(),r.lastFactors.end(),q)!=r.lastFactors.end();
   const bool hit=find(r.nextFactors.begin(),r.nextFactors.end(),q)!=r.nextFactors.end();
   auto&dep=depthBand[r.depth==1?1:r.depth==2?2:r.depth<=4?3:5];
   if(self){
    b.selfLast++;
    if(candidate){b.selfCandidates++;b.weightedSelf+=q;if(q>=103)largeLastqCandidates++;}
    if(hit){lastqActual++;if(q>=103)largeLastqActual++;}
    if(q>=103&&(candidate||hit))throw runtime_error("q>=103 refired after a reset without another high event");
   }else{
    b.distinctTested++;dep.distinctTested++;
    b.expCandidates+=(long double)roots.size()/q;dep.expCandidates+=(long double)roots.size()/q;qExpected+=(long double)roots.size()/q;
    if(candidate){b.candidates++;b.weightedCandidates+=q;qCandidate++;dep.candidates++;dep.weightedCandidates+=q;}
    if(hit){b.actualHits++;b.weightedHits+=q;dep.actualHits++;dep.weightedHits+=q;if(candidate)b.hitCandidates++;else throw runtime_error("next high q not in low prefix activation candidate");}
   }
  }
  weightedAbsDiscrepancy+=q*fabsl(qCandidate-qExpected);weightedSignedDiscrepancy+=q*(qCandidate-qExpected);
  if(q>=103){weightedHighAbsDiscrepancy+=q*fabsl(qCandidateAll-qExpectedAll);weightedHighPhase+=q*qExpectedAll;weightedHighCandidates+=1LL*q*qCandidateAll;}
  weightedBaseline+=q*qExpected;weightedObserved+=q*qCandidate;
  if(qExpected>=100){long double rat=qCandidate/qExpected;if(rat>maxQRatio){maxQRatio=rat;maxQ=q;}if(rat<minQRatio){minQRatio=rat;minQ=q;}}
 }
 ll highQCount=0,resetRootWidthTotal=0;
 for(int q:qs)if(q>=103)highQCount++;
 for(const auto&r:recs){
  int cell=r.t%L+(r.z==6?L:0);
  const auto&pref=lowCache[cell];
  vector<int>u;
  for(int e:pref){u.push_back(e-1);u.push_back(e+1);}
  sort(u.begin(),u.end());u.erase(unique(u.begin(),u.end()),u.end());
  resetRootWidthTotal+=u.size();
 }
 if(fabsl(weightedHighPhase-highQCount*(long double)resetRootWidthTotal)>0.01L)
  throw runtime_error("exact integer phase total mismatch");
 for(auto &[bandLo,b]:band){
  aggregateCandidates+=b.candidates;aggregateExpected+=b.expCandidates;aggregateHits+=b.actualHits;aggregateSelfCandidates+=b.selfCandidates;
  cout<<fixed<<setprecision(8)<<"BAND X="<<X<<" q=["<<bandLo<<","<<min(2*bandLo,B+1)<<")"
    <<" tests="<<b.distinctTested<<" lastq="<<b.selfLast<<" candidate="<<b.candidates
    <<" phaseExpected="<<(double)b.expCandidates<<" cand_over_phase="<<(double)(b.candidates/b.expCandidates)
    <<" nextHits="<<b.actualHits<<" hitOverCand="<<(double)b.actualHits/max(1LL,b.candidates)
    <<" lastqCandidates="<<b.selfCandidates<<" weightedCandidate="<<b.weightedCandidates<<" weightedHit="<<b.weightedHits<<"\n";
 }
 cout<<fixed<<setprecision(8)<<"RESET X="<<X<<" B="<<B<<" primes="<<qs.size()<<" high="<<stats.high<<" highResets="<<stats.reset
   <<" fullEvents="<<stats.events<<" fullGrowth="<<stats.growth<<" nextHighAfterReset="<<stats.nextHigh<<" distinctResetStates="<<distinct<<" collisionEnergy="<<collisionEnergy
   <<" maxResetMultiplicity="<<maxMultiplicity<<" distinctFraction="<<(double)distinct/stats.reset
   <<" knownNextResetLinks="<<knownNextReset<<" distinctStatesWithNextReset="<<statesWithNextReset
   <<" nonlastCandidate="<<aggregateCandidates<<" nonlastPhaseExpected="<<(double)aggregateExpected
   <<" nonlastCandOverPhase="<<(double)(aggregateCandidates/aggregateExpected)
   <<" nonlastNextHit="<<aggregateHits<<" selfCandidates="<<aggregateSelfCandidates
   <<" lastqActual="<<lastqActual<<" largeLastqCand="<<largeLastqCandidates<<" largeLastqActual="<<largeLastqActual
   <<" widthMin="<<minStableWidth<<" widthMax="<<maxStableWidth<<" widthMean="<<(double)(sumStableWidth/(2*L))
   <<" highQWeightedCandidate="<<weightedHighCandidates<<" highQWeightedPhase="<<(double)weightedHighPhase
   <<" highQAbsError="<<(double)weightedHighAbsDiscrepancy<<" highQAbsRatio="<<(double)(weightedHighAbsDiscrepancy/weightedHighPhase)
   <<" weightedCandidate="<<weightedObserved<<" weightedPhase="<<(double)weightedBaseline
   <<" weightedSignedDiscrepancy="<<(double)weightedSignedDiscrepancy
   <<" weightedAbsoluteDiscrepancy="<<(double)weightedAbsDiscrepancy
   <<" weightedAbsOverPhase="<<(double)(weightedAbsDiscrepancy/weightedBaseline)
   <<" meanDepth="<<(double)totalDepth/stats.reset<<" maxDepth="<<depthMax
   <<" qRatioMin="<<(double)minQRatio<<" qMin="<<minQ<<" qRatioMax="<<(double)maxQRatio<<" qMax="<<maxQ<<"\n";
 if(knownNextReset!=stats.reset-depthCount[1])throw runtime_error("reset depth/renewal link conservation failed");
 cout<<"RESET_DEPTH X="<<X;for(int k:{1,2,3,4,5,6,8,10,15,20,25,30})if(k<int(depthCount.size()))cout<<" ge"<<k<<"="<<accumulate(depthCount.begin()+k,depthCount.end(),0LL)<<" exact"<<k<<"="<<depthCount[k];cout<<"\n";
 for(const auto &[depth,b]:depthBand)cout<<fixed<<setprecision(8)<<"DEPTH X="<<X<<" depth="<<depth
   <<" tests="<<b.distinctTested<<" observed="<<b.candidates<<" expected="<<(double)b.expCandidates
   <<" ratio="<<(double)(b.candidates/b.expCandidates)<<" nextHits="<<b.actualHits
   <<" weightedCandidates="<<b.weightedCandidates<<" weightedHits="<<b.weightedHits<<"\n";
}
static ll literal_growth(int M,int B){
 ll C=2LL*M-2,initial=C,K=(7LL*M-1)/4;
 vector<int>f;
 for(ll n=M+3;n<=K;n++){
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));factors(raw,f);
  int d=1;for(int q:f)if(q<=B)d*=q;
  C+=d-1;
 }
 return C-initial;
}
static ll event_growth(int M,int B){
 ll C=2LL*M-2,initial=C,t=M+2,K=(7LL*M-1)/4;
 vector<int>f;
 while(t<K){ll n=K+1;
  factors(int(C-1),f);for(int q:f)if(q<=B)n=min(n,next_clock(t,q,0));
  factors(int(C+1),f);for(int q:f)if(q<=B)n=min(n,next_clock(t,q,q+2));
  if(n>K)break;
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));factors(raw,f);
  int d=1;for(int q:f)if(q<=B)d*=q;
  if(d<=1)throw runtime_error("independent event-jump mismatch");
  C+=d-1;t=n;
 }
 return C-initial;
}
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;vector<int>xs;
 for(int i=1;i<argc;i++){int x=atoi(argv[i]);if(x<256||(x&1)||x>524288)return 2;xs.push_back(x);mx=max(mx,x);}
 setup(mx);
 for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=event_growth(M,41))
  throw runtime_error("original stepwise parity GCD regression failed");
 for(int X:xs)run(X);
}
