// Exact squarefree clipped-GCD simultaneous-prime collision audit for A166944.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror composite_collision_audit.cpp -o audit
// ./audit 4096 16384 65536 262144 1048576
// Original parity-specific recurrence; deterministic finite results, not an asymptotic theorem.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;using ll=long long;
vector<int> spf;
void factors(int n,vector<int>&v){v.clear();while(n>1){int p=spf[n];v.push_back(p);do{n/=p;}while(n%p==0);}}
ll clock_after(ll t,int p,ll residue){ll r=(residue-t)%(2LL*p);if(r<=0)r+=2LL*p;return t+r;}
struct Agg{
 ll starts=0,events=0,growth=0,over=0,composite=0,compositeGrowth=0,oversizeCount=0,oversizeMass=0;
 ll k2=0,k3=0,k4plus=0,k2Over=0,k3Over=0,k4Over=0;
 ll k2OverCost=0,k3OverCost=0,k4OverCost=0;
 ll multPaths=0,oversizePaths=0,allPairs=0,cohitPairs=0,allSameSidePairs=0,allMixedPairs=0;
 ll totalPlateaus=0,totalMultiPlateaus=0,totalActivePrimes=0,totalPossiblePairClocks=0,totalPairHitClocks=0;
 ll maxD=0,maxDM=0,maxDN=0,maxDGap=0,maxDK=0;
 ll highP3=0,highP5=0,highP7=0,highPge11=0;
 ll maxCost2=0,maxCost3=0,maxCost4=0;
 ll events2=0,events3=0,events4=0;
 ll oddOversize=0,evenOversize=0;
 ll largeGFromComposite=0, firstEventComposite=0, allCoHitWitness=0, compositeAtLowDeficit=0;
 ll initialWeight=0,firstMinSum=0;ll sumMinPrime=0, pointwiseViolations=0, gapBoundViolations=0, totalTimeToLast=0, maxRatioNum=0,maxRatioDen=0;
 ll maxE=0,maxEM=0, tailsEhalf=0,tailsEthreequarter=0,tailsElog2=0,ratioGminOver2=0,maxGoverMinM=0;
 long double maxGoverMin=0;
 long double predictedEqualPairs=0, phaseRatio=0, predictedEventPairs=0;
 long double predByDepth[5]={};ll actualByDepth[5]={},hitByDepth[5]={},plateausByDepth[5]={};
 ll phaseShortCircuit=0, oversizeWithHighPreZ=0;
};
ll literal_growth(int M,int B){ll C=2LL*M-2;int K=int((7LL*M-1)/4);vector<int>ff;for(int n=M+3;n<=K;n++){int g=std::gcd((n&1)?n-2:n,(n&1)?int(C+1):int(C-1)),d=1;factors(g,ff);for(int p:ff)if(p<=B)d*=p;C+=d-1;}return C-(2LL*M-2);}
Agg scan(int X){const int B=int(ceill(sqrtl(7.L*X)));Agg a;vector<int> v,ff,u,w;
 for(int M=X+1;M<2*X;M+=2){++a.starts;ll at=M+2,K=(7LL*M-1)/4,C=2LL*M-2;bool hasOversize=false,hasComposite=false;int pathEvents=0;ll sumMinForM=0;ll lastEvent=at;
  factors(int(C-1),v);for(int p:v)if(p<=B)a.initialWeight+=p-1;
  factors(int(C+1),v);for(int p:v)if(p<=B)a.initialWeight+=p-1;
  while(at<K){++a.totalPlateaus;int depthClass=pathEvents==0?0:pathEvents==1?1:pathEvents<=4?2:pathEvents<=19?3:4;++a.plateausByDepth[depthClass];
   factors(int(C-1),v);factors(int(C+1),w);
   vector<pair<int,int>> options;for(int p:v)if(p<=B)options.push_back({p,0});for(int p:w)if(p<=B)options.push_back({p,1});
   a.totalActivePrimes+=options.size();
   ll t=K+1;
   for(auto [p,side]:options){ll candidate=clock_after(at,p,side?p+2:0);t=min(t,candidate);}
   // Audit all active PRIME PAIRS: same-side nontrivial coincidence at next clock.
   bool multipleOptions=false;
   for(size_t i=0;i<options.size();++i)for(size_t j=i+1;j<options.size();++j){
    ++a.allPairs;
    auto [p,side]=options[i];auto [q,side2]=options[j];
    if(side==side2){++a.allSameSidePairs;{long double weight=min(2LL*min(p,q),K-at)/(2.L*p*q);a.predictedEqualPairs+=weight;a.predByDepth[depthClass]+=weight;}}else ++a.allMixedPairs;
    ll x=clock_after(at,p,side?p+2:0),y=clock_after(at,q,side2?q+2:0);
    if(x==y){if(side!=side2)throw runtime_error("opposite parity clocks coincide");if(x<=K){++a.totalPossiblePairClocks;++a.actualByDepth[depthClass]; if(depthClass==0)throw runtime_error("first plateau has simultaneous prime clocks"); if(x==t){++a.totalPairHitClocks;++a.hitByDepth[depthClass];}}}
   }
   if(t>K)break;
   int g=int(std::gcd((t&1)?t-2:t,(t&1)?C+1:C-1)),d=1;factors(g,ff);for(int p:ff)if(p<=B)d*=p;
   if(d<3 || (d%2)==0)throw runtime_error("bad event jump");
   factors(d,u);int omega=int(u.size());
   if(pathEvents==0 && omega>=2)++a.firstEventComposite;
   const ll delta=t-at,deficit=2*at-C;
   if(deficit<0 || (deficit&1))throw runtime_error("deficit invariant");
   if(omega>=2){
     int pmin=u.front(),qnext=u.at(1);
     if(delta>2LL*pmin)throw runtime_error("next prime clock too late");
     ll congr=(t&1)?deficit+2*delta-5:deficit+2*delta+1;
     if(congr<=0 || congr%d)throw runtime_error("composite modular deficit identity failed");
     if(deficit<pmin*(qnext-4LL)-1)throw runtime_error("composite needs large pre-plateau deficit");
     if((t&1)&&deficit<pmin*(qnext-4LL)+5)throw runtime_error("odd composite needs even larger pre-plateau deficit");
     if(deficit<12)++a.compositeAtLowDeficit;
     a.allCoHitWitness+=omega*(omega-1)/2;
     ++a.composite;a.compositeGrowth+=d-1;hasComposite=true;multipleOptions=true;}
   if(multipleOptions)++a.totalMultiPlateaus;
   if(d>B+1){hasOversize=true;++a.oversizeCount;ll cost=d-1-B;a.over+=cost;a.oversizeMass+=d-1;
      if(omega<2)throw runtime_error("oversized non-composite increment");
      if(omega==2){++a.k2Over;a.k2OverCost+=cost;a.maxCost2=max(a.maxCost2,cost);}else if(omega==3){++a.k3Over;a.k3OverCost+=cost;a.maxCost3=max(a.maxCost3,cost);}else{++a.k4Over;a.k4OverCost+=cost;a.maxCost4=max(a.maxCost4,cost);}
      if(t&1)++a.oddOversize;else ++a.evenOversize;
      int p=u.front(); if(p==3)++a.highP3;else if(p==5)++a.highP5;else if(p==7)++a.highP7;else ++a.highPge11;
      if(d>a.maxD){a.maxD=d;a.maxDM=M;a.maxDN=t;a.maxDK=omega;a.maxDGap=t-at;}
   }
   if(omega==2){++a.k2;a.events2++;}else if(omega==3){++a.k3;a.events3++;}else if(omega>=4){++a.k4plus;a.events4++;}
   sumMinForM+=u.front();a.sumMinPrime+=u.front();if(pathEvents==0)a.firstMinSum+=u.front();
   a.events++;a.growth+=d-1;C+=d-1;at=t;lastEvent=at;++pathEvents;
  }
  ll gFinal=C-(2LL*M-2);
  a.maxE=max(a.maxE,0LL+pathEvents);if(pathEvents==a.maxE)a.maxEM=M;
  if(pathEvents>sqrtl(B))++a.tailsEhalf;
  if(pathEvents>powl(B,.75L))++a.tailsEthreequarter;
  if(pathEvents>logl(X)*logl(X))++a.tailsElog2;
  if(sumMinForM){long double rat=(long double)gFinal/sumMinForM;
    if(rat>a.maxGoverMin){a.maxGoverMin=rat;a.maxGoverMinM=M;}
    if(gFinal>2*sumMinForM+6)++a.ratioGminOver2;
  }
  if(gFinal>6+4LL*sumMinForM||gFinal>6+4LL*B*pathEvents)++a.pointwiseViolations;
  if(lastEvent>M+2+2*sumMinForM)++a.gapBoundViolations;
  a.totalTimeToLast+=lastEvent-(M+2);
  if(hasOversize)++a.oversizePaths;
  if(hasComposite)++a.multPaths;
 }
 if(a.pointwiseViolations || a.gapBoundViolations)throw runtime_error("clock budget versus growth fails");
 if(a.firstEventComposite)throw runtime_error("composite at first event, refutes first-hit prime lemma");
 if(a.totalPairHitClocks!=a.allCoHitWitness)throw runtime_error("pair event count does not agree with omega choose 2");
 if(a.composite!=a.k2+a.k3+a.k4plus || a.over!=a.k2OverCost+a.k3OverCost+a.k4OverCost || a.events<a.composite)throw runtime_error("category sum mismatch");
 cout<<setprecision(10)<<"X="<<X<<" B="<<B<<" starts="<<a.starts<<" events="<<a.events<<" growth="<<a.growth<<" oversize_surplus="<<a.over<<" oversized_events="<<a.oversizeCount<<" comp_events="<<a.composite<<" comp_event_fraction="<<double(a.composite)/a.events<<" comp_growth_fraction="<<double(a.compositeGrowth)/a.growth<<"\n";
 cout<<"  OMEGA k2="<<a.k2<<" k3="<<a.k3<<" k4+="<<a.k4plus<<" over2="<<a.k2Over<<" over3="<<a.k3Over<<" over4+="<<a.k4Over<<" over2cost="<<a.k2OverCost<<" over3cost="<<a.k3OverCost<<" over4cost="<<a.k4OverCost<<" compPaths="<<a.multPaths<<" oversizedPaths="<<a.oversizePaths<<"\n";
 cout<<"  MIN_FACTOR oversized_by_3="<<a.highP3<<" 5="<<a.highP5<<" 7="<<a.highP7<<" ge11="<<a.highPge11<<" parityodd="<<a.oddOversize<<" even="<<a.evenOversize<<" max_d="<<a.maxD<<" witness_M="<<a.maxDM<<" n="<<a.maxDN<<" omega="<<a.maxDK<<" gap="<<a.maxDGap<<"\n";
 cout<<"  CLOCK_WEIGHT sum_minprime="<<a.sumMinPrime<<" root_R="<<a.initialWeight<<" ratio_Lambda_over_R="<<double(a.sumMinPrime)/a.initialWeight<<" firstMinSum="<<a.firstMinSum<<" growth_over_4summin="<<double(a.growth)/(4*a.sumMinPrime)<<" time_to_last_over_2summin="<<double(a.totalTimeToLast)/(2*a.sumMinPrime)<<" pointwise_viols="<<a.pointwiseViolations<<" first_event_composite="<<a.firstEventComposite<<"\n";
 cout<<"  EVENT_TAIL mean_E="<<double(a.events)/a.starts<<" max_E="<<a.maxE<<" max_E_at_M="<<a.maxEM<<" E_gt_sqrtB="<<a.tailsEhalf<<" E_gt_B^.75="<<a.tailsEthreequarter<<" E_gt_logX²="<<a.tailsElog2<<" max_G_over_sumMinPrime="<<double(a.maxGoverMin)<<" at_M="<<a.maxGoverMinM<<" G_gt_2sumMin+6="<<a.ratioGminOver2<<"\n";
 cout<<"  PAIRS plateaus="<<a.totalPlateaus<<" activePrimeSum="<<a.totalActivePrimes<<" sameSidePairs="<<a.allSameSidePairs<<" mixedSidePairs="<<a.allMixedPairs<<" pairFirstClockEqual="<<a.totalPossiblePairClocks<<" pairCoincidenceAtNextEvent="<<a.totalPairHitClocks<<" multPlateaus="<<a.totalMultiPlateaus<<" cutoff_adjusted_uniform_phase_expected="<<(double)a.predictedEqualPairs<<" observed_over_predicted="<<double(a.totalPossiblePairClocks/a.predictedEqualPairs)<<" low_deficit_composite="<<a.compositeAtLowDeficit<<"\n";
 cout<<"  DEPTH first/1/2to4/5to19/20plus";for(int k=0;k<5;k++)cout<<" ["<<k<<":plates="<<a.plateausByDepth[k]<<",pred="<<double(a.predByDepth[k])<<",actual="<<a.actualByDepth[k]<<",first="<<a.hitByDepth[k]<<"]";cout<<"\n";
 return a;
}
int main(int argc,char**argv){if(argc<2)return 2;vector<int>Xs;int MaxX=0;for(int i=1;i<argc;i++){int x=atoi(argv[i]);if(x<256||x%2||x>8388608)return 2;Xs.push_back(x);MaxX=max(MaxX,x);}int Z=8*MaxX+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int k=p*p;k<Z;k+=p)if(spf[k]==k)spf[k]=p;
 for(int M=7;M<=119;M+=2){int B=41;ll C=2LL*M-2,at=M+2,K=(7LL*M-1)/4;vector<int>ff,f;while(at<K){ll t=K+1;factors(int(C-1),ff);for(int p:ff)if(p<=B)t=min(t,clock_after(at,p,0));factors(int(C+1),ff);for(int p:ff)if(p<=B)t=min(t,clock_after(at,p,p+2));if(t>K)break;int g=int(std::gcd((t&1)?t-2:t,(t&1)?C+1:C-1)),d=1;factors(g,f);for(int p:f)if(p<=B)d*=p;C+=d-1;at=t;}if(C-(2LL*M-2)!=literal_growth(M,B))throw runtime_error("literal step mismatch");}
 for(int X:Xs){auto a=scan(X);if(X==4096 && a.growth!=399142)throw runtime_error("X4096 growth regression");if(X==16384 && a.growth!=2915326)throw runtime_error("X16384 growth regression");if(X==65536 && a.growth!=19826998)throw runtime_error("X65536 growth regression");if(X==262144 && a.growth!=138903880)throw runtime_error("X262144 growth regression");}
}
