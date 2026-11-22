// A166944 exact squarefree prime insertion: terminal survivors and last zero states.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/squarefree_survivor_audit.cpp -o survivor_audit
// Run: ./survivor_audit 1024 ; ./survivor_audit 4096 ; ./survivor_audit 16384 ; ./survivor_audit 65536
// Uses the ORIGINAL parity-specific clipped gcd; finite tests only, NO infinite theorem.
#include <bits/stdc++.h>
using namespace std; using ll=long long;
struct Event {int t; int excess; int e;};
vector<int> spf;
vector<int> fact(int z){vector<int> f;while(z>1){int p=spf.at(z);f.push_back(p);do{z/=p;}while(z%p==0);}return f;}
ll nextHit(ll pos,int p,ll r){ll d=(r-pos)%(2LL*p);if(d<=0)d+=2LL*p;return pos+d;}
struct Run{int G=0;int lastEventT=0;int pHits=0;vector<Event> ev;};
Run simulate(int m,int cap){ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;Run out;
 while(pos<K){ll n=K+1;
  for(int p:fact(int(C-1)))if(p<=cap)n=min(n,nextHit(pos,p,0));
  for(int p:fact(int(C+1)))if(p<=cap)n=min(n,nextHit(pos,p,p+2));
  if(n>K)break;
  int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
  for(int p:fact(g))if(p<=cap)e*=p;
  if(e<=1)throw runtime_error("clock failure");
  out.ev.push_back({int(n-m-2),e-1,e});if(cap>1 && e%cap==0)++out.pHits;
  C+=e-1;pos=n;out.lastEventT=int(n-m-2);
 }
 out.G=int(C-(2LL*m-2));return out;
}
// Old-wheel tail begun from an arbitrary even horizon at a first p-hit.
ll tailFromState(ll pos,ll C,ll K,int oldCap){ll initial=C;
 while(pos<K){ll n=K+1;
  for(int r:fact(int(C-1)))if(r<=oldCap)n=min(n,nextHit(pos,r,0));
  for(int r:fact(int(C+1)))if(r<=oldCap)n=min(n,nextHit(pos,r,r+2));
  if(n>K)break;
  int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
  for(int r:fact(g))if(r<=oldCap)e*=r;
  if(e<=1)throw runtime_error("shifted tail clock mismatch");
  C+=e-1;pos=n;
 }return C-initial;
}

int simulateSteps(int m,int cap){int K=(7LL*m-1)/4;ll C=2LL*m-2;for(int n=m+3;n<=K;n++){
 int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;
 for(int p:fact(raw))if(p<=cap)d*=p;
 C+=d-1;
 }return int(C-(2LL*m-2));}
struct Bucket {ll pairs=0,touched=0,positive=0,negative=0,returned=0,prelastPos=0,postlastPos=0,pHits2Pos=0,repeatAfterZero=0;
 ll posCost=0,negCost=0,signedCost=0,terminalAbs=0,totalActivity=0,terminalEpisodeActivity=0;
 ll completedEpisodes=0, terminalEpisodes=0,zeroBeforeFinal=0,terminalAgeSum=0,terminalGapSum=0,lateWithin2p=0,lateWithin4p=0;
 ll posCostHit1=0,posCostHit2=0,posCostOldZero=0,posCostPostLast=0,posCostPreLast=0;
 ll maxEpisode=0,maxDelta=0,maxAbsH=0,positiveTermEvents=0;
 ll postOneCost=0,postOneCount=0,postOneTail=0,postMultiCost=0,postMultiCount=0;
 ll postOneHeight0Cost=0,postOneHeight1Cost=0,postOneHeight2Cost=0;
 ll postOneHeight0Count=0,postOneHeight1Count=0,postOneHeight2Count=0;
 ll postOneMaxTail=0,postOneMaxTailP=0,postOneMaxTailM=0,postOneMaxRatio1000=0;

};
int main(int argc,char**argv){int X=argc>1?atoi(argv[1]):4096;if(X<256||X%2||X>262144)return 2;
 int B=int(ceil(sqrt(7.0*X))),Z=8*X+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int n=p*p;n<Z;n+=p)if(spf[n]==n)spf[n]=p;
 vector<int>primes;for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);
 for(int m=7;m<=119;m+=2)for(int cap:{1,3,5,7,11,13,17})if(simulate(m,cap).G!=simulateSteps(m,cap))throw runtime_error("step/event mismatch");
 Bucket all;vector<int> finalSurvivalAges;
 int prev=1;ll maxPerPrimePos=0,maxPerPrimePosP=0,maxPerPrimeRelative1000=0,maxPerPrimeRelativeP=0,sumFinalG=0;ll witnessReturnedM=0,witnessReturnedP=0,witnessRepeatM=0,witnessRepeatP=0; ll noZeroSignCross=0,negativePrelast=0;
 for(int p:primes){Bucket per;
  for(int m=X+1;m<2*X;m+=2){++per.pairs;Run old=simulate(m,prev), now=simulate(m,p);int K=int((7LL*m-1)/4),Horizon=K-m-2;
   ++all.pairs;int ia=0,ib=0;int H=0,firstT=-1,openT=-1,lastZeroT=0,episodes=0,completed=0,absTime=0,terminalActivity=0,maxH=0;
   int lastOld=old.lastEventT;bool signCross=false;vector<pair<int,int>> changes;
   while(ia<(int)now.ev.size()||ib<(int)old.ev.size()){
    int t=min(ia<(int)now.ev.size()?now.ev[ia].t:INT_MAX,ib<(int)old.ev.size()?old.ev[ib].t:INT_MAX);
    int dn=(ia<(int)now.ev.size()&&now.ev[ia].t==t)?now.ev[ia++].excess:0;
    int do_=(ib<(int)old.ev.size()&&old.ev[ib].t==t)?old.ev[ib++].excess:0;
    int a=dn-do_;if(a==0)continue; if(firstT<0)firstT=t;
    if(H==0){
      // At equal horizons the only possible fresh-wheel split is a p-containing event.
      if(dn!=(p*do_)+(p-1))throw runtime_error("episode did not begin with a fresh-p hit");
      openT=t;++episodes;
    }else if((H>0&&H+a<0)||(H<0&&H+a>0)){signCross=true;}
    H+=a;maxH=max(maxH,abs(H));absTime+=abs(a);changes.push_back({t,a});
    if(H==0){++completed;lastZeroT=t;openT=-1;}
   }
   if(H!=now.G-old.G)throw runtime_error("terminal telescope mismatch");
   if(episodes>now.pHits)throw runtime_error("episodes exceed p-hit count");
   if(!changes.empty()){
     ++per.touched; ++all.touched;
     if(H==0){++per.returned;++all.returned;if(!witnessReturnedM){witnessReturnedM=m;witnessReturnedP=p;}}
     if(completed>0 && episodes>completed && now.pHits<2)throw runtime_error("second episode without p refire");
     if(completed>0 && episodes>completed){++per.zeroBeforeFinal;++all.zeroBeforeFinal;if(!witnessRepeatM){witnessRepeatM=m;witnessRepeatP=p;}}
     if(signCross){++noZeroSignCross;}
     if(H!=0){++per.terminalEpisodes;++all.terminalEpisodes;
       if(openT<0||openT>Horizon)throw runtime_error("bad final episode start");
       per.terminalAgeSum+=Horizon-openT+1;all.terminalAgeSum+=Horizon-openT+1;
       finalSurvivalAges.push_back(Horizon-openT+1);
       per.terminalGapSum+=Horizon-lastZeroT;all.terminalGapSum+=Horizon-lastZeroT;
       if(Horizon-openT<=2*p){++per.lateWithin2p;++all.lateWithin2p;}
       if(Horizon-openT<=4*p){++per.lateWithin4p;++all.lateWithin4p;}
       for(auto [t,a]:changes)if(t>=openT)terminalActivity+=abs(a);
     }
   }
   all.completedEpisodes+=completed;per.completedEpisodes+=completed;
   all.totalActivity+=absTime;per.totalActivity+=absTime;
   all.terminalEpisodeActivity+=terminalActivity;per.terminalEpisodeActivity+=terminalActivity;
   all.maxEpisode=max(all.maxEpisode,ll(episodes));per.maxEpisode=max(per.maxEpisode,ll(episodes));
   all.maxAbsH=max(all.maxAbsH,ll(maxH));per.maxAbsH=max(per.maxAbsH,ll(maxH));
   if(H>0){++all.positive;++per.positive;all.posCost+=H;per.posCost+=H;
    if(now.pHits==1){all.posCostHit1+=H;per.posCostHit1+=H;}else if(now.pHits>=2){all.posCostHit2+=H;per.posCostHit2+=H;++all.pHits2Pos;++per.pHits2Pos;}
    if(old.G==0){all.posCostOldZero+=H;per.posCostOldZero+=H;}
    if(firstT>old.lastEventT){all.posCostPostLast+=H;per.posCostPostLast+=H;++all.postlastPos;++per.postlastPos;
      if(now.pHits==1){
       all.postOneCost+=H;++all.postOneCount;all.postOneTail+=H-(p-1);
       if(H<p-1)throw runtime_error("postfreeze one shot below injection");
       int tail=H-(p-1);
       int tau=m+2+firstT;
       int C=2*m-2+old.G;
       if(tailFromState(tau,C+p-1,K,prev)!=tail)throw runtime_error("shifted one-shot tail identity failed");
       if(tail>all.postOneMaxTail){all.postOneMaxTail=tail;all.postOneMaxTailP=p;all.postOneMaxTailM=m;}
       all.postOneMaxRatio1000=max(all.postOneMaxRatio1000,1000LL*tail/p);
       if(p>=11){int tau=m+2+firstT;int state=2*m-2+old.G+p-1;int z=2*tau-state;
        if(z==0||z==6){all.postOneHeight0Cost+=H;++all.postOneHeight0Count;}
        else if(z==2*p||z==2*p+6){all.postOneHeight1Cost+=H;++all.postOneHeight1Count;}
        else{all.postOneHeight2Cost+=H;++all.postOneHeight2Count;}
       }
      }else if(now.pHits>1){all.postMultiCost+=H;++all.postMultiCount;}
     }
    else{all.posCostPreLast+=H;per.posCostPreLast+=H;++all.prelastPos;++per.prelastPos;}
   }else if(H<0){++all.negative;++per.negative;all.negCost-=H;per.negCost-=H;if(firstT>lastOld)throw runtime_error("postfreeze negative");++negativePrelast;}
   all.signedCost+=H;per.signedCost+=H;all.terminalAbs+=abs(H);per.terminalAbs+=abs(H);all.maxDelta=max(all.maxDelta,ll(abs(H)));per.maxDelta=max(per.maxDelta,ll(abs(H)));
  }
  if(per.posCost>maxPerPrimePos){maxPerPrimePos=per.posCost;maxPerPrimePosP=p;}
  if(per.posCost*1000LL/X>maxPerPrimeRelative1000){maxPerPrimeRelative1000=per.posCost*1000LL/X;maxPerPrimeRelativeP=p;}
  sumFinalG+=per.signedCost;prev=p;
 }
 // independently assert total terminal growth across M
 ll direct=0;int firstGoodM=0,firstTwinLower=0;
 for(int m=X+1;m<2*X;m+=2){int g=simulate(m,prev).G;direct+=g;
  int K=(7LL*m-1)/4,H=K-m-2;
  if(!firstGoodM && H-3*g>=2*B){
   int C=2*m-2+g;
   if(spf.at(C-1)!=(C-1)||spf.at(C+1)!=(C+1))throw runtime_error("terminal prime certificate failed");
   firstGoodM=m;firstTwinLower=C-1;
  }
 }
 if(sumFinalG!=direct || all.posCost-all.negCost!=direct)throw runtime_error("prime telescope mismatch");
 const struct {int X;ll pos,neg,net;} reg[]={{1024,40426,486,39940},{4096,445678,46536,399142},{16384,3439438,524112,2915326},{32768,7171394,602226,6569168},{65536,21585484,1758486,19826998}};
 for(const auto &r:reg)if(X==r.X&&(all.posCost!=r.pos||all.negCost!=r.neg||direct!=r.net))throw runtime_error("historical regression mismatch");
 auto print=[&](const string &name,const Bucket &b){cout<<name<<" pairs="<<b.pairs<<" touched="<<b.touched<<" positive="<<b.positive<<" negative="<<b.negative<<" return="<<b.returned<<" completeEpisodes="<<b.completedEpisodes<<" finalNonzero="<<b.terminalEpisodes<<" multiEpisodeFinal="<<b.zeroBeforeFinal<<" posCost="<<b.posCost<<" negCost="<<b.negCost<<" timeL1="<<b.totalActivity<<" finalEpisodeL1="<<b.terminalEpisodeActivity<<" lateFinal<=2p="<<b.lateWithin2p<<" lateFinal<=4p="<<b.lateWithin4p<<" posPostLast="<<b.posCostPostLast<<" posPreLast="<<b.posCostPreLast<<" posOldG0="<<b.posCostOldZero<<" posOneHit="<<b.posCostHit1<<" posMultiHit="<<b.posCostHit2<<" maxAbsH="<<b.maxAbsH<<"\n";};
 cout<<setprecision(12)<<"PASS X="<<X<<" B="<<B<<" primes="<<primes.size()<<" starts="<<X/2<<" P/X^2="<<(long double)all.posCost/(1LL*X*X)<<" P/(X^2/8)="<<(long double)all.posCost/(1.L*X*X/8)<<" meanGrowth="<<double(direct)/(X/2)<<" meanPositive="<<double(all.posCost)/(X/2)<<"\n";
 print("ALL",all);
 cout<<"PRIME_STAGE_MAX positiveCost="<<maxPerPrimePos<<" at_p="<<maxPerPrimePosP<<" at_ratio_p="<<maxPerPrimeRelativeP<<" maxPosOverX="<<double(maxPerPrimeRelative1000)/1000<<" perPrimeAverageCostOverX="<<double(all.posCost)/(X*primes.size())<<" P_over_XB="<<double(all.posCost)/(X*B)<<"\n";
 cout<<"POSTFREEZE_ONESHOT count="<<all.postOneCount<<" cost="<<all.postOneCost<<" excess_tail="<<all.postOneTail<<" multiCount="<<all.postMultiCount<<" multiCost="<<all.postMultiCost<<" h0="<<all.postOneHeight0Count<<","<<all.postOneHeight0Cost<<" h1="<<all.postOneHeight1Count<<","<<all.postOneHeight1Cost<<" h2plus="<<all.postOneHeight2Count<<","<<all.postOneHeight2Cost<<" maxTail="<<all.postOneMaxTail<<" witnessM="<<all.postOneMaxTailM<<" witnessP="<<all.postOneMaxTailP<<" maxTailPerP="<<double(all.postOneMaxRatio1000)/1000<<"\n";
 sort(finalSurvivalAges.begin(),finalSurvivalAges.end());
 if(finalSurvivalAges.size()!=size_t(all.terminalEpisodes))throw runtime_error("age list mismatch");
 int p50=finalSurvivalAges[finalSurvivalAges.size()/2],p90=finalSurvivalAges[finalSurvivalAges.size()*9/10];
 int hmin=(3*X-6)/4;ll finiteTarget=1LL*X*(hmin-2*B);
 cout<<"SURVIVAL_AGE mean="<<double(all.terminalAgeSum)/all.terminalEpisodes<<" median="<<p50<<" p90="<<p90<<" totalReturned="<<all.returned<<" exampleReSplit="<<witnessRepeatM<<","<<witnessRepeatP<<"\n";
 cout<<"FINITE_CERT criterion6P="<<6*all.posCost<<" limitX*(Hmin-2B)="<<finiteTarget<<" guaranteed="<<(6*all.posCost<finiteTarget)<<" firstGoodM="<<firstGoodM<<" twin="<<firstTwinLower<<","<<firstTwinLower+2<<"\n";
 cout<<"examples touchedTerminalZero="<<witnessReturnedM<<","<<witnessReturnedP<<" multiEpisodeFinal="<<witnessRepeatM<<","<<witnessRepeatP<<" crossedSignWithoutZero="<<noZeroSignCross<<" negativePreLast="<<negativePrelast<<"\n";
}
