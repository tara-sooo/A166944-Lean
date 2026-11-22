// Exact squarefree parity-GCD clock-episode and small-event disarming audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror clock_episode_screen_audit.cpp -o clock_episode_screen_audit
// ./clock_episode_screen_audit 4096 16384 65536 262144
// All outputs are finite experiments, not claims of asymptotic theorems.
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
static vector<int> spf, primes;
static void fs(int n,vector<int>&v){v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}}
static ll clockat(ll t,int p,int r){ll d=(r-t)%(2LL*p);if(d<=0)d+=2LL*p;return t+d;}
static ll literal(int M,int B){vector<int> v;ll C=2LL*M-2,K=(7LL*M-1)/4,initial=C;for(ll n=M+3;n<=K;++n){int g=gcd((n&1)?n-2:n,(n&1)?C+1:C-1),d=1;fs(g,v);for(int q:v)if(q<=B)d*=q;C+=d-1;}return C-initial;}
struct Counts{ll root=0,birth=0,hit=0,death=0,terminal=0,hitroot=0,hitbirth=0;
 ll immediate=0,delayed3=0,delayedlarge=0,delayedother=0,side3=0,largeSurvive=0,smallKill=0,otherKill=0;
 ll waitTotal=0,minHit=0,odd3=0,shieldStarts=0,shieldWins=0,unshieldWins=0,screen=0,screenShield=0,screenNoShield=0,failScreen=0,shieldExposure=0; long double predictedScreenShield=0;};
struct Tot{ll starts=0,events=0,growth=0,root=0,birth=0,hit=0,death=0,terminal=0,immediate=0,delayed3=0,delayedlarge=0,delayedother=0,side3=0,largeSurvive=0,smallKill=0,otherKill=0;
 ll rootHits=0,birthHits=0,exposureWeighted=0;
};
static vector<int> factor_active(ll C,int B,vector<int>&f,vector<int>&w){fs(int(C-1),f);fs(int(C+1),w);vector<int> a;for(int q:f)if(q<=B)a.push_back(q);for(int q:w)if(q<=B)a.push_back(q);sort(a.begin(),a.end());return a;}
void run(int X){int B=int(ceill(sqrtl(7.L*X)));vector<Counts> byq(B+1);Tot tot;vector<int> f,w,v,dv;vector<unsigned char> root(B+1),surv3(B+1),survL(B+1),shield(B+1);vector<int> delay(B+1);
 for(int M=X+1;M<2*X;M+=2){++tot.starts;ll C=2LL*M-2,t=M+2,K=(7LL*M-1)/4;ll initial=C;ll sourceWeightedMin=0,sourceWeightedScreen=0;
  auto active=factor_active(C,B,f,w);fill(root.begin(),root.end(),0);fill(shield.begin(),shield.end(),0);fill(surv3.begin(),surv3.end(),0);fill(survL.begin(),survL.end(),0);fill(delay.begin(),delay.end(),0);
  for(size_t idx=0;idx<active.size();++idx){int q=active[idx];byq[q].root++;root[q]=1;shield[q]=idx>0;byq[q].shieldStarts+=idx>0;tot.root++;}
  while(t<K){ll n=K+1;int minActive=active.empty()?B+1:active.front();
   if(!active.empty())tot.exposureWeighted+=1LL*minActive*active.size();
   for(int q:active){int r=(C-1)%q==0?0:q+2;ll candidate=clockat(t,q,r);n=min(n,candidate);
    if(q>minActive){++byq[q].shieldExposure;byq[q].predictedScreenShield+=(long double)min(2LL*minActive,K-t)/(2*q);}
    bool screen=(candidate<=K && (q==minActive || candidate-t<=2LL*minActive));
    if(screen){if(q>2*t-C+4LL*minActive+1)throw runtime_error("screen deficit obstruction failed");
     sourceWeightedScreen+=q;++byq[q].screen;if(q==minActive)++byq[q].screenNoShield;else ++byq[q].screenShield;}
   }
   if(n>K){break;}
   int raw=gcd((n&1)?n-2:n,(n&1)?C+1:C-1),d=1;fs(raw,dv);for(int q:dv)if(q<=B)d*=q;
   if(d<=1){throw runtime_error("non-event clock mismatch");}
   if(d<3){throw runtime_error("invalid d");}
   ll Cnext=C+d-1;auto after=factor_active(Cnext,B,f,w);fs(d,v);tot.events++;tot.growth+=d-1;sourceWeightedMin+=v.front();
   for(int q:active){bool fired=binary_search(v.begin(),v.end(),q);bool stays=binary_search(after.begin(),after.end(),q);
    if(fired){if(q>d)throw runtime_error("fired q>d");++byq[q].hit;++tot.hit;byq[q].waitTotal+=delay[q];
      if(q==v.front())++byq[q].minHit;
      if(q>minActive && n-t>2LL*minActive)throw runtime_error("win without smaller-prime screening");
      if(shield[q])++byq[q].shieldWins;else ++byq[q].unshieldWins;
      if(q==3&&n%2)++byq[q].odd3;
      if(root[q]){++byq[q].hitroot;++tot.rootHits;}else {++byq[q].hitbirth;++tot.birthHits;}
      if(!surv3[q]&&!survL[q]&&delay[q]==0){++byq[q].immediate;++tot.immediate;}
      else if(survL[q]){++byq[q].delayedlarge;++tot.delayedlarge;}
      else if(surv3[q]){++byq[q].delayed3;++tot.delayed3;}
      else {++byq[q].delayedother;++tot.delayedother;}
      if(q>=5&&stays)throw runtime_error("q>=5 hit survived");
      if(q==3&&stays){root[q]=0;shield[q]=0;surv3[q]=survL[q]=0;delay[q]=0;}
      else {root[q]=shield[q]=surv3[q]=survL[q]=0;delay[q]=0;}
    }else if(!stays){++byq[q].death;++tot.death;
      if(q>d+1){++byq[q].smallKill;++tot.smallKill;}else {++byq[q].otherKill;++tot.otherKill;}
      root[q]=shield[q]=surv3[q]=survL[q]=0;delay[q]=0;
    }else {if(q>=5 && d>=5 && (d-3)%q && (d-1)%q && (d+1)%q)
       throw runtime_error("nonfiring survivor does not divide a shifted increment");
      ++delay[q];if(q>d+1){if(d!=3||(C+1)%q)throw runtime_error("q>d+1 unexplained survival");surv3[q]=1;++byq[q].side3;++tot.side3;}
      else{survL[q]=1;++byq[q].largeSurvive;++tot.largeSurvive;}
    }
   }
   for(size_t idx=0;idx<after.size();++idx){int q=after[idx];if(!binary_search(active.begin(),active.end(),q)){++byq[q].birth;++tot.birth;root[q]=surv3[q]=survL[q]=0;shield[q]=idx>0;byq[q].shieldStarts+=idx>0;delay[q]=0;}}
   active.swap(after);C=Cnext;t=n;
  }
  for(int q:active){++byq[q].terminal;++tot.terminal;}
  if(C-initial<0||C-initial>3LL*X)throw runtime_error("growth cap");
  if(C-initial>6+4*sourceWeightedMin || sourceWeightedMin>sourceWeightedScreen)throw runtime_error("screened-clock growth certificate failed");
 }
 long double maxNorm=0,predWeightedShield=0;int maxNormQ=0; ll weightedHits=0,weightedMin=0,weightedScreen=0,weightedBare=0,weightedShield=0;for(int q:primes)if(q<=B){auto &a=byq[q];
   if(q>=5){if(a.root+a.birth!=a.hit+a.death+a.terminal)throw runtime_error("q episode ledger failure");}
   else{if(a.root+a.birth+a.odd3!=a.hit+a.death+a.terminal)throw runtime_error("3 token ledger failed");}
   weightedHits+=1LL*q*a.hit; weightedMin+=1LL*q*a.minHit; weightedScreen+=1LL*q*a.screen;
   weightedBare+=1LL*q*a.screenNoShield;weightedShield+=1LL*q*a.screenShield;predWeightedShield+=q*a.predictedScreenShield;
   auto z=(long double)q*a.hit/(X*sqrtl((long double)B));if(z>maxNorm){maxNorm=z;maxNormQ=q;}
 }
 cout<<setprecision(10)<<"PASS X="<<X<<" B="<<B<<" starts="<<tot.starts<<" events="<<tot.events<<" growth="<<tot.growth<<" roots="<<tot.root<<" births="<<tot.birth<<" hits="<<tot.hit<<" deaths="<<tot.death<<" terminal="<<tot.terminal
 <<" immediate="<<tot.immediate<<" delayed3="<<tot.delayed3<<" delayedlarge="<<tot.delayedlarge<<" delayedother="<<tot.delayedother<<" side3="<<tot.side3<<" largeSurvive="<<tot.largeSurvive<<" smallKill="<<tot.smallKill<<" otherKill="<<tot.otherKill<<" max_qH_norm="<<(double)maxNorm<<" atQ="<<maxNormQ<<" weightedHits="<<weightedHits<<" weightedMin="<<weightedMin<<" weightedScreen="<<weightedScreen<<" screenOverHits="<<(double)weightedScreen/weightedHits<<" weightedMinOverXB2="<<(double)weightedMin/(1.L*X*B*B)<<" weightedBare="<<weightedBare<<" weightedShield="<<weightedShield<<" phaseWeightedShield="<<(double)predWeightedShield<<" shieldPhaseRatio="<<(double)weightedShield/predWeightedShield<<" weightedExposure="<<tot.exposureWeighted<<"\n";
 for(int lo=3;lo<=B;lo*=2){int hi=min(B+1,lo*2);Counts a;int primeCount=0;for(int q:primes)if(q>=lo&&q<hi){++primeCount;auto &z=byq[q];a.root+=z.root;a.birth+=z.birth;a.hit+=z.hit;a.death+=z.death;a.terminal+=z.terminal;a.hitroot+=z.hitroot;a.hitbirth+=z.hitbirth;a.immediate+=z.immediate;a.delayed3+=z.delayed3;a.delayedlarge+=z.delayedlarge;a.delayedother+=z.delayedother;a.side3+=z.side3;a.largeSurvive+=z.largeSurvive;a.smallKill+=z.smallKill;a.otherKill+=z.otherKill;a.minHit+=z.minHit;a.odd3+=z.odd3;a.shieldStarts+=z.shieldStarts;a.shieldWins+=z.shieldWins;a.unshieldWins+=z.unshieldWins;a.screen+=z.screen;a.screenShield+=z.screenShield;a.screenNoShield+=z.screenNoShield;a.shieldExposure+=z.shieldExposure;a.predictedScreenShield+=z.predictedScreenShield;}
  if(primeCount)cout<<"BAND X="<<X<<" ["<<lo<<","<<hi<<") ps="<<primeCount<<" roots="<<a.root<<" born="<<a.birth<<" hits="<<a.hit<<" rootHits="<<a.hitroot<<" birthHits="<<a.hitbirth<<" dies="<<a.death<<" end="<<a.terminal<<" imm="<<a.immediate<<" after3="<<a.delayed3<<" afterLarge="<<a.delayedlarge<<" other="<<a.delayedother<<" smallKill="<<a.smallKill<<" largeSurvive="<<a.largeSurvive<<" win_per_activation="<<(double)a.hit/(a.root+a.birth)<<" minHit="<<a.minHit<<" shieldStarts="<<a.shieldStarts<<" shieldWins="<<a.shieldWins<<" unshieldWins="<<a.unshieldWins<<" screened="<<a.screen<<" screenedShield="<<a.screenShield<<" screenedBare="<<a.screenNoShield<<" screenPerHit="<<(double)a.screen/a.hit<<" shieldExposure="<<a.shieldExposure<<" phaseExpected="<<(double)a.predictedScreenShield<<" screenOverPhase="<<(double)a.screenShield/a.predictedScreenShield<<"\n";
 }
 for(int q:{3,5,7,11,17,31,61,127,257,509,1021})if(q<=B&&spf[q]==q){auto&a=byq[q];cout<<"QSTAT X="<<X<<" q="<<q<<" H="<<a.hit<<" births="<<a.birth<<" deaths="<<a.death<<" root="<<a.root<<" qH/X="<<(double)(q*a.hit)/(double)X<<" win_ratio="<<(double)a.hit/(a.root+a.birth)<<" minHit="<<a.minHit<<" shieldedStartFrac="<<(double)a.shieldStarts/(a.root+a.birth)<<"\n";}
 const struct R{int X;ll E,W;} regression[]={{4096,29349,399142},{16384,171428,2915326},{65536,795689,19826998},{262144,4082904,138903880}};for(const auto&x:regression)if(X==x.X&&(x.E!=tot.events||x.W!=tot.growth))throw runtime_error("historical regression failure");
}
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;vector<int> xs;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X%2||X>262144)return 2;xs.push_back(X);maxX=max(maxX,X);}int Z=8*maxX+1000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;++p)if(spf[p]==p)for(int k=p*p;k<Z;k+=p)if(spf[k]==k)spf[k]=p;for(int p=3;p<=int(ceill(sqrtl(7.L*maxX)));p+=2)if(spf[p]==p)primes.push_back(p);
 for(int M=7;M<=119;M+=2){int B=41;ll C=2LL*M-2,t=M+2,K=(7LL*M-1)/4;vector<int> a,b,tmp;while(t<K){auto v=factor_active(C,B,a,b);ll n=K+1;for(int q:v)n=min(n,clockat(t,q,(C-1)%q==0?0:q+2));if(n>K)break;int g=gcd((n&1)?n-2:n,(n&1)?C+1:C-1),d=1;fs(g,tmp);for(int q:tmp)if(q<=B)d*=q;C+=d-1;t=n;}if(C-(2LL*M-2)!=literal(M,B))throw runtime_error("literal test failure");}
 for(int X:xs)run(X);
}
