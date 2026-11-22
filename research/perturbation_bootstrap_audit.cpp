// A166944 squarefree wheel: test conjectural bootstrapped stage bound, exact perturbation decomposition.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/perturbation_bootstrap_audit.cpp -o perturbation_bootstrap_audit
// ./perturbation_bootstrap_audit 1024; ./perturbation_bootstrap_audit 4096; ./perturbation_bootstrap_audit 16384
// Finite calculation; nothing herein asserts a uniform estimate.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
struct Ev{int t,e;};
struct Run {int G=0;vector<Ev> ev;};
vector<int> spf;
void factors(int n,vector<int>&fs){fs.clear();while(n>1){int q=spf.at(n);fs.push_back(q);do{n/=q;}while(n%q==0);}}
ll next_hit(ll pos,int q,int r){ll d=(r-pos)%(2LL*q);if(d<=0)d+=2LL*q;return pos+d;}
Run simulate(int M,int cap){ll pos=M+2,K=(7LL*M-1)/4,C=2LL*M-2;Run out;vector<int> fs;
 while(pos<K){ll n=K+1;factors(int(C-1),fs);for(int q:fs)if(q<=cap)n=min(n,next_hit(pos,q,0));factors(int(C+1),fs);for(int q:fs)if(q<=cap)n=min(n,next_hit(pos,q,q+2));if(n>K)break;
 int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));int e=1;factors(g,fs);for(int q:fs)if(q<=cap)e*=q;
 if(e<=1)throw runtime_error("first-hit mismatch");
 C+=e-1;out.ev.push_back({int(n-M-2),e});pos=n;
 }
 out.G=int(C-(2LL*M-2));return out;
}
// First fresh-p clock on the OLD wheel: at least one later new-wheel p hit
// iff this returns true, because both trajectories agree until this clock.
bool old_path_first_p_opportunity(int M,int p,const Run &old){
 ll pos=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
 auto within=[&](ll hi){
  if((C-1)%p==0 && next_hit(pos,p,0)<=hi)return true;
  if((C+1)%p==0 && next_hit(pos,p,p+2)<=hi)return true;
  return false;
 };
 for(const auto &e:old.ev){ll n=M+2+e.t;if(within(n))return true;
  pos=n;C+=e.e-1;
 }
 return within(K);
}
int literal_steps(int M,int cap){ll C=2LL*M-2;int K=int((7LL*M-1)/4);vector<int>fs;for(int n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));int e=1;factors(g,fs);for(int q:fs)if(q<=cap)e*=q;C+=e-1;}return int(C-(2LL*M-2));}
struct Stat{ll pos=0,neg=0,rawInj=0,oldResponse=0,posResponse=0,negResponse=0,timePosResponse=0,onePositive=0,multiPositive=0,nonzero=0,oneHit=0,multiHit=0,postOneTail=0,postOneCost=0,respSquare=0,postTailSquare=0;};

// Demonstrates that the baseline C=2M-2+h with h>=0, C even,
// and the universal quadratic fibre collision budget alone do NOT imply
// near-1/p dispersion of terminal horizons. These are ARTIFICIAL heights,
// not values of the clipped-GCD recurrence.
void check_artificial_sawtooth(int X,int p){
 ll W=0,collisions=0;vector<ll> Cvalues;Cvalues.reserve(X/2);
 for(int m=X+1;m<2*X;m+=2){
  int raw=(p+1-(2*m-2))%(2*p);if(raw<0)raw+=2*p;
  if(raw%2 || raw<0 || raw>2*p-2)throw runtime_error("bad sawtooth parity");
  int C=2*m-2+raw,K=int((7LL*m-1)/4);
  if(C%p!=1 || (C&1) || C>2*K)throw runtime_error("bad fake phase envelope");
  Cvalues.push_back(C);W+=raw;
 }
 sort(Cvalues.begin(),Cvalues.end());
 for(size_t i=0,j;i<Cvalues.size();i=j){j=i+1;while(j<Cvalues.size()&&Cvalues[j]==Cvalues[i])j++;ll k=j-i;collisions+=k*(k-1)/2;}
 if(4*collisions>W)throw runtime_error("fake phase violates collision budget");
 if(X==4096&&p==79&&(W!=159504 || collisions!=39138))throw runtime_error("fake phase regression failed");
}
int main(int argc,char**argv){int X=argc>1?atoi(argv[1]):4096;
 if(X<256||X>262144||(X&1))return 2;
 int B=int(ceil(sqrt(7.0*X))),N=X/2,Z=8*X+1000;spf.resize(Z);iota(spf.begin(),spf.end(),0);
 for(int i=2;1LL*i*i<Z;i++)if(spf[i]==i)for(int j=i*i;j<Z;j+=i)if(spf[j]==j)spf[j]=i;
 for(int M=7;M<=119;M+=2)for(int cap:{1,3,5,7,11,13,17})if(simulate(M,cap).G!=literal_steps(M,cap))throw runtime_error("literal vs jump mismatch");
 if(simulate(127,7).G!=0||simulate(127,11).G!=18||literal_steps(127,11)!=18)throw runtime_error("positive-response/no-old-growth witness fails");
 vector<int> primes;for(int q=3;q<=B;q+=2)if(spf[q]==q)primes.push_back(q);
 if(X==4096)check_artificial_sawtooth(4096,79);else check_artificial_sawtooth(X,primes.back());
 vector<Run> prev(N),next(N);ll Wprev=0,P=0,Neg=0;
 long double maxA=0,maxB=0,maxA0=0,maxOneTailA=0,maxFullA=0;int maxAP=0,maxBP=0,maxOneP=0; long double maxIperX=0,maxRperD=0,maxRtimeD=0;int maxIP=0,maxRP=0,maxRtimeP=0;long double maxActivationRatio=0,maxResponseMoment=0,maxCauchyNorm=0,maxInjSqrt=0;int maxActP=0,maxMomP=0,maxCauchyP=0;
 ll injSum=0, respSum=0, respTimePos=0, respPerSourcePos=0, tailPostOne=0,oneCost=0;ll Nall=0,Qall=0;
 for(int p:primes){Stat st;ll firstMomentOld=Wprev;ll oneTailCnt=0; ll candidate=0,postOneCount=0;vector<int> positiveValues;int largestPositiveM=0,largestPositive=0;
  for(int j=0;j<N;j++){int m=X+1+2*j;Run newer=simulate(m,p);Run &older=prev[j];int del=newer.G-older.G;
    int oldC=2*m-2+older.G; if((oldC-1)%p==0||(oldC+1)%p==0)candidate++;
    if(del>0){positiveValues.push_back(del);if(del>largestPositive){largestPositive=del;largestPositiveM=m;}}
    if(del>0)st.pos+=del;else st.neg-=del;
    if(del!=0)st.nonzero++;
    int seenP=0;int oldLast=older.ev.empty()?0:older.ev.back().t;
    for(const auto &e:newer.ev)if(e.e%p==0)seenP++;
    if(del>0){if(seenP==1)st.onePositive+=del;else st.multiPositive+=del;}
    if(seenP==1)st.oneHit++;else if(seenP>1)st.multiHit++;
    if((seenP>0)!=old_path_first_p_opportunity(m,p,older))throw runtime_error("old-only activation clock mismatch");
    ll inj=0,re=0,rePos=0;size_t a=0,b=0;
    while(a<newer.ev.size()||b<older.ev.size()){
      int t=min(a<newer.ev.size()?newer.ev[a].t:numeric_limits<int>::max(),b<older.ev.size()?older.ev[b].t:numeric_limits<int>::max());
      int eNew=(a<newer.ev.size()&&newer.ev[a].t==t)?newer.ev[a++].e:1;
      int eOld=(b<older.ev.size()&&older.ev[b].t==t)?older.ev[b++].e:1;
      bool hit=eNew%p==0;int eL=hit?eNew/p:eNew;ll jn=hit?(p-1LL)*eL:0;
      ll r=eL-eOld;
      inj+=jn;re+=r;rePos+=max(0LL,r);
    }
    if(inj+re!=del)throw runtime_error("perturbation decomposition failed");
    st.rawInj+=inj;st.oldResponse+=re;st.timePosResponse+=rePos;
    st.posResponse+=max(0LL,re);st.negResponse+=max(0LL,-re);st.respSquare+=max(0LL,re)*max(0LL,re);
    if(del>0&&seenP==1&&!newer.ev.empty()){
      int firstHit=-1;for(const auto &e:newer.ev)if(e.e%p==0){firstHit=e.t;break;}
      if(firstHit>oldLast){st.postOneTail+=del-(p-1);st.postOneCost+=del;oneTailCnt++;postOneCount++;}
    }
    next[j]=move(newer);
  }
  (void)oneTailCnt;
  const long double denomA=X*sqrt((long double)p)+(long double)firstMomentOld/p;
  const long double denomB=X+(long double)firstMomentOld/p;
  const long double denom0=X*sqrt((long double)p);
  auto R=st.pos/denomA;
  if(R>maxA){maxA=R;maxAP=p;}
  if(st.pos/denomB>maxB){maxB=st.pos/denomB;maxBP=p;}
  maxA0=max(maxA0,st.pos/denom0);
  ll activations=st.oneHit+st.multiHit;
  auto ar=(long double)activations*p/X; if(ar>maxActivationRatio){maxActivationRatio=ar;maxActP=p;}
  auto mr=(long double)st.respSquare/(X*(long double)p*p); if(mr>maxResponseMoment){maxResponseMoment=mr;maxMomP=p;}
  auto cs=sqrt((long double)activations*st.respSquare)/(X*sqrt((long double)p));if(cs>maxCauchyNorm){maxCauchyNorm=cs;maxCauchyP=p;}
  maxInjSqrt=max(maxInjSqrt,(long double)st.rawInj/denom0);
  maxFullA=max(maxFullA,(long double)st.rawInj/denomA);
  if((long double)st.rawInj/X>maxIperX){maxIperX=(long double)st.rawInj/X;maxIP=p;}
  if((long double)st.posResponse/denomA>maxRperD){maxRperD=(long double)st.posResponse/denomA;maxRP=p;}
  if((long double)st.timePosResponse/denomA>maxRtimeD){maxRtimeD=(long double)st.timePosResponse/denomA;maxRtimeP=p;}
  if((long double)st.postOneTail/denomA>maxOneTailA){maxOneTailA=(long double)st.postOneTail/denomA;maxOneP=p;}
  if((X==4096&&p==79)||(X==16384&&p==173)||(X==65536&&p==331)||(X==131072&&p==541))cout<<"MOMENT X="<<X<<" p="<<p<<" activations="<<activations<<" Np_over_Xdivp="<<(double)ar<<" Rplus="<<st.posResponse<<" Qresponse="<<st.respSquare<<" Q_over_Xp2="<<(double)mr<<" sqrt_NQ_over_Xsqrtp="<<(double)cs<<" injection_over_Xsqrtp="<<double(st.rawInj/denom0)<<"\n";
  Nall+=activations; Qall+=st.respSquare;
  injSum+=st.rawInj;respSum+=st.oldResponse;respTimePos+=st.timePosResponse;respPerSourcePos+=st.posResponse;tailPostOne+=st.postOneTail;oneCost+=st.onePositive;
  P+=st.pos;Neg+=st.neg;Wprev+=st.pos-st.neg;
  prev.swap(next);
  if((X==4096&&p==79)||(X==16384&&p==173)||(X==65536&&p==331)||(X==131072&&p==541)){
    sort(positiveValues.rbegin(),positiveValues.rend());ll top10=0;for(int i=0;i<min(10,(int)positiveValues.size());i++)top10+=positiveValues[i];
    cout<<"RESONANCE X="<<X<<" p="<<p<<" N="<<N<<" candidate_oldC="<<candidate<<" heuristic_2N/p="<<2.0*N/p<<" posPairs="<<positiveValues.size()<<" posCost="<<st.pos<<" top10Mass="<<top10<<" maxPos="<<largestPositive<<" maxPosM="<<largestPositiveM<<" postOneCount="<<postOneCount<<" postOneCost="<<st.postOneCost<<" postOneTail="<<st.postOneTail<<"\n";
  }
  if(X==4096 || X==16384){
  if(p==11||p==19||p==41||p==79||p==173||p==257||p==331)
    cout<<"STAGE X="<<X<<" p="<<p<<" P="<<st.pos<<" Wold="<<firstMomentOld<<" I="<<st.rawInj<<" R="<<st.oldResponse<<" Rplus="<<st.posResponse<<" Rtimeplus="<<st.timePosResponse<<" postOneTail="<<st.postOneTail<<" normalized="<<(double)R<<"\n";
  }
 }
 const struct {int x;ll p,n,g;} rows[]={{1024,40426,486,39940},{4096,445678,46536,399142},{16384,3439438,524112,2915326},{32768,7171394,602226,6569168},{65536,21585484,1758486,19826998},{131072,49868078,4033062,45835016}};
 for(auto row:rows)if(X==row.x&&(P!=row.p||Neg!=row.n||Wprev!=row.g))throw runtime_error("regression mismatch");
 ll direct=0;for(auto&v:prev)direct+=v.G;if(direct!=Wprev)throw runtime_error("final telescoping failed");
 if(injSum+respSum!=Wprev)throw runtime_error("global perturbation failed");
 const struct{int X;ll N,Q,J;} moments[]={{1024,1588,1577084,27622},{4096,7953,57873748,252670},{16384,32838,1835546388LL,1555068},{32768,66733,2184212120LL,4038216},{65536,140554,12680715456LL,11295926},{131072,285003,25337594692LL,27961802}};
 for(const auto &w:moments)if(X==w.X&&(Nall!=w.N||Qall!=w.Q||injSum!=w.J))throw runtime_error("new activation-response second moment regression failed");
 cout<<setprecision(12)<<"PASS X="<<X<<" B="<<B<<" primes="<<primes.size()<<" P="<<P<<" negative="<<Neg<<" growth="<<Wprev<<"\n";
 cout<<"MAX stage_weak_A="<<double(maxA)<<" at_p="<<maxAP<<" MAX stage_A_linear="<<double(maxB)<<" at_p="<<maxBP<<" MAX without_bootstrap="<<double(maxA0)<<" MAX_injection_A="<<double(maxFullA)<<"\n";
 cout<<"MAX_MOMENTS activation_over_Xdivp="<<double(maxActivationRatio)<<" at_p="<<maxActP<<" Q_over_Xp2="<<double(maxResponseMoment)<<" at_p="<<maxMomP<<" CS_over_Xsqrtp="<<double(maxCauchyNorm)<<" at_p="<<maxCauchyP<<" J_over_Xsqrtp="<<double(maxInjSqrt)<<"\n";
 cout<<"MAX_DIAG injection_per_X="<<double(maxIperX)<<" at_p="<<maxIP<<" response_source_A="<<double(maxRperD)<<" at_p="<<maxRP<<" response_time_A="<<double(maxRtimeD)<<" at_p="<<maxRtimeP<<"\n";
 cout<<"GLOBAL_PRODUCT Nall="<<Nall<<" Qall="<<Qall<<" Jall="<<injSum<<" sqrtNQ="<<double(sqrt((long double)Nall*Qall))<<" JplusSqrt="<<double(injSum+sqrt((long double)Nall*Qall))<<" positive_mass="<<P<<" ratio_upper_to_P="<<double((injSum+sqrt((long double)Nall*Qall))/P)<<" ratio_upper_to_X2over8="<<double((injSum+sqrt((long double)Nall*Qall))/(1.L*X*X/8))<<"\n";
 cout<<"INJECTION total="<<injSum<<" OLD_RESPONSE_signed="<<respSum<<" OLD_RESPONSE_source_pos="<<respPerSourcePos<<" OLD_RESPONSE_time_pos="<<respTimePos<<" postfreeze_onehit_tail="<<tailPostOne<<" positive_onehit_cost="<<oneCost<<" MAX_postOneTail_A="<<double(maxOneTailA)<<" at_p="<<maxOneP<<"\n";
}
