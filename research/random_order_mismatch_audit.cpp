// A166944 squarefree wheel prime-order and shared-factor perturbation audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror random_order_mismatch_audit.cpp -o random_order_mismatch_audit
// ./random_order_mismatch_audit 1024 32 20261123
// ./random_order_mismatch_audit 4096 16 20261123
// Experimental finite results; not a Lean proof or uniform asymptotic theorem.
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
struct Event { int n, e; };
struct Run { int G=0; vector<Event> ev; };
vector<int> spf;
vector<int> factors(int x){vector<int> out;while(x>1){int q=spf.at(x);out.push_back(q);do{x/=q;}while(x%q==0);}return out;}
ll first_after(ll pos,int q,ll residue){ll d=(residue-pos)%(2LL*q);if(d<=0)d+=2LL*q;return pos+d;}
Run simulate(int M, const vector<unsigned char>& active){
 const ll K=(7LL*M-1)/4;ll pos=M+2,C=2LL*M-2; Run out;
 while(pos<K){ll hit=K+1;
   for(int q:factors(int(C-1)))if(q<(int)active.size() && active[q])hit=min(hit,first_after(pos,q,0));
   for(int q:factors(int(C+1)))if(q<(int)active.size() && active[q])hit=min(hit,first_after(pos,q,q+2));
   if(hit>K)break;
   int raw=int(gcd((hit&1)?hit-2:hit,(hit&1)?C+1:C-1)),e=1;
   for(int q:factors(raw))if(q<(int)active.size() && active[q])e*=q;
   if(e<=1)throw runtime_error("event clock mismatch");
   C+=e-1; pos=hit; out.ev.push_back({int(hit),e});
 }
 out.G=int(C-(2LL*M-2));return out;
}
int literal(int M,const vector<unsigned char>& active){
 ll C=2LL*M-2,K=(7LL*M-1)/4;
 for(ll n=M+3;n<=K;n++){
  int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
  for(int q:factors(g))if(q<(int)active.size()&&active[q])e*=q;
  C+=e-1;
 }
 return int(C-(2LL*M-2));
}
struct First {int n=0,eold=1;};
First first_hit_old(int M,int p,const Run& old){
  ll pos=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
  auto next_clock=[&](){ll v=K+1;
    if((C-1)%p==0)v=min(v,first_after(pos,p,0));
    if((C+1)%p==0)v=min(v,first_after(pos,p,p+2));
    return v;
  };
  for(const auto& e:old.ev){ll t=next_clock();if(t<=e.n)return {int(t),t==e.n?e.e:1};pos=e.n;C+=e.e-1;}
  ll t=next_clock();if(t<=K)return {int(t),1};return {};
}
struct Tot {
 ll P=0,Neg=0,J=0,R=0,Q=0,N=0,FirstKick=0,firstOldBound=0,W=0;
 ll mismatchEvents=0,mismatchAtNoH=0,overlapHits=0,disagreePrimes=0,biggestR=0;
 long double sumActivationOpportunityRatio=0;
};
Tot scan_order(int X,const vector<int>& order,int B,bool inspectFactors){
 vector<unsigned char> active(B+1,0);
 vector<Run> prev(X/2),next(X/2);
 Tot out;ll Wold=0;
 for(size_t stage=0;stage<order.size();stage++){
  int p=order[stage];active[p]=1;
  for(int j=0;j<X/2;j++){
    int M=X+1+2*j;
    auto v=simulate(M,active);const auto& old=prev[j];
    int delta=v.G-old.G;
    if(delta>0)out.P+=delta;else out.Neg-=delta;
    auto fst=first_hit_old(M,p,old);
    ll inj=0;int nHits=0,hitn=0;for(auto& ev:v.ev)if(ev.e%p==0){inj+=(p-1LL)*(ev.e/p);nHits++;if(!hitn)hitn=ev.n;}
    if((nHits>0)!=(fst.n>0)||((nHits>0)&&(fst.n!=hitn)))throw runtime_error("old-path first clock discrepancy");
    if(fst.n>0){ll kick=(p-1LL)*fst.eold;out.FirstKick+=kick;out.N++;if(kick>inj)throw runtime_error("kick greater than total injection");}
    ll R=delta-inj;out.J+=inj;out.R+=R;out.Q+=max(0LL,R)*max(0LL,R);out.biggestR=max(out.biggestR,R);
    if(inspectFactors){
      size_t a=0,b=0;ll H=0, Co=2LL*M-2;while(a<v.ev.size()||b<old.ev.size()){
        int n=min(a<v.ev.size()?v.ev[a].n:INT32_MAX,b<old.ev.size()?old.ev[b].n:INT32_MAX);
        int en=(a<v.ev.size()&&v.ev[a].n==n)?v.ev[a++].e:1;
        int eo=(b<old.ev.size()&&old.ev[b].n==n)?old.ev[b++].e:1;
        int el=en%p==0?en/p:en;
        int t=n%2?n-2:n;
        ll aa=(n&1)?Co+1:Co-1;
        int dset=1;
        for(int q:factors(t))if(q<=B&&active[q]&&q!=p)dset*=q;
        int shared=std::gcd((ll)dset,llabs(H)),unshared=dset/shared;
        int common=std::gcd((ll)shared,llabs(aa));
        int oldFactor=common*std::gcd((ll)unshared,llabs(aa));
        int newFactor=common*std::gcd((ll)unshared,llabs(aa+H));
        if(oldFactor!=eo || newFactor!=el)throw runtime_error("shared-factor perturbation identity failed");
        int predictedEN=el*((t%p==0&&(aa+H)%p==0)?p:1);
        if(predictedEN!=en)throw runtime_error("new p factored increment mismatch");
        if(el!=eo){out.mismatchEvents++;if(H==0)out.mismatchAtNoH++;}
        int co=gcd(el,eo);
        for(int q:factors(t)) if(q<=B && active[q] && q!=p){
           bool one=(el%q==0),two=(eo%q==0);
           if(q!=p && H%q==0 && one!=two)throw runtime_error("q|H but membership differs");
           if(one&&two && co%q!=0)throw runtime_error("common factor missing");
           if(one!=two){out.disagreePrimes++;if(H%q==0)throw runtime_error("disagreement prime divides H");}
        }
        Co+=eo-1;H+=en-eo;
      }
      if(H!=delta)throw runtime_error("perturbation mismatch");
    }
    next[j]=move(v);
  }
  // On old wheel with all p unadded, any next first p-clock's kick
  // is bounded in aggregate by 7 B (1 + 3 G_old/2).
  Wold+=0;prev.swap(next);
 }
 out.W=accumulate(prev.begin(),prev.end(),0LL,[](ll a,const Run& b){return a+b.G;});
 if(out.J+out.R!=out.W || out.P-out.Neg!=out.W)throw runtime_error("order-wide telescope failure");
 return out;
}
void check_old_all_options(int X,int B,const vector<int>& primes, int completedStages){
  vector<unsigned char> mask(B+1,0);for(int i=0;i<completedStages;i++)mask[primes[i]]=1;
  ll maxRatioN=0, failures=0, sumF=0,sumBound=0,sumW=0;
  for(int M=X+1;M<2*X;M+=2){
    Run old=simulate(M,mask);
    ll sum=0;for(int p:primes)if(!mask[p]){auto f=first_hit_old(M,p,old);if(f.n)sum+=(p-1LL)*f.eold;}
    ll bound=7LL*B*(1+3LL*old.G/2); // floor 1.5G; all G even
    if(sum>bound){failures++;if(failures<=2)cerr<<"old-options failure M="<<M<<" sum="<<sum<<" bound="<<bound<<"\n";}
    sumF+=sum;sumBound+=bound;sumW+=old.G;
    maxRatioN=max(maxRatioN,bound?sum*1000000/bound:0LL);
  }
  if(failures)throw runtime_error("candidate first-kick bound false");
  cout<<"OLD_OPTIONS_PASS X="<<X<<" stage="<<completedStages<<" options="<<primes.size()-completedStages<<" avg_firstkick_sum="<<(double)sumF/(X/2)<<" avg_bound="<<(double)sumBound/(X/2)<<" avg_oldG="<<(double)sumW/(X/2)<<" max_actual_to_bound="<<maxRatioN/1000000.0<<"\n";
}
int main(int argc,char**argv){
 int X=argc>1?atoi(argv[1]):1024, trials=argc>2?atoi(argv[2]):32;unsigned seed=argc>3?unsigned(strtoul(argv[3],nullptr,10)):20261123U;
 if(X<256||X>32768||(X%2)||trials<0||trials>500)return 2;
 int B=int(ceil(sqrt(7.0*X))),Z=8*X+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);
 for(int q=2;1LL*q*q<Z;q++)if(spf[q]==q)for(int t=q*q;t<Z;t+=q)if(spf[t]==t)spf[t]=q;
 vector<int> primes;for(int q=3;q<=B;q+=2)if(spf[q]==q)primes.push_back(q);
 vector<unsigned char> full(B+1,0);for(int q:primes)full[q]=1;
 for(int M=7;M<120;M+=2){vector<unsigned char> few(B+1,0);for(int p:primes)if(p<=min(B,17))few[p]=1;if(simulate(M,few).G!=literal(M,few))throw runtime_error("literal mismatch");}
 check_old_all_options(X,B,primes,0);
 check_old_all_options(X,B,primes,(int)primes.size()/2);
 auto asc=scan_order(X,primes,B,true);vector<int> reversed=primes;reverse(reversed.begin(),reversed.end());auto desc=scan_order(X,reversed,B,true);
 if(asc.W!=desc.W)throw runtime_error("terminal total depends on prime order");
 if(X==512 && (asc.P!=26042||asc.W!=20048))throw runtime_error("baseline 512 regression");
 if(X==1024 && (asc.P!=40426||asc.W!=39940))throw runtime_error("baseline 1k regression");
 if(X==4096 && (asc.P!=445678||asc.W!=399142))throw runtime_error("baseline 4k regression");
 if(X==8192 && (asc.P!=1167152||asc.W!=1084898))throw runtime_error("baseline 8k regression");
 ll direct=0;for(int M=X+1;M<2*X;M+=2)direct+=simulate(M,full).G;
 if(direct!=asc.W)throw runtime_error("independent full-set terminal check failed");
 auto show=[&](const char*label,const Tot&a){cout<<label<<" P="<<a.P<<" P_over_XB="<<setprecision(9)<<(double)a.P/(X*B)<<" W="<<a.W<<" J="<<a.J<<" R="<<a.R<<" Q="<<a.Q<<" N="<<a.N<<" firstKick="<<a.FirstKick<<" mismatchEvents="<<a.mismatchEvents<<" mismatchAtH0="<<a.mismatchAtNoH<<" disagreePrimeEvents="<<a.disagreePrimes<<"\n";};
 cout<<"PASS X="<<X<<" B="<<B<<" primes="<<primes.size()<<" trials="<<trials<<" seed="<<seed<<"\n";
 show("ASC",asc);show("DESC",desc);
 mt19937_64 eng(seed);long double sumP=0,sumJ=0,sumQ=0,sumN=0,sumK=0,sumCS=0,minP=1e99,maxP=0;int lessAsc=0;
 for(int rep=0;rep<trials;rep++){
   auto perm=primes;shuffle(perm.begin(),perm.end(),eng);
   auto u=scan_order(X,perm,B,rep==0);if(u.W!=asc.W)throw runtime_error("random order terminal growth changed");
   minP=min(minP,(long double)u.P);maxP=max(maxP,(long double)u.P);if(u.P<asc.P)lessAsc++;
   sumP+=u.P;sumJ+=u.J;sumQ+=u.Q;sumN+=u.N;sumK+=u.FirstKick;sumCS+=u.J+sqrt((long double)u.N*u.Q);
   if(rep<5)show((string("RAND")+to_string(rep)).c_str(),u);
 }
 if(trials)cout<<"RANDOM_SUMMARY avgP="<<(double)(sumP/trials)<<" minP="<<(double)minP<<" maxP="<<(double)maxP<<" fraction_below_ASC="<<(double)lessAsc/trials<<" avgJ="<<(double)sumJ/trials<<" avgQ="<<(double)sumQ/trials<<" avgN="<<(double)sumN/trials<<" avgFirstKick="<<(double)sumK/trials<<" avgCS_upper="<<(double)(sumCS/trials)<<"\n";
 long double bsumP=0, bsumQ=0, bsumCS=0, bminP=1e99, bmaxP=0;int bbetter=0;
 for(int rep=0;rep<trials;rep++){
   auto perm=primes;int start=0;
   while(start<(int)perm.size()){
      int right=1;while(2*right<=perm[start])right*=2;
      int stop=start;while(stop<(int)perm.size()&&perm[stop]<2*right)stop++;
      shuffle(perm.begin()+start,perm.begin()+stop,eng);start=stop;
   }
   auto u=scan_order(X,perm,B,false);if(u.W!=asc.W)throw runtime_error("dyadic block order terminal changed");
   bsumP+=u.P;bsumQ+=u.Q;bsumCS+=u.J+sqrt((long double)u.N*u.Q);bminP=min(bminP,(long double)u.P);bmaxP=max(bmaxP,(long double)u.P);if(u.P<asc.P)bbetter++;
 }
 if(trials)cout<<"BLOCK_RANDOM_SUMMARY avgP="<<(double)(bsumP/trials)<<" minP="<<(double)bminP<<" maxP="<<(double)bmaxP<<" fraction_below_ASC="<<(double)bbetter/trials<<" avgQ="<<(double)(bsumQ/trials)<<" avgCS_upper="<<(double)(bsumCS/trials)<<"\n";
}
