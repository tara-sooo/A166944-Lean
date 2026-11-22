// A166944 squarefree clipped-GCD: exact active-prime clock cancellation audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/active_clock_survival_audit.cpp -o /tmp/active_clock_survival_audit
// /tmp/active_clock_survival_audit 4096 16384 65536
// Finite evidence only: the asymptotic winner-clock bound is not proved.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using ll = long long;
static vector<int> spf;
void prime_factors(int n, vector<int>&v){
 v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}
}
ll next_clock(ll t,int q,int r){ll k=(r-t)%(2LL*q);if(k<=0)k+=2LL*q;return t+k;}
int step_increment(ll n,ll C,int B,vector<int>&buf){
 int raw=int(gcd(n%2?n-2:n,n%2?C+1:C-1));
 prime_factors(raw,buf);int d=1;for(int q:buf)if(q<=B)d*=q;return d;
}
ll literal_growth(int M,int B,vector<int>&tmp){
 ll C=2LL*M-2,K=(7LL*M-1)/4;for(ll n=M+3;n<=K;n++)C+=step_increment(n,C,B,tmp)-1;
 return C-(2LL*M-2);
}
struct Stat{
 ll events=0,growth=0,roots=0,births=0,unhitDeaths=0,hitFactors=0,
    odd3Hits=0,smallCompetitions=0,smallKills=0,smallSurvives=0,
    terminalActive=0,composites=0;
 vector<ll> pHits;
 explicit Stat(int B):pHits(B+1,0){}
};
void active_at(ll C,int B,set<int>&active,vector<int>&tmp){
 active.clear();prime_factors(int(C-1),tmp);for(int p:tmp)if(p<=B)active.insert(p);
 prime_factors(int(C+1),tmp);for(int p:tmp)if(p<=B)active.insert(p);
}
void run_X(int X){
 const int B=int(ceill(sqrtl(7.L*X))),N=X/2;
 Stat a(B);vector<int> v,dFactors,tmp;set<int> current,after;
 for(int M=X+1;M<2*X;M+=2){
  ll t=M+2,K=(7LL*M-1)/4,C=2LL*M-2;int E=0;
  active_at(C,B,current,tmp);const ll roots=current.size();a.roots+=roots;
  ll mBirth=0,mUnhitDeath=0,mHits=0,mOdd3=0;
  while(t<K){
   ll n=K+1;
   prime_factors(int(C-1),v);for(int q:v)if(q<=B)n=min(n,next_clock(t,q,0));
   prime_factors(int(C+1),v);for(int q:v)if(q<=B)n=min(n,next_clock(t,q,q+2));
   if(n>K)break;
   const int d=step_increment(n,C,B,v);
   if(d<=1)throw runtime_error("event clock mismatch");
   prime_factors(d,dFactors);if(dFactors.size()>1)a.composites++;
   const ll Cp=C+d-1;active_at(Cp,B,after,tmp);
   for(int q:current){
    const bool fired=binary_search(dFactors.begin(),dFactors.end(),q);
    const bool survives=after.count(q);
    if(!survives && !fired){a.unhitDeaths++;mUnhitDeath++;}
    if(fired){a.hitFactors++;mHits++;a.pHits[q]++;}
    if(fired && q==3 && n%2){a.odd3Hits++;mOdd3++;}
    if(fired && (survives!=(q==3 && n%2)))
      throw runtime_error("firing prime did not disarm correctly");
    if(q>d+1){
      a.smallCompetitions++;
      const bool predicted=(d==3 && (C+1)%q==0);
      if(survives!=predicted)
        throw runtime_error("small-event large-prime cancellation failed");
      if(survives)a.smallSurvives++;else a.smallKills++;
    }
   }
   for(int q:after)if(!current.count(q)){a.births++;mBirth++;}
   C=Cp;t=n;E++;current.swap(after);
  }
  a.events+=E;a.growth+=C-(2LL*M-2);a.terminalActive+=current.size();
  if(roots+mBirth-mUnhitDeath-(mHits-mOdd3)!=(ll)current.size())
    throw runtime_error("active token accounting fails per start");
 }
 if(a.roots+a.births-a.unhitDeaths-a.hitFactors+a.odd3Hits!=a.terminalActive)
  throw runtime_error("global token accounting fails");
 const struct Expected{int X;ll events,growth,roots,births,unhit,smallKills,pHits;} regression[]={
  {4096,29349,399142,5781,54421,31355,27683,29884},
  {16384,171428,2915326,25096,354156,210084,186771,175707},
  {65536,795689,19826998,107744,1806563,1123623,1017497,816075}};
 for(const auto&r:regression)if(X==r.X&&(a.events!=r.events||a.growth!=r.growth||
     a.roots!=r.roots||a.births!=r.births||a.unhitDeaths!=r.unhit||
     a.smallKills!=r.smallKills||a.hitFactors!=r.pHits))
    throw runtime_error("historical regression mismatch");
 long double maxNorm=0;int maxP=0;
 for(int p=3;p<=B;p+=2)if(spf[p]==p){
   long double ratio=(long double)p*a.pHits[p]/(X*sqrtl((long double)B));
   if(ratio>maxNorm){maxNorm=ratio;maxP=p;}
 }
 cout<<fixed<<setprecision(8)<<"PASS X="<<X<<" B="<<B<<" starts="<<N
   <<" events="<<a.events<<" growth="<<a.growth
   <<" rootActive="<<a.roots<<" births="<<a.births
   <<" unhitDeaths="<<a.unhitDeaths<<" smallKills="<<a.smallKills
   <<" smallCompetitions="<<a.smallCompetitions<<" smallSurvives="<<a.smallSurvives
   <<" odd3Hits="<<a.odd3Hits<<" allPrimeHits="<<a.hitFactors
   <<" terminalActive="<<a.terminalActive
   <<" max_pHits_p_over_XsqrtB="<<(double)maxNorm<<" at_p="<<maxP<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;vector<int> xs;int mx=0;
 for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||(X&1)||X>262144)return 2;xs.push_back(X);mx=max(mx,X);}
 const int bound=8*mx+1000;spf.resize(bound);iota(spf.begin(),spf.end(),0);
 for(int i=2;1LL*i*i<bound;i++)if(spf[i]==i)for(int j=i*i;j<bound;j+=i)if(spf[j]==j)spf[j]=i;
 vector<int>tmp;for(int M=7;M<=119;M+=2){
  int B=41;ll C=2LL*M-2,t=M+2,K=(7LL*M-1)/4;
  while(t<K){ll n=K+1;prime_factors(int(C-1),tmp);for(int q:tmp)if(q<=B)n=min(n,next_clock(t,q,0));
   prime_factors(int(C+1),tmp);for(int q:tmp)if(q<=B)n=min(n,next_clock(t,q,q+2));
   if(n>K)break;
   C+=step_increment(n,C,B,tmp)-1; t=n;
  }
  if(C-(2LL*M-2)!=literal_growth(M,B,tmp))throw runtime_error("literal GCD comparison failed");
 }
 for(int X:xs)run_X(X);
}
