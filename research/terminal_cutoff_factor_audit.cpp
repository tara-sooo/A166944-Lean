// Exact prime-factor next-hit CRT and synthetic canonical-start scan.
// c++ -O3 -std=c++17 research/terminal_cutoff_factor_audit.cpp -o /tmp/terminal-audit
// /tmp/terminal-audit 1000000
// Synthetic M are NOT necessarily attained records of A166944.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
vector<int> primes;
void initPrimes(int maxM) {
  int bound=(int)sqrtl(8LL*maxM+1000)+100;
  vector<bool> sieve(bound+1,true);
  sieve[0]=sieve[1]=false;
  for(int i=2;i*i<=bound;i++) if(sieve[i])
    for(int j=i*i;j<=bound;j+=i) sieve[j]=false;
  for(int i=3;i<=bound;i+=2) if(sieve[i]) primes.push_back(i);
}
template<class F> void eachOddPrimeFactor(ll n,F callback) {
  for(ll p:primes) {
    if(p*p>n) break;
    if(n%p==0) { callback(p); do {n/=p;} while(n%p==0); }
  }
  ll p=primes.empty()?3:primes.back()+2;
  if(p%2==0) p++;
  for(;p*p<=n;p+=2) if(n%p==0) {
    callback(p); do {n/=p;} while(n%p==0);
  }
  if(n>1) callback(n);
}
bool prime(ll n) {
  if(n<2) return false;
  if(n%2==0) return n==2;
  bool okay=true;
  eachOddPrimeFactor(n,[&](ll p){if(p!=n)okay=false;});
  return okay;
}
pair<ll,ll> nextHit(ll s,ll C) {
  if(s<2||C<6||C%2) throw runtime_error("invalid state");
  ll best=numeric_limits<ll>::max();
  eachOddPrimeFactor(C-1,[&](ll p) {
    ll period=2*p,d=(-s)%period;
    if(d<=0)d+=period;
    best=min(best,s+d);
  });
  eachOddPrimeFactor(C+1,[&](ll p) {
    ll period=2*p,d=(p+2-s)%period;
    if(d<=0)d+=period;
    best=min(best,s+d);
  });
  ll e=gcd(best%2?best-2:best,best%2?C+1:C-1);
  if(e<=1)throw runtime_error("nonhit");
  return {best,e};
}
struct Result {ll M,K,S,C,L,E;bool slow,twins;int events;};
Result trace(ll M) {
  ll s0=M+2,K=(7*M-1)/4,C=2*M-2,S=s0;
  vector<ll> weights; int events=0;
  while(true) {
    auto [r,e]=nextHit(S,C);
    if(r>K)break;
    weights.push_back(4*(r-S)-9*(e-1));
    S=r;C+=e-1;events++;
  }
  ll E=0,sum=0;
  for(int i=(int)weights.size()-1;i>=0;i--) {
    sum+=weights[i];E=max(E,sum);
  }
  if(E>32)throw runtime_error("verified W envelope bound violated");
  ll t=(ll)sqrtl(C+1);
  while((t+1)*(t+1)<=C+1)t++;
  while(t*t>C+1)t--;
  bool slow=4*(K-S)+E>=32+8*t;
  bool twins=prime(C-1)&&prime(C+1);
  auto [J,e]=nextHit(S,C);
  if(J<=K)throw runtime_error("postcutoff hit not later");
  if(twins) {
    if(J!=C+3||e!=C+1)throw runtime_error("twin return mismatch");
  } else {
    if(J-S>2*t)throw runtime_error("composite-side gap mismatch");
    if(M>=968&&C<=2*K&&J>C)
      throw runtime_error("missed short postcutoff hit");
  }
  return {M,K,S,C,K-S,E,slow,twins,events};
}
void directCrossCheck() {
  for(ll M=7;M<=2201;M+=2) {
    auto v=trace(M);
    ll K=(7*M-1)/4,C=2*M-2,S=M+2;
    int count=0;
    for(ll r=S+1;r<=K;r++) {
      ll e=gcd(r%2?r-2:r,r%2?C+1:C-1);
      if(e>1){C+=e-1;S=r;count++;}
    }
    if(v.C!=C||v.S!=S||v.events!=count)
      throw runtime_error("direct gcd cross-check mismatch");
  }
}
int main(int argc,char**argv) {
  int maxM=argc>1?atoi(argv[1]):1000000;
  if(maxM<2201)throw runtime_error("maxM must be >=2201");
  initPrimes(maxM);
  directCrossCheck();
  int tested=0,notSlow=0,notTwin=0;
  ll largestNotSlow=0,largestNotTwin=0;
  vector<ll> badTwin;
  for(ll M=7;M<=maxM;M+=2) {
    auto x=trace(M);tested++;
    if(!x.slow){notSlow++;largestNotSlow=M;}
    if(!x.twins){notTwin++;largestNotTwin=M;badTwin.push_back(M);}
  }
  cout<<"Direct gcd cross-check odd M=7..2201 PASS\n";
  cout<<"Synthetic starts checked="<<tested
      <<" no-slow="<<notSlow<<" max-no-slow="<<largestNotSlow
      <<" non-twin="<<notTwin<<" max-non-twin="<<largestNotTwin<<"\n";
  cout<<"Non-twin synthetic M:";
  for(auto M:badTwin)cout<<" "<<M;
  cout<<"\n";
  if(maxM>=1000000) {
    const vector<ll> expected={11,13,23,25,39,41,43,45,305};
    if(notSlow!=38||largestNotSlow!=365||badTwin!=expected)
      throw runtime_error("one-million audit mismatch");
  }
  cout<<"PASS (finite synthetic audit, NOT a twin-prime infinitude proof)\n";
}
