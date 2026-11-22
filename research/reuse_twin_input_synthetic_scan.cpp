// Exact first-hit replay for artificial canonical-shaped TWIN-PRIME starts.
// This scans ALL twin prime input pairs M-2,M up to maxM, but DOES NOT
// assert these starts are reached by the actual A166944 recurrence.
// Build: c++ -O3 -std=c++17 research/reuse_twin_input_synthetic_scan.cpp -o /tmp/twin-scan
// Run: /tmp/twin-scan 20000000
#include <bits/stdc++.h>
using namespace std;
using ll=long long;

vector<int> sieve(int n) {
  vector<int> sp(n+1);
  for (int i=2;i<=n;i++) if (!sp[i]) {
    for (int j=i;j<=n;j+=i) if (!sp[j]) sp[j]=i;
  }
  return sp;
}
vector<ll> factors(ll n,const vector<int>&primes) {
  vector<ll> f;
  for (ll p:primes) {
    if (p*p>n) break;
    if (n%p==0) {
      f.push_back(p);
      do { n/=p; } while (n%p==0);
    }
  }
  if (n>1) f.push_back(n);
  return f;
}
ll positive_distance(ll s,ll p,ll target) {
  const ll m=2*p;
  ll x=(target-s)%m;
  if(x<=0)x+=m;
  return x;
}
bool isprime(ll n,const vector<int>&primes) {
  if(n<2)return false;
  const auto fs=factors(n,primes);
  return fs.size()==1&&fs[0]==n;
}
int main(int argc,char**argv) {
  const int maxM=argc>1?atoi(argv[1]):1000000;
  auto sp=sieve(maxM+100);
  vector<int> primes;
  for(int i=2;i<=maxM+100;i++)if(sp[i]==i)primes.push_back(i);
  ll starts=0,violate=0,violate5k=0,violate100k=0;
  double bestRatio=0;
  ll bestM=0,bestN=0,bestR=0,bestC=0;
  const double threshold=3.0/(8.0*sqrt(3.5));
  for(ll M=7;M<=maxM;M+=2) {
    if (sp[M]!=M||sp[M-2]!=M-2)continue;
    ++starts;
    ll K=(7*M-1)/4, s=M+2,C=2*M-2;
    ll N=0,R=0;
    unordered_set<ll> used;
    while(s<K) {
      ll j=LLONG_MAX;
      for(ll p:factors(C-1,primes))
        j=min(j,s+positive_distance(s,p,0));
      for(ll p:factors(C+1,primes))
        j=min(j,s+positive_distance(s,p,p+2));
      if(j>K)break;
      ll e=gcd((j&1)?j-2:j,(j&1)?C+1:C-1);
      if(e<=1)return 2;
      ++N;
      auto fs=factors(e,primes);
      bool repeat=false;
      for(ll p:fs)if(used.count(p))repeat=true;
      if(repeat)++R;
      for(ll p:fs)used.insert(p);
      s=j;
      C+=e-1;
    }
    double ratio=double(R)/sqrt(double(M));
    if(ratio>=threshold) {
      ++violate;
      if(M>=5000)++violate5k;
      if(M>=100000)++violate100k;
    }
    if(ratio>bestRatio) {
      bestRatio=ratio;
      bestM=M;
      bestN=N;
      bestR=R;
      bestC=C;
    }
  }
  cout<<"starts="<<starts<<" threshold="<<fixed<<setprecision(8)
      <<threshold<<" above_threshold="<<violate
      <<" above_for_M>=5000="<<violate5k
      <<" above_for_M>=100000="<<violate100k<<"\n";
  cout<<"largest_ratio="<<bestRatio<<" M="<<bestM
      <<" N="<<bestN<<" R="<<bestR<<" C="<<bestC
      <<" start_twin="<<(isprime(bestM,primes)&&isprime(bestM-2,primes))
      <<" terminal_twin="<<(isprime(bestC-1,primes)&&isprime(bestC+1,primes))
      <<"\n";
  if(maxM==20000000) {
    if(starts!=107406||violate!=165||violate5k!=136||
       violate100k!=49||bestM!=28549||bestN!=177||bestR!=153||
       bestC!=60648)return 3;
  }
  return 0;
}
