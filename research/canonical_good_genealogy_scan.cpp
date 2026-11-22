// A166944 exact factor-first-hit scan of artificial twin-prime canonical starts.
// Build: g++ -O3 -std=c++17 research/canonical_good_genealogy_scan.cpp -o genealogy
// Run:   ./genealogy 20000000
// Every GOOD parent->child edge is a canonical relay. Roots are ARTIFICIAL;
// none are automatically identified with the original a(1)=2 orbit.
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
struct Row {int M,F,N,R,G;bool good;int depth,parent;};
vector<int> primes;
vector<unsigned char> sieveP;

vector<int> factors(ll n) {
  vector<int> f;
  for(ll p:primes) {
    if(p*p>n)break;
    if(n%p==0){f.push_back(int(p));do{n/=p;}while(n%p==0);}
  }
  if(n>1)f.push_back(int(n));
  return f;
}
bool is_prime(ll n) {
  if(n<2)return false;
  for(ll p:primes){if(p*p>n)break;if(n%p==0)return false;}
  return true;
}
ll next_gap(ll s,ll p,ll t) {
  ll x=(t-s)%(2*p);
  if(x<=0)x+=2*p;
  return x;
}
Row run(int M) {
  ll s=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
  int N=0,R=0;
  unordered_set<int> used;
  while(s<K) {
    ll r=LLONG_MAX;
    for(ll p:factors(C-1))r=min(r,s+next_gap(s,p,0));
    for(ll p:factors(C+1))r=min(r,s+next_gap(s,p,p+2));
    if(r>K)break;
    ll e=gcd((r&1)?r-2:r,(r&1)?C+1:C-1);
    if(e<=1){cerr<<"invalid first hit";exit(2);}
    ++N;
    auto fs=factors(e);
    bool reused=false;
    for(int p:fs)if(used.count(p))reused=true;
    R+=reused;
    for(int p:fs)used.insert(p);
    C+=e-1;
    s=r;
  }
  return {M,int(C+1),N,R,int(C-(2*M-2)),
          is_prime(C-1)&&is_prime(C+1),0,0};
}
int main(int argc,char**argv) {
  const int limit=argc>1?atoi(argv[1]):20000000;
  if(limit<7 || limit>20000000)return 3;
  sieveP.assign(limit+1,1);
  sieveP[0]=sieveP[1]=0;
  for(ll p=2;p*p<=limit;p++)if(sieveP[p])
    for(ll j=p*p;j<=limit;j+=p)sieveP[j]=0;
  for(int p=2;p<=limit;p++)if(sieveP[p])primes.push_back(p);
  unordered_map<int,Row> rows;
  unordered_map<int,pair<int,int>> depthParents;
  unordered_map<int,int> quietParents;
  unordered_map<int,vector<int>> selectedParents;
  rows.reserve(limit/120);
  int starts=0,high=0,highGood=0;
  vector<int> bad,highItems;
  const double threshold=3/(8*sqrt(3.5));
  for(int M=7;M<=limit;M+=2) {
    if(!sieveP[M]||!sieveP[M-2])continue;
    ++starts;
    Row r=run(M);
    auto it=depthParents.find(M);
    if(it!=depthParents.end() && r.good) {
      r.parent=it->second.first;
      r.depth=it->second.second+1;
    }
    if(!r.good)bad.push_back(M);
    if(double(r.R)/sqrt(double(M))>=threshold) {
      ++high;
      highGood+=r.good;
      highItems.push_back(M);
    }
    if(r.good) {
      if(r.N==0)quietParents[r.F]=M;
      if(r.F==28549)selectedParents[r.F].push_back(M);
      auto it2=depthParents.find(r.F);
      if(it2==depthParents.end()||it2->second.second<r.depth)
        depthParents[r.F]={M,r.depth};
    }
    rows.emplace(M,r);
  }
  int highQuiet=0, highDepth3=0,highDepth5=0,maxdepth=0;
  for(int M:highItems) {
    const Row &r=rows.at(M);
    highQuiet+=quietParents.count(M)>0;
    highDepth3+=r.depth>=3;
    highDepth5+=r.depth>=5;
    maxdepth=max(maxdepth,r.depth);
  }
  if(limit==20000000) {
    const auto &w=rows.at(475381), &parent=rows.at(237691);
    const auto &seven=rows.at(113623);
    const vector<int> chain={113623,56713,28183,13999,6961,3463,1723,859};
    int t=113623;
    for(int want:chain){if(t!=want)return 6;t=rows.at(t).parent;}
    if(t!=0||parent.N!=0||parent.F!=475381||w.N!=186||w.R!=157
       ||quietParents.at(475381)!=237691||seven.depth!=7
       ||selectedParents[28549]!=vector<int>({14083,14251})
       ||starts!=107406||bad!=vector<int>({13,43})
       ||high!=165||highGood!=163||highQuiet!=5
       ||highDepth3!=10||highDepth5!=5||maxdepth!=7)return 7;
  }
  cout<<"Twin artificial starts="<<starts<<" BAD="<<bad.size()
      <<" high recycling="<<high<<" high GOOD="<<highGood
      <<" high with quiet GOOD parent="<<highQuiet
      <<" high with depth>=3="<<highDepth3
      <<" high with depth>=5="<<highDepth5
      <<" max GOOD ancestry depth="<<maxdepth<<"\n";
  cout<<"Witness: quiet parent 237691 -> child 475381, N=186 R=157\n";
  cout<<"Witness: 7 GOOD ancestral steps -> child 113623, N=107 R=84\n";
  cout<<"PASS finite exact prime-factor clocks; global upper bound OPEN\n";
  return 0;
}
