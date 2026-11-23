// Actual final squarefree parity-GCD single-high-donor q-return source multiplicity.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low7_one_donor_reuse_scan.cpp -o /tmp/one_donor
// /tmp/one_donor 16384; /tmp/one_donor 65536
// A donor is ONE non-q event containing at least one prime >=11, even if composite.
// The tracked pair (q,r) uses the unique >=11 factor r when there is only one.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <tuple>
#include <vector>
using namespace std;
using ll=long long;
static vector<int>spf;
static void sieve(int n){
 spf.resize(n);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)
  for(int z=p*p;z<n;z+=p)if(spf[z]==z)spf[z]=p;
}
static void factor(int n,vector<int>&f){
 f.clear();while(n>1){int p=spf[n];f.push_back(p);do{n/=p;}while(n%p==0);}
}
static int gap(ll t,int p,int r){
 ll x=(r-t)%(2LL*p);return int(x>0?x:x+2*p);
}
int main(int argc,char**argv){
 int X=argc>1?atoi(argv[1]):16384;
 if(X<256||X>262144||X%4)return 2;
 int B=int(ceill(sqrtl(7.L*X)));
 sieve(8*X+200);
 vector<int> f;
 int repeatedPair=0,maxPairInSource=0,witnessM=0,witnessQ=0,witnessR=0;
 ll one=0,multi=0,zero=0;
 map<tuple<int,int>,ll> perPair;
 for(int M=X+1;M<2*X;M+=2){
  ll c=2LL*M-2,t=M+2,K=(7LL*M-1)/4;
  vector<vector<int>>events;
  while(t<K){
   ll n=K+1;
   factor(int(c-1),f);
   for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));
   factor(int(c+1),f);
   for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));
   if(n>K)break;
   int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1)),d=1;
   factor(raw,f);vector<int>labels;
   for(int p:f)if(p<=B){d*=p;labels.push_back(p);}
   events.push_back(labels);c+=d-1;t=n;
  }
  map<int,int>last;
  map<pair<int,int>,int>localPairs;
  for(int k=0;k<int(events.size());k++)for(int q:events[k])if(q>=11){
   auto it=last.find(q);
   if(it!=last.end()){
    int donors=0,r=0;
    for(int j=it->second+1;j<k;j++){
     int hi=0;
     for(int p:events[j])if(p>=11){hi++;r=p;}
     if(hi)donors++;
     if(hi>1)r=-1;
    }
    if(donors==0)zero++;
    else if(donors==1){
     one++;perPair[{q,r}]++;
     int v=++localPairs[{q,r}];
     if(v==2){
      repeatedPair++;
      if(!witnessM){witnessM=M;witnessQ=q;witnessR=r;}
     }
     maxPairInSource=max(maxPairInSource,v);
    } else multi++;
   }
   last[q]=k;
  }
 }
 ll maxTotalPerPair=0;int qtop=0,rtop=0;
 for(const auto&it:perPair)if(it.second>maxTotalPerPair){
  maxTotalPerPair=it.second;qtop=get<0>(it.first);rtop=get<1>(it.first);
 }
 if(X==16384&&(zero!=646||one!=4373||multi!=12698||
      witnessM!=22689||witnessQ!=11||witnessR!=17))
  return 4;
 cout<<"ONE_DONOR_SOURCE_PASS X="<<X<<" B="<<B
     <<" zero="<<zero<<" one="<<one<<" multiple="<<multi
     <<" largest_same_M_pair="<<maxPairInSource
     <<" repeated_source_pairs="<<repeatedPair
     <<" witness_M="<<witnessM<<" q="<<witnessQ<<" r="<<witnessR
     <<" max_total_for_pair="<<maxTotalPerPair<<" at_q="<<qtop<<" at_r="<<rtop
     <<" unique_pairs="<<perPair.size()<<"\n";
}
