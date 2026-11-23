// Reproducible finite cases for the LOW7 plus ONE-large-prime theorem.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low7_large_prime_bridge.cpp -o /tmp/low7_onehigh
// /tmp/low7_onehigh
// The q>=109 result is proved separately using LOW7 time/growth potentials;
// this program exhausts canonical classes only for q<=107 and checks a sharp counterexample.
#include <algorithm>
#include <climits>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static bool prime(int n){if(n<2)return false;for(int d=2;d*d<=n;d++)if(n%d==0)return false;return true;}
struct Event{ll time;int d;ll C;};
static vector<Event> run(ll t,ll C,const vector<int> &primes){
 vector<Event> es;
 for(int k=0;k<2000;k++){
  int gap=INT_MAX;int d=1;
  for(int p:primes){int r=-1;
   if((C-1)%p==0)r=0;
   else if((C+1)%p==0)r=p+2;
   if(r<0)continue;
   int g=int(((r-t)%(2LL*p)+2LL*p)%(2LL*p));if(g==0)g=2*p;
   if(g<gap){gap=g;d=p;}else if(g==gap)d*=p;
  }
  if(d==1)return es;
  t+=gap;C+=d-1;es.push_back({t,d,C});
 }
 throw runtime_error("event guard exceeded");
}
int main(){
 ll total=0,smallReturns=0;int cases=0;
 for(int q=11;q<=107;q+=2){
  if(!prime(q))continue;
  vector<int>ps={3,5,7,q};ll returns=0,firstM=0,maxHits=0,maxEvents=0;
  // All canonical residue classes M mod 2*105*q, M odd.
  for(int M=7;M<7+2*105*q;M+=2){
   auto ev=run(M+2,2LL*M-2,ps);int hits=0;
   for(auto const &e:ev)if(e.d%q==0)hits++;
   if(hits>=2){returns++;if(!firstM)firstM=M;}
   maxHits=max(maxHits,(ll)hits);maxEvents=max(maxEvents,(ll)ev.size());
  }
  if(q>=29 && maxHits>1)throw runtime_error("q>=29 canonical refiring");
  if(q==11&&returns!=15)throw runtime_error("q11 regression");
  if(q==23&&returns!=3)throw runtime_error("q23 regression");
  total+=105LL*q;smallReturns+=returns;cases++;
  cout<<"CANONICAL_ONEHIGH_PASS q="<<q<<" classes="<<105*q<<" maxQHits="<<maxHits
      <<" refireClasses="<<returns<<" witnessM="<<firstM<<" maxEvents="<<maxEvents<<"\n";
 }
 const vector<int>ps={3,5,7,107};auto actual=run(5563,5458,ps);
 if(actual.size()<4 || actual[0].time!=5564||actual[0].d!=107||actual[1].time!=5567||actual[1].d!=105||actual[2].time!=5568||actual[2].d!=3||actual[3].time!=5673||actual[3].d!=107)
  throw runtime_error("q107 sharp counterexample wrong");
 cout<<"POSTQ_107_REFIRE_WITNESS_PASS t0=5563 C0=5458 events=(5564,107),(5567,105),(5568,3),(5673,107)\n";
 cout<<"LOW7_ONEHIGH_FINITE_PASS qcases="<<cases<<" classes="<<total<<" low-q-return-classes="<<smallReturns<<"\n";
}
