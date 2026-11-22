// A166944 squarefree wheel: exact finite-state small-prime burst audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/small_prime_burst_audit.cpp -o /tmp/small_prime_burst_audit
// /tmp/small_prime_burst_audit 4096 16384 65536
// Mathematical and computational checkpoint, NOT a Lean kernel theorem.
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using i64=long long;
static vector<int> spf;
static void distinct_factors(int n, vector<int>&out){
 out.clear(); while(n>1){int p=spf.at(n);out.push_back(p);do{n/=p;}while(n%p==0);}
}
static int next_offset(int t, int q, int r){
 int a=(r-t)%(2*q);if(a<=0)a+=2*q;return a;
}
struct RestrictedProof {int P=1,maxEvents=0;long long states=0,terminalStates=0;int witnessT=0,witnessC=0;};
static RestrictedProof certify_restricted(const vector<int>&primes){
 RestrictedProof out;for(int q:primes)out.P*=q;
 const int P=out.P, period=2*P, N=period*P;
 out.states=N;
 vector<int> succ(N,-1), indeg(N,0), depth(N,0);
 for(int t=0;t<period;t++)for(int v=0;v<P;v++){
  const int c=2*v,idx=t*P+v;int gap=INT32_MAX,d=1;
  for(int q:primes){
    int r;
    if((c-1)%q==0)r=0;
    else if((c+1)%q==0)r=q+2;
    else continue;
    int e=next_offset(t,q,r);
    if(e<gap){gap=e;d=q;}
    else if(e==gap)d*=q;
  }
  if(gap==INT32_MAX){out.terminalStates++;continue;}
  // Independent direct parity-specific GCD check over the small fixed prime set.
  if(idx%(N/997+1)==0){
    int directDelta=-1,directProduct=1;
    for(int j=1;j<=2*primes.back();j++){
     int n=t+j,raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));
     int product=1;for(int q:primes)if(raw%q==0)product*=q;
     if(product>1){directDelta=j;directProduct=product;break;}
    }
    if(directDelta!=gap||directProduct!=d)throw runtime_error("literal restricted clock mismatch");
  }
  int t2=(t+gap)%period,c2=(c+d-1)%period;
  if(c2&1)throw runtime_error("parity of state changed");
  const int next=t2*P+c2/2;
  succ[idx]=next;indeg[next]++;
 }
 vector<int>queue;queue.reserve(N);
 for(int i=0;i<N;i++)if(indeg[i]==0)queue.push_back(i);
 for(size_t i=0;i<queue.size();i++){
  int s=succ[queue[i]];
  if(s>=0 && --indeg[s]==0)queue.push_back(s);
 }
 if((int)queue.size()!=N)throw runtime_error("restricted finite-state graph contains a nonterminating directed cycle");
 // Reverse of deletion order is a topological order from terminal sinks backward.
 for(int i=N-1;i>=0;i--){int id=queue[i];
  depth[id]=succ[id]<0?0:depth[succ[id]]+1;
  if(depth[id]>out.maxEvents){out.maxEvents=depth[id];out.witnessT=id/P;out.witnessC=2*(id%P);}
 }
 cout<<"FINITE_FSM_CERT primes=";for(int p:primes)cout<<p<<",";
 cout<<" states="<<out.states<<" sinkStates="<<out.terminalStates
     <<" cycles=0 maxEvents="<<out.maxEvents<<" witness_tmod="<<out.witnessT
     <<" witness_Cmod="<<out.witnessC<<"\n";
 return out;
}
static void sieve(int size){spf.resize(size);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<size;p++)if(spf[p]==p)
   for(int k=p*p;k<size;k+=p)if(spf[k]==k)spf[k]=p;
}
static void scan_full(int X,int smallLimit,int maxSmallEvents){
 const int B=int(ceill(sqrtl(7.L*X)));i64 events=0,largeEvents=0,growth=0;
 i64 maxBlock=0,maxLargePerStart=0,maxTotalEvents=0;
 vector<int>f,rawf;
 for(int M=X+1;M<2*X;M+=2){
  i64 t=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
  int E=0,L=0,block=0;
  while(t<K){
   i64 n=K+1;
   distinct_factors(int(C-1),f);
   for(int q:f)if(q<=B)n=min(n,t+next_offset(int(t),q,0));
   distinct_factors(int(C+1),f);
   for(int q:f)if(q<=B)n=min(n,t+next_offset(int(t),q,q+2));
   if(n>K)break;
   int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;
   distinct_factors(raw,rawf);bool large=false;
   for(int q:rawf)if(q<=B){d*=q;if(q>smallLimit)large=true;}
   if(d<=1)throw runtime_error("full wheel clock mismatch");
   if(large){maxBlock=max(maxBlock,(i64)block);block=0;L++;}
   else {block++;if(block>maxSmallEvents)throw runtime_error("small-event burst bound broken");}
   C+=d-1;t=n;E++;
  }
  maxBlock=max(maxBlock,(i64)block);
  if(E>maxSmallEvents+(maxSmallEvents+1)*L)throw runtime_error("burst insertion inequality broken");
  maxLargePerStart=max(maxLargePerStart,(i64)L);
  maxTotalEvents=max(maxTotalEvents,(i64)E);
  events+=E;largeEvents+=L;growth+=C-(2LL*M-2);
 }
 if(X==4096&&(events!=29349||growth!=399142))throw runtime_error("4096 regression broken");
 if(X==16384&&(events!=171428||growth!=2915326))throw runtime_error("16384 regression broken");
 if(X==65536&&(events!=795689||growth!=19826998))throw runtime_error("65536 regression broken");
 cout<<"FULL_WHEEL_PASS X="<<X<<" B="<<B<<" starts="<<X/2
     <<" events="<<events<<" eventsWithPrimeAbove"<<smallLimit<<"="<<largeEvents
     <<" largeFraction="<<double(largeEvents)/events
     <<" maxSmallOnlyBurst="<<maxBlock<<" maxE="<<maxTotalEvents
     <<" maxLargeE="<<maxLargePerStart<<" growth="<<growth<<"\n";
}
int main(int argc,char**argv){
 for(auto primes:vector<vector<int>>{{3},{3,5},{3,5,7},{3,5,7,11}}){
  RestrictedProof p=certify_restricted(primes);
  if(primes.size()==1&&p.maxEvents!=2)throw runtime_error("3 bound regression");
  if(primes.size()==2&&p.maxEvents!=5)throw runtime_error("3*5 bound regression");
  if(primes.size()==3&&p.maxEvents!=9)throw runtime_error("3*5*7 bound regression");
  if(primes.size()==4&&p.maxEvents!=22)throw runtime_error("3*5*7*11 bound regression");
 }
 int maxX=0;vector<int>Xs;
 for(int i=1;i<argc;i++){int x=atoi(argv[i]);if(x<256||x%2||x>1000000)return 2;Xs.push_back(x);maxX=max(maxX,x);}
 if(maxX){sieve(8*maxX+1000);for(int X:Xs)scan_full(X,11,22);}
}
