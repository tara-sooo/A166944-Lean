// Canonical MIN: stop each source at its FIRST selected high p>=11 reset to h=0/6.
// Keep source multiplicities per (time,height) reset atom and high event counts
// before/after the atom. This supports a first-reset weighted renewal inequality.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_first_reset_transfer.cpp -o /tmp/minfirst
// /tmp/minfirst 256 4096 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <vector>
using namespace std;using ll=long long;
static vector<int>spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)
 for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;
}
static vector<int>fac(int n){vector<int>f;while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
static ll gap(ll t,int p,int r){ll k=(r-t)%(2LL*p);return k>0?k:k+2*p;}
int main(int argc,char**argv){
 if(argc<2)return 2;
 int largest=0;for(int i=1;i<argc;i++)largest=max(largest,atoi(argv[i]));
 sieve(8*largest+500);
 for(int arg=1;arg<argc;arg++){
  int X=atoi(argv[arg]),B=ceil(sqrt(7.0*X));
  unordered_map<ll,int>firstResetWeights;
  ll covered=0,uncovered=0,pre=0,post=0,all=0;
  for(int M=X+1;M<2*X;M+=2){
   ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   bool reached=false;
   while(t<K){
    ll n=K+1;
    for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
    for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),p=0;
    for(int v:fac(raw))if(v<=B){p=v;break;}
    if(!p)return 3;
    C+=p-1;t=n;ll h=2*t-C;
    if(p>=11){all++;if(reached)post++;else pre++;}
    if(!reached&&p>=11&&h==((n&1)?6:0)){
     reached=true;covered++;
     firstResetWeights[2*t+(h==6)]++;
    }
   }
   if(!reached)uncovered++;
  }
  int maxWeight=0;
  for(auto [key,w]:firstResetWeights){(void)key;maxWeight=max(maxWeight,w);}
  if(covered+uncovered!=X/2||pre+post!=all)return 4;
  cout<<"MIN_FIRST_RESET_PASS X="<<X<<" B="<<B
      <<" covered="<<covered<<" uncovered="<<uncovered
      <<" fraction="<<double(covered)/(X/2)
      <<" atoms="<<firstResetWeights.size()<<" maxFibre="<<maxWeight
      <<" highBeforeFirstReset="<<pre<<" highAfterFirstReset="<<post
      <<" totalHigh="<<all<<"\n";
 }
}
