// Exact MIN event-jump: 2p height divisibility, reset surfaces and source fibres.
// Independent per-integer regression in min_prime_gap_height_literal_oracle.py.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_height_reset_coalescence.cpp -o /tmp/minreset
// /tmp/minreset 256 512 1024 4096 65536 262144 1048576
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
 for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
static vector<int>fac(int n){vector<int>v;
 while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}
 return v;
}
static ll gap(ll t,int p,int r){ll z=(r-t)%(2LL*p);
 return z>0?z:z+2LL*p;
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 int largest=0;for(int j=1;j<argc;j++)largest=max(largest,atoi(argv[j]));
 sieve(8*largest+500);
 for(int a=1;a<argc;a++){
  int X=atoi(argv[a]),B=ceil(sqrt(7.0*X));
  unordered_map<ll,int>resets;
  ll top=0,topReset=0,topR=0,topRReset=0,topPreSmall=0,topBigPost=0;
  for(int M=X+1;M<2*X;M+=2){
   ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   vector<uint8_t>seen(B+1,0);
   while(t<K){
    ll n=K+1;
    for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
    for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),p=0;
    for(int v:fac(raw))if(v<=B){p=v;break;}
    if(!p)return 3;
    bool repeated=seen[p];seen[p]=1;
    ll oldHeight=2*t-C;
    C+=p-1;t=n;
    ll h=2*t-C;
    if(h<0 || ((n&1)?h-6:h)%(2*p))return 4;
    bool reset=h==((n&1)?6:0);
    if(p>=11&&2*p>=B){
     top++;topR+=repeated;topPreSmall+=(oldHeight<B);
     topBigPost+=(h>=B);
     if(reset){
      topReset++;topRReset+=repeated;
      resets[2*t+(h==6)]++;
     }
     if(oldHeight<B&&(!reset)){
      bool allowed=(n&1)?(h==6+2*p||h==6+4*p):(h==2*p||h==4*p);
      if(!allowed)return 5;
     }
    }
   }
  }
  int maxWeight=0;
  for(auto [key,w]:resets){(void)key;maxWeight=max(maxWeight,w);}
  cout<<"MIN_HEIGHT_RESET_PASS X="<<X<<" B="<<B<<" top="<<top
      <<" topReset="<<topReset<<" uniqueResetStates="<<resets.size()
      <<" maxSourceFibre="<<maxWeight<<" topReturns="<<topR
      <<" repeatAtReset="<<topRReset<<" preHltB="<<topPreSmall
      <<" postHgeB="<<topBigPost<<"\n";
 }
}
