// Canonical MIN-prime clock: exact source-weighted selected-prime returns
// by geometric label bands Q<=p<2Q, Q=11*2^j. No stochastic assumptions.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_dyadic_return_audit.cpp -o /tmp/minbands
// /tmp/minbands 256 4096 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;using ll=long long;
static vector<int>spf;
static void sieve(int n){
 spf.resize(n);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)
  for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;
}
static vector<int>fac(int n){
 vector<int>out;
 while(n>1){int p=spf.at(n);out.push_back(p);do{n/=p;}while(n%p==0);}
 return out;
}
static ll gap(ll t,int p,int r){
 ll z=(r-t)%(2LL*p);return z>0?z:z+2LL*p;
}
int main(int argc,char**argv){
 if(argc<2)return 2;
 int largest=0;for(int j=1;j<argc;j++)largest=max(largest,atoi(argv[j]));
 sieve(8*largest+500);
 for(int arg=1;arg<argc;arg++){
  int X=atoi(argv[arg]);if(X<256||X%4)return 2;
  int B=ceil(sqrt(7.0*X));
  vector<ll>F(B+1),R(B+1);
  vector<int>seen(B+1,0);
  int epoch=0;ll totalEvents=0;
  for(int M=X+1;M<2*X;M+=2){
   epoch++;ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   while(t<K){
    ll n=K+1;
    for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
    for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),p=0;
    for(int v:fac(raw))if(v<=B){p=v;break;}
    if(!p)return 3;
    if(p>=11){if(seen[p]==epoch)R[p]++;else{seen[p]=epoch;F[p]++;}}
    C+=p-1;t=n;totalEvents++;
   }
  }
  ll fsum=0,rsum=0;
  for(int p=11;p<=B;p++){fsum+=F[p];rsum+=R[p];}
  cout<<"MIN_RETURN_BANDS X="<<X<<" B="<<B<<" events="<<totalEvents
      <<" F="<<fsum<<" R="<<rsum<<"\n";
  for(int Q=11;Q<=B;Q*=2){
   ll f=0,r=0;
   for(int p=Q;p<=B&&p<2*Q;p++){f+=F[p];r+=R[p];}
   double norm=double(r)*Q/(double(X)*log(2.0*X));
   cout<<" Q="<<Q<<" first="<<f<<" returns="<<r
       <<" normalized_QR_over_Xlog2X="<<norm<<"\n";
  }
 }
}
