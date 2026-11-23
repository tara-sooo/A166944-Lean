// Original parity-GCD squarefree FINAL-wheel event-jump auditor.
// Counts ALL q-bearing events (not only high minimum-owner labels).
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/high_band_return_audit.cpp -o /tmp/high_band
// Run:   /tmp/high_band 4096 16384 65536 262144
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
static void sieve(int n) {
  spf.resize(n); iota(spf.begin(),spf.end(),0);
  for(int p=2;1LL*p*p<n;p++) if(spf[p]==p)
    for(int j=p*p;j<n;j+=p) if(spf[j]==j) spf[j]=p;
}
static void factors(int n,vector<int>&z) {
  z.clear();
  while(n>1) {
    int p=spf.at(n); z.push_back(p);
    do{n/=p;}while(n%p==0);
  }
}
static int gap(ll t,int p,int r) {
  ll z=(r-t)%(2LL*p); return int(z>0?z:z+2*p);
}
struct Group {ll hits=0,first=0,repeat=0;};
static void run(int X) {
  int B=int(ceill(sqrtl(7.L*X)));
  Group z[3]; vector<int>fac;
  for(int M=X+1;M<2*X;M+=2){
    ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
    vector<unsigned char> seen(B+1,0);
    while(t<K) {
      ll n=K+1;
      factors(int(C-1),fac);
      for(int p:fac)if(p<=B)n=min(n,t+gap(t,p,0));
      factors(int(C+1),fac);
      for(int p:fac)if(p<=B)n=min(n,t+gap(t,p,p+2));
      if(n>K)break;
      int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
      factors(raw,fac);
      int d=1;
      for(int p:fac)if(p<=B){
        d*=p;
        if(p>=11){
          int bin=(2*p>=B)?2:((4*p>=B)?1:0);
          z[bin].hits++;
          if(seen[p])z[bin].repeat++;
          else {z[bin].first++;seen[p]=1;}
        }
      }
      if(d<=1)throw runtime_error("missing clipped event");
      C+=d-1;t=n;
    }
  }
  if(X==4096 && (z[1].repeat!=39 || z[2].repeat!=11))throw runtime_error("X4096 regression");
  if(X==16384 && (z[1].repeat!=32 || z[2].repeat!=8))throw runtime_error("X16384 regression");
  if(X==65536 && (z[1].repeat!=168 || z[2].repeat!=0))throw runtime_error("X65536 regression");
  if(X==262144 && (z[1].repeat!=535 || z[2].repeat!=0))throw runtime_error("X262144 regression");
  cout<<"BAND_RETURN_PASS X="<<X<<" B="<<B;
  for(int i=0;i<3;i++)
    cout<<" band="<<i<<" hits="<<z[i].hits<<" first="<<z[i].first<<" repeats="<<z[i].repeat;
  cout<<"\n";
}
int main(int argc,char**argv){
  int mx=0;vector<int>xs;
  for(int i=1;i<argc;i++){
    int X=atoi(argv[i]);if(X<256||X%4||X>262144)return 2;
    xs.push_back(X);mx=max(mx,X);
  }
  if(xs.empty())return 2;
  sieve(8*mx+100);
  for(int X:xs)run(X);
}
