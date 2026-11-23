// Original parity-specific full B clipped GCD: q>=19 count after S<=17 nilpotent certificate.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
static vector<int>spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
void fac(int n,vector<int>&a){a.clear();while(n>1){int p=spf.at(n);a.push_back(p);do{n/=p;}while(n%p==0);}}
int gap(ll t,int q,int r){int z=int((r-t)%(2LL*q));if(z<=0)z+=2*q;return z;}
ll literal(int M,int B){ll c=2LL*M-2,c0=c,K=(7LL*M-1)/4;vector<int>v;for(ll n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(g,v);int d=1;for(int q:v)if(q<=B)d*=q;c+=d-1;}return c-c0;}
ll jumping(int M,int B){ll c=2LL*M-2,c0=c,t=M+2,K=(7LL*M-1)/4;vector<int>v;while(t<K){ll n=K+1;fac(int(c-1),v);for(int q:v)if(q<=B)n=min(n,t+gap(t,q,0));fac(int(c+1),v);for(int q:v)if(q<=B)n=min(n,t+gap(t,q,q+2));if(n>K)break;int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(g,v);int d=1;for(int q:v)if(q<=B)d*=q;c+=d-1;t=n;}return c-c0;}
void run(int X){int B=int(ceill(sqrtl(7.L*X)));ll high13=0,high17=0,high19=0,low17only=0,W=0,maxT19=0,terminal=0;vector<int>f;
 for(int M=X+1;M<2*X;M+=2){ll c=2LL*M-2,t=M+2,K=(7LL*M-1)/4,T19=0;
  while(t<K){ll n=K+1;fac(int(c-1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,0));fac(int(c+1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,q+2));if(n>K)break;
   int gd=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1)),d=1;fac(gd,f);
   bool hi13=false,hi17=false,hi19=false;
   for(int q:f)if(q<=B){d*=q;if(q>=13)hi13=true;if(q>=17)hi17=true;if(q>=19)hi19=true;}
   if(d<3)throw runtime_error("clock mismatch");
   high13+=hi13;high17+=hi17;high19+=hi19;
   if(hi17&&!hi19)low17only++;
   T19+=hi19;c+=d-1;t=n;
  }
  maxT19=max(maxT19,T19);W+=c-(2LL*M-2);
  bool hasFactor=false;
  fac(int(c-1),f);for(int q:f)if(q<=B)hasFactor=true;
  fac(int(c+1),f);for(int q:f)if(q<=B)hasFactor=true;
  if(!hasFactor)terminal++;
 }
 if((X==4096&&high13!=7675)||(X==16384&&high13!=45343)||(X==65536&&high13!=224221)||(X==262144&&high13!=1198498)||(X==1048576&&high13!=5516751))throw runtime_error("q13 regression");
 if((X==4096&&high17!=6131)||(X==16384&&high17!=37272)||(X==65536&&high17!=187142)||(X==262144&&high17!=1001099)||(X==1048576&&high17!=4612625))throw runtime_error("q17 regression");
 cout<<"HI19_ORIGINAL_PASS X="<<X<<" B="<<B<<" high13="<<high13<<" high17="<<high17<<" high19="<<high19<<" q17_only="<<low17only<<" normalized19="<<double(high19)/(X*double(B))<<" maxPerSource19="<<maxT19<<" growth="<<W<<" fullSinks="<<terminal<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;vector<int>xs;for(int k=1;k<argc;k++){int X=atoi(argv[k]);if(X<256||X>2000000||X%4)return 2;maxX=max(maxX,X);xs.push_back(X);}sieve(8*maxX+1000);for(int M=7;M<=119;M+=2)if(literal(M,41)!=jumping(M,41))throw runtime_error("small direct mismatch");for(int X:xs)run(X);}
