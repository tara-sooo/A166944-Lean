// Actual first three MIN high selections after h=0/6 reset from all time-indexed atoms.
// Build g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_reset_first_three_high_crt_audit.cpp -o /tmp/first3
// Run /tmp/first3 256 1024 4096 16384 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <unordered_set>
#include <vector>
using namespace std;using ll=long long;
static vector<int> spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
vector<int>fac(int n){vector<int> v;while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}return v;}
ll gap(ll t,int p,int r){ll a=(r-t)%(2LL*p);return a>0?a:a+2*p;}
int advance(ll &t,ll &C,ll K,int B){ll n=K+1;
 for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
 for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
 if(n>K)return 0;
 int d=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),q=0;
 for(int p:fac(d))if(p<=B){q=p;break;}
 if(!q){abort();}t=n;C+=q-1;return q;
}
struct Triple{int a=0,b=0,c=0;int gain=0;ll time1=0,time3=0;};
Triple firstthree(ll n,ll K,int B){ll t=n,C=2*n-(n&1?6:0);Triple tr;int count=0,L=0;
 while(int p=advance(t,C,K,B)){
  if(p<11){if(count==1||count==2)L+=p-1;continue;}
  if(count==0){tr.a=p;tr.time1=t;}
  if(count==1)tr.b=p;
  if(count==2){tr.c=p;tr.time3=t;tr.gain=L;break;}
  count++;
 }
 if(tr.c&&tr.a==tr.c&&tr.a>=37){
  if(tr.a==tr.b||tr.gain>68)abort();
  int c=(tr.time1%2==0)?((tr.time3%2==0)?1:-1):((tr.time3%2==0)?3:1);
  if((tr.b-1+tr.gain-c)%tr.a)abort();
  if(tr.a>=max(37,(B+1)/2) && !(tr.b-tr.a>=-68&&tr.b-tr.a<=4) && !(tr.b-2*tr.a>=-68&&tr.b-2*tr.a<=4))abort();
 }
 return tr;
}
int main(int argc,char**argv){if(argc<2)return 2;int big=0;for(int i=1;i<argc;i++)big=max(big,atoi(argv[i]));sieve(8*big+500);
 for(int i=1;i<argc;i++){int X=atoi(argv[i]),B=int(ceill(sqrtl(7.L*X))),lo=max(37,(B+1)/2);ll Kmax=(7LL*(2*X-1)-1)/4;
  unordered_set<ll>A;for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   while(int p=advance(t,C,K,B))if(p>=11&&2*t-C==(t&1?6:0)){A.insert(t);break;}
  }
  ll all=0,reached=0,allOther=0,allLastDifferent=0,one=0,two=0,oneReached=0,twoReached=0,sumZ=0,sumZ2=0;int witness=0,wq=0,wr=0,wL=0;
  for(ll n=X+3;n<=Kmax;n++){
   Triple t=firstthree(n,Kmax,B);
   int z=0;ll cc=2*n-(n&1?6:0);
   for(int p:fac(int(cc-1)))if(p>=lo&&p<=B)z++;
   for(int p:fac(int(cc+1)))if(p>=lo&&p<=B)z++;
   sumZ+=z;sumZ2+=1LL*z*z;
   one+=(t.a>=lo);two+=(t.a>=lo&&t.b>=lo);
   if(A.count(n)){oneReached+=(t.a>=lo);twoReached+=(t.a>=lo&&t.b>=lo);}
   if(t.a>=lo&&t.c==t.a){all++;if(A.count(n))reached++;if(!witness){witness=n;wq=t.a;wr=t.b;wL=t.gain;}}
   if(t.a>=37&&t.c==t.a)allOther++;
   if(t.a>=lo&&t.c&&t.c!=t.a)allLastDifferent++;
  }
  cout<<"RESET_THREE_REHIT_PASS X="<<X<<" B="<<B<<" topFirstThirdSameAll="<<all
  <<" firstTopAll="<<one<<" firstTwoTopAll="<<two
  <<" firstTopReached="<<oneReached<<" firstTwoTopReached="<<twoReached<<" staticZ="<<sumZ<<" staticZ2="<<sumZ2
  <<" topFirstThirdSameReached="<<reached<<" any37FirstThirdSameAll="<<allOther
  <<" topFirstThirdDifferent="<<allLastDifferent<<" witnessTime="<<witness
  <<" witnessQ="<<wq<<" witnessR="<<wr<<" witnessLowGain="<<wL<<"\n";
 }
}
