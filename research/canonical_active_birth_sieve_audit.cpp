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
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int i=p*p;i<n;i+=p)if(spf[i]==i)spf[i]=p;}
vector<int> fac(int n){vector<int> o;while(n>1){int p=spf.at(n);o.push_back(p);do{n/=p;}while(n%p==0);}return o;}
int gap(ll t,int p,int r){ll k=(r-t)%(2LL*p);return (int)(k>0?k:k+2*p);}
struct Counts {ll fires=0,first=0,returns=0,births=0,postFirstBirths=0,renewalBirths=0,deadBeforeFiring=0,actives=0,visits=0;int peakActive=0;};
void scan(int X){int B=ceil(sqrt(7.0*X));Counts hi,half,all;
 int maxTopActive=0, maxHalfActive=0; ll maxC=0; ll hugeEvents=0,hugeTime=0,allTime=0;int hugeThreshold=int(ceil(pow(double(B),1.25)));
 for(int M=X+1;M<2*X;M+=2){ll C=2LL*M-2,t=M+2,K=(7LL*M-1)/4;vector<char> fired(B+1),wasActive(B+1);
  auto active=[&](ll c){vector<int> f=fac(int(c-1)),g=fac(int(c+1));f.insert(f.end(),g.begin(),g.end());vector<int> o;for(int p:f)if(p>=11&&p<=B)o.push_back(p);return o;};
  auto firstactive=active(C);for(int p:firstactive)wasActive[p]=1;
  while(t<K){ll n=K+1;
   for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
   for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
   if(n>K)break;
   maxC=max(maxC,C);
   auto old=active(C);int countTop=0,countHalf=0;for(int p:old){countTop+=(2*p>=B);countHalf+=(4*p>=B);}maxTopActive=max(maxTopActive,countTop);maxHalfActive=max(maxHalfActive,countHalf);
   if(B>32 && countTop>4)throw runtime_error("top live bound");
   int raw=(int)gcd((n&1)?n-2:n,(n&1)?C+1:C-1),d=1;
   for(int p:fac(raw))if(p<=B){d*=p;if(p>=11){auto &z=2*p>=B?hi:4*p>=B?half:all;z.fires++;if(fired[p])z.returns++;else z.first++;fired[p]=1;}}
   if(d<=1)throw runtime_error("empty event");
   allTime+=n-t;if(d>=hugeThreshold){hugeEvents++;hugeTime+=n-t;}
   C+=d-1;t=n;auto now=active(C);vector<char> before(B+1);
   for(int p:old)before[p]=1;
   for(int p:now){if(!before[p]){auto &z=2*p>=B?hi:4*p>=B?half:all;z.births++;if(fired[p])z.renewalBirths++;}}
   for(int p:fac(d))if(p>=11&&p<=B)if((C-1)%p==0||(C+1)%p==0)throw runtime_error("fired still active");
  }
 }
 cout<<"ACTIVITY_PASS X="<<X<<" B="<<B<<" peakTop="<<maxTopActive<<" peakMidPlus="<<maxHalfActive<<" maxC="<<maxC<<" hugeThreshold="<<hugeThreshold<<" hugeEvents="<<hugeEvents<<" hugeTime="<<hugeTime<<" allTime="<<allTime<<" ";
 auto put=[&](const char *name,Counts z){cout<<name<<"[firings="<<z.fires<<",first="<<z.first<<",returns="<<z.returns<<",births="<<z.births<<",renewalBirths="<<z.renewalBirths<<"] ";if(z.returns>z.renewalBirths)throw runtime_error("renewal birth charge violated");};
 put("top",hi);put("middle",half);put("low",all);cout<<"\n";
}
int main(int argc,char **argv){if(argc<2)return 2;int Xmax=0;for(int i=1;i<argc;i++)Xmax=max(Xmax,atoi(argv[i]));sieve(8*Xmax+200);for(int i=1;i<argc;i++)scan(atoi(argv[i]));}
