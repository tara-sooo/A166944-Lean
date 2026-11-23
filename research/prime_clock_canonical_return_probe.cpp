// Canonical squarefree B-wheel owner-return and growth/travel extrema.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_canonical_return_probe.cpp -o /tmp/probe
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;using ll=long long;
static vector<int> spf;
static void sieve(int N){spf.resize(N);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<N;p++)if(spf[p]==p)for(int z=p*p;z<N;z+=p)if(spf[z]==z)spf[z]=p;}
static void fac(int n,vector<int>&f){f.clear();while(n>1){int p=spf[n];f.push_back(p);do{n/=p;}while(n%p==0);}}
static int gap(ll t,int p,int r){int v=int((r-t)%(2LL*p));return v>0?v:v+2*p;}
static void run(int X){int B=ceil(sqrtl(7.L*X)),N=X/2;vector<int>f,seen(B+1);int maxRet=-1,maxM=0,maxAllEv=0,maxGrowth=0;ll sumRet=0,sumG=0,sumTravel=0,sumHighRetTime=0;
 ll bigPair=0,largeDClock=0,largeDCount=0;int largeCut=int(pow(double(B),1.2));
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;int ret=0,ev=0;vector<int>touched;
   while(t<K){ll n=K+1;fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1,owner=0,highCnt=0;
    fac(raw,f);for(int p:f)if(p<=B){d*=p;if(p>=11){highCnt++;if(!owner)owner=p;}}
    if(d<=1){cerr<<"missing event";exit(2);}int dt=int(n-t);if(owner){if(seen[owner]++) {ret++;sumHighRetTime+=dt;}else touched.push_back(owner);}
    if(highCnt>=2)bigPair++;
    if(d>=largeCut){largeDCount++;largeDClock+=dt;}
    C+=d-1;t=n;ev++;
   }
   for(int p:touched)seen[p]=0;
   int g=int(C-(2LL*M-2)),v=int(t-(M+2));sumRet+=ret;sumG+=g;sumTravel+=v;
   maxGrowth=max(maxGrowth,g);maxAllEv=max(maxAllEv,ev);
   if(ret>maxRet){maxRet=ret;maxM=M;}
 }
 cout<<"CANON_RETURN_PROBE X="<<X<<" B="<<B<<" starts="<<N<<" R7="<<sumRet<<" R7/XB="<<double(sumRet)/(double(X)*B)<<" maxPerSource="<<maxRet<<" maxOverB="<<double(maxRet)/B<<" witnessM="<<maxM<<" noTwinNecessary="<<3.0/56.0<<" maxEvents="<<maxAllEv<<" maxGrowth="<<maxGrowth<<" meanG="<<double(sumG)/N<<" meanTravel="<<double(sumTravel)/N<<" returnTime="<<sumHighRetTime<<" highHighEvents="<<bigPair<<" largeCut="<<largeCut<<" largeEvents="<<largeDCount<<" largeClock="<<largeDClock<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;for(int i=1;i<argc;i++)mx=max(mx,atoi(argv[i]));sieve(8*mx+300);for(int i=1;i<argc;i++)run(atoi(argv[i]));}
