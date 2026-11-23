// Exact MIN wheel first-reset source pushforward, fibre L2, and future high-event tails.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_reset_weighted_moments.cpp -o /tmp/min_reset_moments
// Run: /tmp/min_reset_moments 256 512 1024 4096 16384 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <vector>
using namespace std;using ll=long long;
static vector<int> spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
vector<int> factors(int n){vector<int>v;while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}return v;}
ll gap(ll t,int p,int r){ll a=(r-t)%(2LL*p);return a>0?a:a+2*p;}
// The FIRST nonunit parity GCD clock, followed by MIN prime selection.
int advance(ll &t,ll &C,ll K,int B){ll n=K+1;
 for(int p:factors((int)(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
 for(int p:factors((int)(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
 if(n>K)return 0;
 int raw=(int)gcd((n&1)?n-2:n,(n&1)?C+1:C-1),pick=0;
 for(int p:factors(raw))if(p<=B){pick=p;break;}
 if(!pick){abort();} t=n;C+=pick-1;return pick;
}
struct Atom{ll weight=0;int future=0;};
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;
 for(int a=1;a<argc;a++)maxX=max(maxX,atoi(argv[a]));
 sieve(8*maxX+500);
 for(int a=1;a<argc;a++){
 int X=atoi(argv[a]),B=(int)ceill(sqrtl(7.L*X));ll N=X/2,Kmax=(7LL*(2*X-1)-1)/4;
 unordered_map<ll,Atom> atoms;ll pre=0,post=0,entranceGain=0,S=0;
 vector<int> preHist(1024),futureHist(1024);
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
  bool reset=false;int sourcePre=0;
  while(true){int p=advance(t,C,K,B);if(!p)break;
   if(p>=11){if(reset)post++;else{pre++;sourcePre++;}}
   if(!reset&&p>=11&&2*t-C==((t&1)?6:0)){
    reset=true;atoms[2*t+(t&1)].weight++;S++;entranceGain+=C-(2LL*M-2);
   }
  }
  if(sourcePre>=1024){abort();} preHist[sourcePre]++;
 }
 ll w2=0,u2=0,wu=0,us=0;ll Kcount=atoms.size();ll maxW=0,maxU=0;
 for(auto &[key,v]:atoms){ll t=key/2,C=2*t-(key&1?6:0);int U=0;
  while(true){int p=advance(t,C,Kmax,B);if(!p)break;U+=(p>=11);}
  if(U>=1024){abort();} futureHist[U]++;v.future=U;
  w2+=v.weight*v.weight;u2+=(ll)U*U;wu+=v.weight*U;us+=U;
  maxW=max(maxW,v.weight);maxU=max(maxU,(ll)U);
 }
 if(wu<post||w2>S+entranceGain/2||entranceGain>(B+33LL)*pre)abort();
 long double aMean=(long double)us/Kcount,wMean=(long double)wu/S;
 long double pearson=0;
 long double mW=(long double)S/Kcount,mU=aMean;
 long double cov=(long double)wu/Kcount-mW*mU;
 long double vw=(long double)w2/Kcount-mW*mW,vu=(long double)u2/Kcount-mU*mU;
 if(vw>0&&vu>0)pearson=cov/sqrtl(vw*vu);
 ll pu=0,ph=0;long double maxRatioU=0,maxRatioH=0;
 for(int t=1023;t>=1;t--){pu+=futureHist[t];ph+=preHist[t];
  long double ef=expl((long double)t/logl(2.L*X));
  maxRatioU=max(maxRatioU,(long double)pu/Kcount*ef);
  maxRatioH=max(maxRatioH,(long double)ph/N*ef);
 }
 cout<<"MIN_RESET_MOMENT_PASS X="<<X<<" B="<<B<<" atoms="<<Kcount<<" covered="<<S
  <<" Hpre="<<pre<<" Hpost="<<post<<" envelope="<<wu
  <<" entranceGain="<<entranceGain<<" fibreL2="<<w2<<" atomU2="<<u2
  <<" maxW="<<maxW<<" maxU="<<maxU
  <<" Umean="<<(double)aMean<<" Uweighted="<<(double)wMean
  <<" pearson="<<(double)pearson
  <<" expTailRatioU="<<(double)maxRatioU<<" expTailRatioPre="<<(double)maxRatioH<<"\n";
 }
}
