// Split event times into bounded low-prime blocks and one high-prime owner per high event.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror twin_prime_lowblock_highowner_audit.cpp -o /tmp/lowhigh
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
static vector<int>spf;
static void sieve(int N){spf.resize(N);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<N;p++)if(spf[p]==p)for(int z=p*p;z<N;z+=p)if(spf[z]==z)spf[z]=p;}
static void fac(int n,vector<int>&f){f.clear();while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}}
static int gap(ll t,int p,int r){int v=int((r-t)%(2LL*p));return v>0?v:v+2*p;}
struct Stat{ll lowTime=0,highTimeFirst=0,highTimeRet=0,highCountFirst=0,highCountRet=0,highWeightFirst=0,highWeightRet=0,blocks=0,maxLowBlock=0;
 ll cleanReturnTime=0,maskedReturnTime=0,cleanReturnCount=0,maskedReturnCount=0,maskedHiWeight=0,maskedHiHits=0,maskedHiCost=0,extra=0,ZhiReturn=0,Zhi5=0;
};
static void run(int X){int B=int(ceill(sqrtl(7.L*X)));constexpr array<int,4> cut={3,5,7,17};constexpr array<int,4> lbd={7,19,56,769};
 array<Stat,4>z{};array<vector<int>,4> seen, masked, active;
 for(int j=0;j<4;j++){seen[j].resize(B+1);masked[j].resize(B+1);}vector<int> f;ll travel=0;
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;array<ll,4> block{};
   for(int j=0;j<4;j++)active[j].clear();
   while(t<K){ll n=K+1;fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
     int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));fac(raw,f);int d=1,linear=0;vector<int>label;
     for(int p:f)if(p<=B){label.push_back(p);d*=p;linear+=p-1;}
     if(d<=1)throw runtime_error("event missing");
     const ll dt=n-t;travel+=dt;
     for(int j=0;j<4;j++){
       int owner=0;for(int p:label)if(p>cut[j]){owner=p;break;}
       if(!owner){block[j]+=dt;z[j].lowTime+=dt;z[j].maxLowBlock=max(z[j].maxLowBlock,block[j]);
         if(block[j]>lbd[j])throw runtime_error("low-only clock bound violated");
       }else{
         z[j].blocks++;block[j]=0;
         if(seen[j][owner]==0){z[j].highCountFirst++;z[j].highTimeFirst+=dt;z[j].highWeightFirst+=owner;}
         else{z[j].highCountRet++;z[j].highTimeRet+=dt;z[j].highWeightRet+=owner;
           if(masked[j][owner]==0){z[j].cleanReturnTime+=dt;z[j].cleanReturnCount++;}
           else{z[j].maskedReturnTime+=dt;z[j].maskedReturnCount++;}
         }
         for(int p:label)if(p>cut[j]){
           if(seen[j][p]==0)active[j].push_back(p);
           if(p>owner){z[j].maskedHiWeight+=p;z[j].maskedHiHits++;z[j].maskedHiCost+=2*p+lbd[j];if(seen[j][p]>0)masked[j][p]++;}
         }
         seen[j][owner]++;
         masked[j][owner]=0;
       }
       z[j].extra+=d-1-linear;
     }
     C+=d-1;t=n;
   }
   for(int j=0;j<4;j++){
     if(block[j]>lbd[j])throw runtime_error("tail low block bound violated");
     for(int p:active[j]){
       ll r=max(0,seen[j][p]-1);z[j].ZhiReturn+=r*r;
       if(p==5)z[j].Zhi5+=r*r;
       seen[j][p]=0;masked[j][p]=0;
     }
   }
 }
 for(int j=0;j<4;j++){
   const auto &a=z[j];
   if(a.lowTime+a.highTimeFirst+a.highTimeRet!=travel ||
      a.cleanReturnTime+a.maskedReturnTime!=a.highTimeRet ||
      a.maskedReturnTime>2*a.maskedHiWeight ||
      a.maskedReturnTime+ll(lbd[j])*a.maskedReturnCount>a.maskedHiCost ||
      (j==0 && 8*a.maskedHiCost>7*a.extra) ||
      travel>ll(lbd[j])*(X/2+a.highCountFirst+a.highCountRet)+2*a.highWeightFirst+a.highTimeRet)
     throw runtime_error("high-owner time ledger inconsistent");
   cout<<"LOW_HIGH_PASS X="<<X<<" B="<<B<<" cutoff="<<cut[j]<<" lowMax="<<lbd[j]
       <<" maxObservedBlock="<<a.maxLowBlock<<" travel="<<travel<<" lowTime="<<a.lowTime
       <<" highFirstCount="<<a.highCountFirst<<" highRepeatCount="<<a.highCountRet
       <<" highFirstWeight="<<a.highWeightFirst<<" highRepeatWeight="<<a.highWeightRet
       <<" highFirstTime="<<a.highTimeFirst<<" highRepeatTime="<<a.highTimeRet
       <<" highRepeatCertificate="<<(a.highTimeRet+ll(lbd[j])*a.highCountRet)
       <<" certificateOverX2="<<double(a.highTimeRet+ll(lbd[j])*a.highCountRet)/(double(X)*X)
       <<" cleanHighTime="<<a.cleanReturnTime<<" maskedHighTime="<<a.maskedReturnTime
       <<" maskedHighWeight="<<a.maskedHiWeight<<" maskedHighHits="<<a.maskedHiHits
       <<" maskCost="<<a.maskedHiCost<<" cleanHighCount="<<a.cleanReturnCount
       <<" maskedReturnCount="<<a.maskedReturnCount<<" compositeExtra="<<a.extra
       <<" ZhiReturn="<<a.ZhiReturn<<" Zhi5="<<a.Zhi5
       <<" momentOverXBLogB="<<double(a.ZhiReturn)/(double(X)*B*log(double(B)))
       <<" oneShadowBound="<<(a.cleanReturnTime+ll(lbd[j])*a.cleanReturnCount+a.maskedHiCost)
       <<" oneShadowBoundOverX2="<<double(a.cleanReturnTime+ll(lbd[j])*a.cleanReturnCount+a.maskedHiCost)/(double(X)*X)<<"\n";
 }
}
int main(int argc,char**argv){vector<int>xs;int mx=0;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X%4||X>262144)return 2;xs.push_back(X);mx=max(mx,X);}
 if(xs.empty())return 2;
 sieve(8*mx+1000);for(int X:xs)run(X);
}