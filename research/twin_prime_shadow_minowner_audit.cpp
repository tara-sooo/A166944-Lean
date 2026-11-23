// Exact marked q-deleted next-hit shadow and minimum-prime clean/masked return decomposition.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror twin_prime_shadow_minowner_audit.cpp -o /tmp/marked_shadow
// /tmp/marked_shadow 256 512 1024 4096 16384 65536
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll = long long;
static vector<int> spf;
static void sieve(int N){spf.resize(N);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<N;p++)if(spf[p]==p)for(int j=p*p;j<N;j+=p)if(spf[j]==j)spf[j]=p;}
static void fac(int x,vector<int>&f){f.clear();while(x>1){int p=spf.at(x);f.push_back(p);do{x/=p;}while(x%p==0);}}
static ll clock_gap(ll t,int p,int residue){ll z=(residue-t)%(2LL*p);return z>0?z:z+2*p;}
static int raw_gcd(ll n,ll c){return int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));}
static int clipped(int raw,int B,vector<int>&f){fac(raw,f);int d=1;for(int p:f)if(p<=B)d*=p;return d;}
struct ReturnHit{ll n=0,postC=0,preGap=0;int d=0;bool owner=false;ll skippedNonQ=0;};
// q-deleted shadow: advance with only p!=q, stop when q's clock is no later than other clock.
static ReturnHit shadow(ll t,ll C,ll K,int q,int B){vector<int>f;ll skipped=0;
  while(t<K){ll nq=K+1,no=K+1;
    fac(int(C-1),f);for(int p:f)if(p<=B){ll candidate=t+clock_gap(t,p,0);if(p==q)nq=min(nq,candidate);else no=min(no,candidate);}
    fac(int(C+1),f);for(int p:f)if(p<=B){ll candidate=t+clock_gap(t,p,p+2);if(p==q)nq=min(nq,candidate);else no=min(no,candidate);}
    if(nq<=no && nq<=K){int d=clipped(raw_gcd(nq,C),B,f);if(d%q)throw runtime_error("q clock not in clipped gcd");
       bool isOwner=true;for(int p:f)if(p<q && p<=B)isOwner=false;
       return {nq,C+d-1,nq-t,d,isOwner,skipped};}
    if(no>K)break;
    int d=clipped(raw_gcd(no,C),B,f);
    if(d<=1 || d%q==0)throw runtime_error("q-free shadow mismatch");
    C+=d-1;t=no;++skipped;
  }
  return {};
}
struct Totals{ll minRepeat=0,repeatTime=0,cleanTime=0,maskedTime=0;
  ll cleanReturnCount=0,maskedReturnCount=0,maskedHitCount=0,maskedWeight=0,extra=0,totalGrowth=0;
  ll shadowChecked=0,shadowNoReturn=0,shadowSteps=0,events=0,maskHighEvents=0;
  ll minFirstTime=0,firstP=0,firstOwner=0,ownerHigh=0;
  ll maskGapUpper=0,maskedReturnOwnerQsum=0;
  ll witnessM=0,witnessQ=0,witnessOwner=0,witnessMasked=0,witnessReturn=0;
};
static void run(int X){int B=int(ceill(sqrtl(7.L*X)));Totals z;
  vector<int>f,oldT(B+1,0),oldC(B+1,0),ownerCount(B+1,0),maskedSince(B+1,0),lastQOwner(B+1,0),hits(B+1,0),active;
  for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;active.clear();
    while(t<K){ll n=K+1;fac(int(C-1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,0));
      fac(int(C+1),f);for(int p:f)if(p<=B)n=min(n,t+clock_gap(t,p,p+2));
      if(n>K)break;
      int d=clipped(raw_gcd(n,C),B,f);if(d<=1)throw runtime_error("full event missing");
      int owner=0,linear=0;vector<int>labels;
      for(int p:f)if(p<=B){if(!owner)owner=p;linear+=p-1;labels.push_back(p);}
      if(owner==0)throw runtime_error("no owner");
      const ll g=n-t;z.events++;z.totalGrowth+=d-1;z.extra+=d-1-linear;
      if(ownerCount[owner]==0){z.firstP+=owner;z.firstOwner++;z.minFirstTime+=g;}
      else{z.minRepeat+=owner;z.repeatTime+=g;}
      for(int p:labels){
        if(hits[p]==0)active.push_back(p);
        else{
          ReturnHit s=shadow(oldT[p],oldC[p],K,p,B);z.shadowChecked++;z.shadowSteps+=s.skippedNonQ;
          if(s.n!=n || s.postC!=C+d-1 || s.d!=d || s.preGap!=g || s.owner!=(p==owner)){
            throw runtime_error("q shadow did not exactly reconstruct full next q event");}
        }
        if(p!=owner){z.maskedHitCount++;z.maskedWeight+=p;if(p>=19)z.maskHighEvents++;
          if(ownerCount[p]>0){maskedSince[p]++;}
        }else{
          if(ownerCount[p]>0){
            if(maskedSince[p]==0){
              if(!lastQOwner[p])throw runtime_error("clean return does not follow owned q hit");
              ++z.cleanReturnCount;z.cleanTime+=g;
            }else{
              ++z.maskedReturnCount;z.maskedTime+=g;z.maskedReturnOwnerQsum+=p;
              if(z.witnessM==0 && p>=19){z.witnessM=M;z.witnessQ=p;z.witnessOwner=oldT[p];z.witnessMasked=maskedSince[p];z.witnessReturn=n;}
            }
          }
          ownerCount[p]++;maskedSince[p]=0;if(p>=19)z.ownerHigh++;
        }
        hits[p]++;oldT[p]=int(n);oldC[p]=int(C+d-1);lastQOwner[p]=(p==owner);
      }
      C+=d-1;t=n;
    }
    for(int p:active){ReturnHit s=shadow(oldT[p],oldC[p],K,p,B);if(s.n)throw runtime_error("shadow predicted false terminal q hit");z.shadowNoReturn++;z.shadowSteps+=s.skippedNonQ;
      oldT[p]=oldC[p]=ownerCount[p]=maskedSince[p]=lastQOwner[p]=hits[p]=0;
    }
  }
  if(z.cleanTime+z.maskedTime!=z.repeatTime||z.maskedTime>2*z.maskedReturnOwnerQsum||
     z.maskedReturnOwnerQsum>z.maskedWeight||8*z.maskedWeight>5*z.extra||
     z.repeatTime>z.cleanTime+2*z.maskedWeight||
     z.repeatTime>z.cleanTime+5*z.extra/4+1||
     (X==4096&&(z.repeatTime!=83597||z.minRepeat!=92301))||
     (X==16384&&(z.repeatTime!=582420||z.minRepeat!=678809))||
     (X==65536&&(z.repeatTime!=2793148||z.minRepeat!=3257705))||
     (X==262144&&(z.repeatTime!=16242087||z.minRepeat!=19294492)))
     throw runtime_error("return and masked charge crosscheck failed");
  cout<<"MARKED_SHADOW_PASS X="<<X<<" B="<<B<<" fullEvents="<<z.events
    <<" W="<<z.totalGrowth<<" extra="<<z.extra<<" shadowMatched="<<z.shadowChecked
    <<" shadowNoReturn="<<z.shadowNoReturn<<" shadowSkipped="<<z.shadowSteps
    <<" firstOwner="<<z.firstOwner<<" minFirstTime="<<z.minFirstTime
    <<" minRepeat="<<z.minRepeat<<" returnTime="<<z.repeatTime
    <<" cleanReturnCount="<<z.cleanReturnCount<<" cleanReturnTime="<<z.cleanTime
    <<" maskedReturnCount="<<z.maskedReturnCount<<" maskedReturnTime="<<z.maskedTime
    <<" maskedQHits="<<z.maskedHitCount<<" maskedQWeight="<<z.maskedWeight
    <<" maskedChargeUpper="<<(2*z.maskedWeight)
    <<" extraUpper="<<(5*z.extra/4.0)
    <<" cleanAndMaskUpper="<<(z.cleanTime+2*z.maskedWeight)
    <<" witnessM="<<z.witnessM<<" witnessQ="<<z.witnessQ
    <<" witnessLastQ="<<z.witnessOwner<<" witnessMasked="<<z.witnessMasked
    <<" witnessReturn="<<z.witnessReturn<<"\n";
}
int main(int argc,char**argv){int mx=0;vector<int>xs;
  for(int i=1;i<argc;++i){int X=atoi(argv[i]);if(X<256||X%4||X>262144)return 2;xs.push_back(X);mx=max(mx,X);}
  if(xs.empty())return 2;
  sieve(8*mx+1000);
  for(int X:xs)run(X);
}