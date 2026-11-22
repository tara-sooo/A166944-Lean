// A166944 research: high-prime restart epochs and affine first high event cells.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror restart_epoch_audit.cpp -o restart_epoch_audit
// ./restart_epoch_audit 4096 16384 65536 262144 1048576
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
static vector<int> spf;
static constexpr int smallP=1155;
static void distinct_factors(int x,vector<int>&v){v.clear();while(x>1){int q=spf.at(x);v.push_back(q);do{x/=q;}while(x%q==0);}}
static ll clk(ll t,int p,int r){ll a=(r-t)%(2LL*p);if(a<=0)a+=2LL*p;return t+a;}
static ll literal_growth(int M,int B){ll C=2LL*M-2,init=C,K=(7LL*M-1)/4;vector<int>f;
 for(ll n=M+3;n<=K;n++){
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
  distinct_factors(raw,f);int d=1;for(int q:f)if(q<=B)d*=q;
  C+=d-1;
 }
 return C-init;
}
static ll event_growth(int M,int B){ll C=2LL*M-2,init=C,t=M+2,K=(7LL*M-1)/4;vector<int>f;
 while(t<K){ll n=K+1;
  distinct_factors(int(C-1),f);for(int q:f)if(q<=B)n=min(n,clk(t,q,0));
  distinct_factors(int(C+1),f);for(int q:f)if(q<=B)n=min(n,clk(t,q,q+2));
  if(n>K)break;
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));distinct_factors(raw,f);
  int d=1;for(int q:f)if(q<=B)d*=q;
  if(d<=1)throw runtime_error("small event mismatch");
  C+=d-1;t=n;
 }
 return C-init;
}
static void setup(int X){int Z=8*X+1000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;}
struct Rec{int offset,clockOffset;};
static void run(int X){int B=int(ceill(sqrtl(7.L*X)));ll N=X/2,ev=0,large=0,nonfirst=0,multiHigh=0,sumHighFirst=0;
 ll firstMaxD=0,firstMaxM=0,maxLowBetween=0,maxQConsecutive=0,repeatCount=0,firstComposite=0,firstHighMulti=0,firstCompositeMax=0,hiMassAll=0,hiMass1=0,hiMass2=0;
 int maxHigh=0,maxHighM=0,maxSmall=0;ll totalGrowth=0,firstCount=0,firstNo=0;
 vector<ll> atleast(2001,0),exact(2001,0);
 vector<int> factors,factors2;
 unordered_map<ll,Rec> affine,afterFirstLowAffine;ll affineChecks=0,lowAffineChecks=0;
 for(int M=X+1;M<2*X;M+=2){
   ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   int waves=0,lowCount=0;int prevHighFactor=0;int prefixIndex=0;ll firstSig=-1;
   ll lowBetween=0;
   while(t<K){
     ll n=K+1;
     distinct_factors(int(C-1),factors);for(int q:factors)if(q<=B)n=min(n,clk(t,q,0));
     distinct_factors(int(C+1),factors);for(int q:factors)if(q<=B)n=min(n,clk(t,q,q+2));
     if(n>K)break;
     int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));distinct_factors(raw,factors);
     int d=1,H=1,highCount=0;int hiWeight=0;int side=int(n&1);
     for(int q:factors)if(q<=B){d*=q;if(q>11){H*=q;++highCount;hiWeight+=q;}}
     if(d<=1)throw runtime_error("wrong clock event");
     ev++;
     if(H>1){
        hiMassAll+=hiWeight;if(waves==0)hiMass1+=hiWeight;else if(waves==1)hiMass2+=hiWeight;
        if(waves==0){
          firstCount++;sumHighFirst+=d;if(2*t-C>146)throw runtime_error("first-high canonical z>146");if(highCount!=1)throw runtime_error("first high event has multiple primes >=13"); if(H>=59 && d!=H)throw runtime_error("first high prime >=59 shares small prime"); if(d>max(B,191))throw runtime_error("first high event too large");if(d!=H){firstComposite++;firstCompositeMax=max(firstCompositeMax,1LL*d);}if(highCount>=2)firstHighMulti++;
          if(d>firstMaxD){firstMaxD=d;firstMaxM=M;}
          if(d>4LL*B+975)throw runtime_error("first large d exceeded uniform delay bound");
          int r=M%(2*smallP);
          ll key= (((ll(r)*24+prefixIndex)*2+side) * (8LL*B+2000))+H;
          firstSig=key;
          Rec actual{int(C+d-1-(2LL*M-2)),int(n-M)};
          auto it=affine.find(key);
          if(it!=affine.end()){
             affineChecks++;
             if(it->second.offset!=actual.offset||it->second.clockOffset!=actual.clockOffset)
               throw runtime_error("first-high affine restart signature collision");
          }else affine.emplace(key,actual);
        }else{
          nonfirst++;maxLowBetween=max(maxLowBetween,lowBetween);
          if(lowBetween>1156)throw runtime_error("low-only prefix growth > exact computed 1156");
          distinct_factors(H,factors2);
          for(int q:factors2)if(prevHighFactor%q==0){
              if((lowBetween-3)%q!=0 && (lowBetween-1)%q!=0 && (lowBetween+1)%q!=0)
                throw runtime_error("consecutive high prime q missing low-growth congruence");
              repeatCount++;maxQConsecutive=max(maxQConsecutive,1LL*q);
              if(q>1157)throw runtime_error("forbidden q repeat in successive high events");
          }
        }
        ++waves;large++;
        if(highCount>=2)multiHigh++;
        prevHighFactor=H;lowBetween=0;lowCount=0;
     }else{
        ++lowCount;lowBetween+=d-1;
        if(waves==1){
           ll key=firstSig*24+lowCount;
           Rec now{int(C+d-1-(2LL*M-2)),int(n-M)};
           auto it=afterFirstLowAffine.find(key);
           if(it!=afterFirstLowAffine.end()){
             lowAffineChecks++;
             if(it->second.offset!=now.offset||it->second.clockOffset!=now.clockOffset)
               throw runtime_error("post-first low plateau not affine in CRT cell");
           }else afterFirstLowAffine.emplace(key,now);
        }
        maxSmall=max(maxSmall,lowCount);
        if(waves==0)prefixIndex++;
     }
     C+=d-1;t=n;
   }
   if(lowBetween>1156)throw runtime_error("tail low-growth >1156");
   totalGrowth+=C-(2LL*M-2); if(waves==0)firstNo++;
   if(waves>maxHigh){maxHigh=waves;maxHighM=M;}
   if(waves>2000)throw runtime_error("hist overrun");
   exact[waves]++;
 }
 for(int k=1;k<=2000;k++)for(int j=k;j<=2000;j++)atleast[k]+=exact[j];
 if(X==4096&&(ev!=29349||large!=7675||totalGrowth!=399142))throw runtime_error("X4096 mismatch");
 if(X==16384&&(ev!=171428||large!=45343||totalGrowth!=2915326))throw runtime_error("X16384 mismatch");
 if(X==65536&&(ev!=795689||large!=224221||totalGrowth!=19826998))throw runtime_error("X65536 mismatch");
 cout<<"X="<<X<<" B="<<B<<" N="<<N<<" events="<<ev<<" high="<<large<<" highMean="<<fixed<<setprecision(7)<<double(large)/N
     <<" maxHigh="<<maxHigh<<" atM="<<maxHighM<<" highFirst="<<firstCount<<" noHigh="<<firstNo
     <<" firstMaxD="<<firstMaxD<<" atM="<<firstMaxM<<" firstMaxDivB="<<double(firstMaxD)/B
     <<" hiMassAll="<<hiMassAll<<" hiMass1="<<hiMass1<<" hiMass2="<<hiMass2<<" ratioMass1_XB="<<double(hiMass1)/(X*double(B))<<" ratioMass2_XB="<<double(hiMass2)/(X*double(B))<<" firstComposite="<<firstComposite<<" firstHighMulti="<<firstHighMulti<<" firstCompositeMax="<<firstCompositeMax<<" multiHighEvents="<<multiHigh<<" nonfirst="<<nonfirst
     <<" maxLowGapGrowth="<<maxLowBetween<<" consecutivePrimeRepeats="<<repeatCount<<" maxRepeatQ="<<maxQConsecutive
     <<" affineCells="<<affine.size()<<" affineCollisionChecks="<<affineChecks<<" lowAffineCells="<<afterFirstLowAffine.size()<<" lowAffineChecks="<<lowAffineChecks<<" maxLowRun="<<maxSmall<<"\n";
 cout<<"HIGH_DEPTH";
 for(int k:{1,2,3,5,10,20,30,40,50,75,100,150,200,300,500})if(k<=2000)cout<<" ge"<<k<<"="<<atleast[k];
 cout<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;vector<int> xs;
 for(int i=1;i<argc;i++){int x=atoi(argv[i]);if(x<256||x%2||x>10000000)return 2;xs.push_back(x);mx=max(mx,x);} setup(mx);
 for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=event_growth(M,41))
  throw runtime_error("literal-step reference mismatch");
 for(int x:xs)run(x);
}
