// Compiled finite audit of deterministic high-event low-clock budget.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror charged_clock_budget_audit.cpp -o audit
// ./audit 4096 16384 65536 262144 1048576
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <climits>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
static void sieve(int bound){spf.resize(bound);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<bound;++p)if(spf[p]==p)for(int k=p*p;k<bound;k+=p)if(spf[k]==k)spf[k]=p;}
static void factors(int n,vector<int>&v){v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}}
static ll next_gap(ll t,int p,ll r){ll d=(r-t)%(2LL*p);if(d<=0)d+=2*p;return d;}
static ll literal_growth(int M,int B){ll c=2LL*M-2,start=c,K=(7LL*M-1)/4;vector<int>ps;for(ll n=M+3;n<=K;++n){int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(raw,ps);int d=1;for(int p:ps)if(p<=B)d*=p;c+=d-1;}return c-start;}
static ll jumping_growth(int M,int B){ll c=2LL*M-2,start=c,t=M+2,K=(7LL*M-1)/4;vector<int>ps;while(t<K){ll dt=K-t+1;factors(int(c-1),ps);for(int p:ps)if(p<=B)dt=min(dt,next_gap(t,p,0));factors(int(c+1),ps);for(int p:ps)if(p<=B)dt=min(dt,next_gap(t,p,p+2));if(t+dt>K)break;ll n=t+dt;int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factors(raw,ps);int d=1;for(int p:ps)if(p<=B)d*=p;c+=d-1;t=n;}return c-start;}
struct Counts{ll big=0,small=0,sink=0,high=0,low=0,lowTime=0,charged=0,maxLowTime=0,maxLowEvents=0,terminalZ=0,highTime=0;};
static void run(int X){const int B=int(ceill(sqrtl(7.L*X)));int Q=219;if(Q>B)Q=B+1;
  vector<int>ps;Counts total;ll maxRatioNumer=0,maxZ=0,maxHigh=0;ll trajectoriesWithBig=0,fullSinkStarts=0,noSinkStarts=0,minNoSinkHigh=LLONG_MAX,maxHighNoSink=0;
  for(int M=X+1;M<2*X;M+=2){ll t=M+2,c=2LL*M-2,K=(7LL*M-1)/4,zStart=6;ll lowTime=0,lowGrowth=0;ll lowCount=0;ll big=0,small=0,sink=0,high=0,low=0;
    while(t<K){ll next=K+1;factors(int(c-1),ps);for(int p:ps)if(p<=B)next=min(next,t+next_gap(t,p,0));factors(int(c+1),ps);for(int p:ps)if(p<=B)next=min(next,t+next_gap(t,p,p+2));if(next>K)break;
      int raw=int(gcd((next&1)?next-2:next,(next&1)?c+1:c-1));factors(raw,ps);int d=1;bool isHi=false;for(int p:ps)if(p<=B){d*=p;if(p>=13)isHi=true;}
      if(d<=1)throw runtime_error("clock mismatch");
      const bool lowActive= c%3==1||c%3==2||c%5==1||c%5==4||c%7==1||c%7==6||c%11==1||c%11==10;
      const ll dt=next-t;
      const ll beforeZ=2*t-c,afterZ=2*next-c-d+1;
      if(beforeZ<0||afterZ<0)throw runtime_error("negative z");
      if(isHi){
        ++high;total.high++;
        if(lowCount>22||lowTime>133)throw runtime_error("finite low-only envelope failed");
        if(2*lowTime-lowGrowth>(lowActive?172:192))throw runtime_error("exact low-prefix deficit gain exceeded");
        total.maxLowTime=max(total.maxLowTime,lowTime);total.maxLowEvents=max(total.maxLowEvents,lowCount);
        if(lowActive){
          if(dt>22)throw runtime_error("active low prime clock took >22 steps");
          if(afterZ-zStart>217-d)throw runtime_error("low-clock high-event budget failed");
          if(d>=Q){++big;total.big++;}
          else {++small;total.small++;}
        }else{
          if(dt>2*B)throw runtime_error("sink clock took >2B steps");
          if(afterZ-zStart>4*B+193)throw runtime_error("low-sink recharge bound failed");
          ++sink;total.sink++;
        }
        zStart=afterZ;lowTime=0;lowGrowth=0;lowCount=0;
        total.charged+=(afterZ!=0 && afterZ!=6);
      }else{
        if(dt>22)throw runtime_error("active low clock took >22 steps");
        lowTime+=dt;lowGrowth+=d-1;++lowCount;++low;total.low++;
        if(lowCount>22||lowTime>133)throw runtime_error("low-only block exceeds exact 133-time universal limit");
      }
      c+=d-1;t=next;maxZ=max(maxZ,afterZ);
    }
    if(Q>217){ll lhs=(Q-217)*big,rhs=6+217*small+(4LL*B+193)*sink;
      if(lhs>rhs)throw runtime_error("global potential budget violated");
      maxRatioNumer=max(maxRatioNumer,lhs);}
    bool anyFullActive=false;
    factors(int(c-1),ps);for(int p:ps)if(p<=B)anyFullActive=true;
    factors(int(c+1),ps);for(int p:ps)if(p<=B)anyFullActive=true;
    if(!anyFullActive){
      fullSinkStarts++;
      if(spf.at(int(c-1))!=c-1||spf.at(int(c+1))!=c+1)
        throw runtime_error("full sink must be a twin-prime center");
    }else{
      noSinkStarts++;
      minNoSinkHigh=min(minNoSinkHigh,high);maxHighNoSink=max(maxHighNoSink,high);
      ll horizon=K-(M+2),charge=(high+1)*(2LL*B+133);
      if(horizon>charge)throw runtime_error("no-sink high-depth time bound violated");
    }
    if(big)trajectoriesWithBig++;
    maxHigh=max(maxHigh,high);total.terminalZ+=2*t-c;
  }
  if(X==4096&&total.high!=7675)throw runtime_error("high-event regression X4096");
  if(X==16384&&total.high!=45343)throw runtime_error("high-event regression X16384");
  if(X==65536&&total.high!=224221)throw runtime_error("high-event regression X65536");
  if(X==262144&&total.high!=1198498)throw runtime_error("high-event regression X262144");
  if(X==1048576&&total.high!=5516751)throw runtime_error("high-event regression X1048576");
  if(maxRatioNumer<0||maxZ<0)throw runtime_error("impossible aggregation");
  if(total.high!=total.big+total.small+total.sink)throw runtime_error("category sum mismatch");
  cout<<"BUDGET_PASS X="<<X<<" B="<<B<<" Q="<<Q<<" high="<<total.high<<" big_interrupted="<<total.big<<" small_interrupted="<<total.small<<" low_sink="<<total.sink<<" maxLowTime="<<total.maxLowTime<<" maxLowEvents="<<total.maxLowEvents<<" maxHigh="<<maxHigh<<" withBig="<<trajectoriesWithBig<<" twinSinkStarts="<<fullSinkStarts<<" noSinkStarts="<<noSinkStarts<<" minNoSinkHigh="<<(noSinkStarts?minNoSinkHigh:0)<<" maxNoSinkHigh="<<maxHighNoSink<<" normalizedHighMean="<<double(total.high)/(X*double(B))<<"\n";
}
int main(int argc,char **argv){if(argc<2)return 2;int maxX=0;vector<int>xs;for(int i=1;i<argc;++i){int X=atoi(argv[i]);if(X<256||X%2||X>2000000)return 2;xs.push_back(X);maxX=max(maxX,X);}sieve(8*maxX+1000);
  for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=jumping_growth(M,41))throw runtime_error("independent literal-step check");
  for(int X:xs)run(X);
}
