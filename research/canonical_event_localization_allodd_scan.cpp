// Original A166944 parity-gcd, exact factorized first-hit scanner.
// c++ -O3 -std=c++17 research/canonical_event_localization_allodd_scan.cpp -o /tmp/a166944_scan
// /tmp/a166944_scan 10000000
// Finite exhaustive computation, NOT a proof of universal localization.
#include <bits/stdc++.h>
using namespace std;using ll=long long;
vector<int>spf;
vector<int> fact(ll v){vector<int>out;while(v>1){int p=spf[v];if(!p)p=(int)v;out.push_back(p);while(v%p==0)v/=p;}return out;}
ll gap(ll pos,ll p,ll target){ll t=(target-pos)%(2*p);if(t<=0)t+=2*p;return t;}
int main(int argc,char**argv){int maxM=argc>1?atoi(argv[1]):5000000;int mx=(7LL*maxM+3)/2+3;spf.resize(mx+1,0);for(int p=2;1LL*p*p<=mx;p++)if(!spf[p])for(ll j=1LL*p*p;j<=mx;j+=p)if(!spf[j])spf[j]=p;
long long checked=0,late=0,bad=0,lateTw=0,badTw=0,twin=0;vector<int> badMs,lateMs;int maxLate=0,maxBad=0,maxRatioM=0,maxOffsetM=0;double maxRatio=0,maxRatioBeyond1000=0;int maxBeyondM=0;ll maxOffset=0;array<long long,6> countLate{};
for(int M=7;M<=maxM;M+=2){checked++;ll s=(ll)M+2,K=(7LL*M-1)/4,pos=s,C=2LL*M-2,last=s;int N=0;
while(pos<K){ll nex=K+1;for(int p:fact(C-1))nex=min(nex,pos+gap(pos,p,0));for(int p:fact(C+1))nex=min(nex,pos+gap(pos,p,p+2));if(nex>K)break;ll e=gcd((nex&1)?nex-2:nex,(nex&1)?C+1:C-1);if(e<=1){cerr<<"fail first hit";return 4;}C+=e-1;last=nex;pos=nex;N++;}
bool good=(C-1>1&&spf[C-1]==0)&&(C+1>1&&spf[C+1]==0),tw=(spf[M]==0&&spf[M-2]==0);
if(tw){twin++;badTw+=!good;}
if(!good){bad++;maxBad=M;badMs.push_back(M);}
int offs=(int)(last-s);
if(2LL*offs>M){late++;maxLate=M;countLate[M%6]++;lateTw+=tw;lateMs.push_back(M);}
double rat=double(offs)/M;
if(rat>maxRatio){maxRatio=rat;maxRatioM=M;}
if(M>=1000&&rat>maxRatioBeyond1000){maxRatioBeyond1000=rat;maxBeyondM=M;}
if(offs>maxOffset){maxOffset=offs;maxOffsetM=M;}
}
cout<<"M<= "<<maxM<<" all odd="<<checked<<" twin="<<twin<<" BAD="<<bad<<" BAD twin="<<badTw<<" late>M/2="<<late<<" late twin="<<lateTw<<" maxBAD_M="<<maxBad<<" lastLate_M="<<maxLate<<" class late "<<countLate[1]<<","<<countLate[3]<<","<<countLate[5]<<"\n";
cout<<setprecision(10)<<" maxLastRatio="<<maxRatio<<" M="<<maxRatioM<<" maxLastRatioM>=1000="<<maxRatioBeyond1000<<" M="<<maxBeyondM<<" maxLastOffset="<<maxOffset<<" M="<<maxOffsetM<<"\n";
cout<<"BAD odd starts:";for(int m:badMs)cout<<" "<<m;cout<<"\n";
cout<<"late odd starts:";for(int m:lateMs)cout<<" "<<m;cout<<"\n";
if(maxM==10000000){
  if(checked!=4999997||twin!=58979||bad!=9||badTw!=2||
     late!=21||lateTw!=0||maxBad!=305||maxLate!=375||
     maxBeyondM!=1331||maxOffset!=44892||maxOffsetM!=7209299||
     badMs!=vector<int>({11,13,23,25,39,41,43,45,305})){
       cerr<<"finite 10M regression mismatch\n";return 3;
  }
}
cout<<"PASS exact finite scan; universal event localization OPEN\n";
}
