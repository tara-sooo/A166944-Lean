// Second moment in (source,prime) of number of actual q>=19 clipped-GCD hits.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/q_label_autocorrelation_audit.cpp -o /tmp/q_label_moment
// /tmp/q_label_moment 4096 16384 65536 262144 1048576 1999996
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int z=p*p;z<n;z+=p)if(spf[z]==z)spf[z]=p;}
static void factor(int n, vector<int>&a){a.clear();while(n>1){int p=spf.at(n);a.push_back(p);do{n/=p;}while(n%p==0);}}
static int gap(ll t,int p,int r){int x=int((r-t)%(2LL*p));return x>0?x:x+2*p;}
static ll literal_growth(int M,int B){ll c=2LL*M-2,c0=c,K=(7LL*M-1)/4;vector<int>f;for(ll n=M+3;n<=K;n++){int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factor(g,f);int d=1;for(int q:f)if(q<=B)d*=q;c+=d-1;}return c-c0;}
static ll jump_growth(int M,int B){ll c=2LL*M-2,c0=c,t=M+2,K=(7LL*M-1)/4;vector<int>f;while(t<K){ll n=K+1;factor(int(c-1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,0));factor(int(c+1),f);for(int q:f)if(q<=B)n=min(n,t+gap(t,q,q+2));if(n>K)break;int g=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));factor(g,f);int d=1;for(int q:f)if(q<=B)d*=q;c+=d-1;t=n;}return c-c0;}
static void run(int X){const int B=int(ceill(sqrtl(7.L*X)));ll H=0,F=0,Z=0,T19=0;int maxN=0,maxAtQ=0,maxAtM=0,piCount=0;
    for(int q=19;q<=B;q++)if(spf[q]==q)piCount++;
    vector<int> f,nHits(B+1,0),active;
    vector<ll> hist(65,0);
    vector<array<int,65>> perPrimeHistogram(B+1);
    array<ll,5> bandH{},bandF{},bandZ{};
    for(int M=X+1;M<2*X;M+=2){ll c=2LL*M-2,t=M+2,K=(7LL*M-1)/4;active.clear();
      while(t<K){ll n=K+1;factor(int(c-1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,0));factor(int(c+1),f);for(int p:f)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
        int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1)),d=1;bool high=false;factor(raw,f);
        for(int p:f)if(p<=B){d*=p;if(p>=19){if(nHits[p]++==0)active.push_back(p);high=true;}}
        if(d<3)throw runtime_error("bad event");
        T19+=high;c+=d-1;t=n;
      }
      for(int q:active){ll v=nHits[q];if(v>=64)throw runtime_error("histogram cap exceeded");nHits[q]=0;H+=v;F++;Z+=v*v;
         hist[size_t(min(64LL,v))]++;
         perPrimeHistogram[q][size_t(min(64LL,v))]++;
         if(v>maxN){maxN=int(v);maxAtQ=q;maxAtM=M;}
         int band=q<=B/16?0:q<=B/8?1:q<=B/4?2:q<=B/2?3:4;
         bandH[band]+=v;bandF[band]++;bandZ[band]+=v*v;
      }
    }
    if(Z<H||T19>H||H*H>ll(X/2)*piCount*Z)throw runtime_error("moment consistency");
    if((X==4096&&(H!=5391||F!=4823))||(X==16384&&(H!=31042||F!=25450))||(X==65536&&(H!=160698||F!=136058))||(X==262144&&(H!=868502||F!=703647))||(X==1048576&&(H!=4031949||F!=3248703))||(X==1999996&&(H!=8564171||F!=6757307)))throw runtime_error("old H/F regression mismatch");
    double maxDoublingTail=0;int maxDoubleAtK=0;
    vector<ll> globalTail(65,0);ll runningTail=0;
    for(int k=64;k>=1;k--){runningTail+=hist[k];globalTail[k]=runningTail;}
    ll ZfromTail=0;
    for(int k=1;k<=64;k++)ZfromTail+=(2LL*k-1)*globalTail[k];
    if(ZfromTail!=Z)throw runtime_error("summation-by-parts second moment identity failed");
    for(int k=1;k<=32;k++)if(globalTail[k]>0){const double ratio=double(globalTail[2*k])/globalTail[k];
      if(ratio>maxDoublingTail){maxDoublingTail=ratio;maxDoubleAtK=k;}}
    double maxQuadraticTail=0;int maxTailPrime=0,maxTailK=0;
    double q19tail2=0,q19tail5=0;
    for(int q=19;q<=B;q++)if(spf[q]==q){ll tail=0;
        for(int k=64;k>=1;k--){tail+=perPrimeHistogram[q][k];
          const double score=double(k)*k*tail/X;
          if(score>maxQuadraticTail){maxQuadraticTail=score;maxTailPrime=q;maxTailK=k;}
          if(q==19 && k==2)q19tail2=double(tail)/X;
          if(q==19 && k==5)q19tail5=double(tail)/X;
        }
    }
    cout<<"LABEL_MOMENT_PASS X="<<X<<" B="<<B<<" pi19="<<piCount<<" H="<<H<<" F="<<F<<" R="<<H-F<<" Z="<<Z<<" extraPair="<<(Z-H)/2
      <<" momentPerX="<<double(Z)/X<<" momentOverXB="<<double(Z)/(double(X)*B)
      <<" momentOverXBLogB="<<double(Z)/(double(X)*B*log(B))
      <<" momentOverXPi="<<double(Z)/(double(X)*piCount)
      <<" meanHitsPerUsedLabel="<<double(H)/F
      <<" secondPerUsedLabel="<<double(Z)/F
      <<" maxN="<<maxN<<" maxAtQ="<<maxAtQ<<" maxAtM="<<maxAtM
      <<" HoverXB="<<double(H)/(double(X)*B)
      <<" maxTailDoubling="<<maxDoublingTail<<" maxDoubleAtK="<<maxDoubleAtK
      <<" maxQuadraticTailRatio="<<maxQuadraticTail
      <<" maxTailPrime="<<maxTailPrime<<" maxTailK="<<maxTailK
      <<" q19Tail2PerX="<<q19tail2<<" q19Tail5PerX="<<q19tail5<<"\n";
    for(int i=0;i<5;i++)cout<<"LABEL_BAND X="<<X<<" band="<<i<<" H="<<bandH[i]<<" F="<<bandF[i]<<" Z="<<bandZ[i]<<" Z_over_H="<<(bandH[i]?double(bandZ[i])/bandH[i]:0)<<"\n";
    for(int k:{1,2,3,4,5,8,12,16,24,32,64}){ll count=0;for(size_t j=k;j<hist.size();j++)count+=hist[j];cout<<"LABEL_TAIL X="<<X<<" threshold="<<k<<" count="<<count<<" ratioOverF="<<double(count)/F<<"\n";}
}
int main(int argc,char**argv){if(argc<2)return 2;int maxX=0;vector<int>xs;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X>2000000||X%4)return 2;xs.push_back(X);maxX=max(maxX,X);}sieve(8*maxX+1000);
for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=jump_growth(M,41))throw runtime_error("literal original GCD mismatch");
for(int X:xs)run(X);}
