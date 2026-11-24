#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using I=int64_t; using U=uint64_t;
struct Hit{int t,p;};
struct Wheel{
 int B;vector<int> spf;
 explicit Wheel(int X):B(int(ceil(sqrt(7.0*X)))),spf(7*X+4){for(int i=2;i<int(spf.size());++i)if(!spf[i]){spf[i]=i;if(I(i)*i<I(spf.size()))for(I j=I(i)*i;j<I(spf.size());j+=i)if(!spf[j])spf[j]=i;}}
 Hit hit(int t,int C,int K)const{Hit best{K+1,0};for(int sign:{-1,1}){int v=C+sign;while(v>1){int p=spf[v];if(p>B)break;if(p>2){int m=2*p,r=sign==-1?0:p+2,u=t+1+(r-(t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(v%p==0)v/=p;}}return best;}
};
void audit(int X){assert(X>=256&&X%4==0);Wheel w(X);int B=w.B,Q=int(ceil(B/pow(log(B),2.0/3))),z=int(sqrt(sqrt(B))),L=210,P=0;for(int p=11;p<=B;++p)P+=w.spf[p]==p;int m=2*P;I N=X/2,threshold=I(B*log(B)),Hs=0,Hl=0,Hlong=0,R=0,smallWait=0,lowWait=0,shortWait=0,longWait=0,gain=0,elapsed=0,A=0;int a=int(ceil(pow(log(B),1.0/3)));vector<int> cnt(B+1),used;vector<U> longkeys;U stride=U(7)*X+4;
 for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4,j=0,block=0;I localLow=0,localSmall=0,localShort=0,localLong=0,localGain=0;int lastHigh=t;used.clear();while(j<m){Hit h=w.hit(t,C,K);if(!h.p)break;int p=h.p,d=h.t-t;assert(d<=2*p);int pre=C;t=h.t;C+=p-1;assert(C<=2*t);if(p<=7){block+=d;assert(block<3*L);continue;}++j;localLow+=block;block=0;lastHigh=t;if(!cnt[p]++)used.push_back(p);if(p<Q){++Hs;localSmall+=d;}else{++Hl;localGain+=p-1;if(d>2*z){++Hlong;R+=p;localLong+=d;assert(w.spf[pre-1]>z&&w.spf[pre+1]>z);longkeys.push_back(U(p)*stride+C);}else localShort+=d;}}
  assert(localLow+localSmall+localShort+localLong==lastHigh-(M+2));assert(localGain<=6+2*(lastHigh-(M+2)));lowWait+=localLow;smallWait+=localSmall;shortWait+=localShort;longWait+=localLong;gain+=localGain;elapsed+=lastHigh-(M+2);for(int p:used){if(p<Q)A+=max(0,cnt[p]-1-a);cnt[p]=0;}}
 assert(gain<=6*N+2*elapsed);assert((Q-1)*Hl<=6*N+6*L*(Hs+Hl)+4*Q*Hs+4*z*Hl+4*R);
 sort(longkeys.begin(),longkeys.end());I maxW=0,heavy=0,weightedHeavy=0,observed=0;for(size_t i=0,j;i<longkeys.size();i=j){for(j=i+1;j<longkeys.size()&&longkeys[j]==longkeys[i];++j){}I n=j-i,p=longkeys[i]/stride;maxW=max(maxW,n);heavy+=max(I(0),n-threshold);weightedHeavy+=p*max(I(0),n-threshold);++observed;}
 I T=0,Tweight=0;for(int p=max(Q,11);p<=B;++p)if(w.spf[p]==p){for(int sig:{-1,1}){I h=(2*I(X)+sig+p-1)/p;if(h%2==0)++h;for(;p*h-sig+p-1<7*I(X);h+=2){I pre=p*h-sig;if(pre<2*I(X))continue;if(w.spf[pre-1]>z&&w.spf[pre+1]>z){++T;Tweight+=p;}}}}
 assert(observed<=T);assert(R<=threshold*Tweight+weightedHeavy);cout<<"X="<<X<<" B="<<B<<" P="<<P<<" Q="<<Q<<" z="<<z<<" Hs="<<Hs<<" Hl="<<Hl<<" long="<<Hlong<<" R="<<R<<" longKeys="<<observed<<" maxLongW="<<maxW<<" tau="<<threshold<<" J="<<heavy<<" Jweighted="<<weightedHeavy<<" T="<<T<<" Tweight="<<Tweight<<" A="<<A<<" waitLow="<<lowWait<<" waitSmall="<<smallWait<<" waitShort="<<shortWait<<" waitLong="<<longWait<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
