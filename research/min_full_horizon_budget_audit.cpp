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
void audit(int X){Wheel w(X);int B=w.B,z=int(sqrt(sqrt(B)));I tau=I(B*log(B)),total=0,elapsed=0,travel=0,bad=0;vector<int> W(7*X/2+1);for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4;travel+=K-t;while(true){Hit h=w.hit(t,C,K);if(!h.p){if(w.spf[C-1]!=C-1||w.spf[C+1]!=C+1){++bad;assert(K-t<2*B);}break;}int r=min(w.spf[C-1],w.spf[C+1]);assert(r<=B&&h.t-t<=2*r);++W[C/2];++total;elapsed+=h.t-t;t=h.t;C+=h.p-1;assert(C<=2*t);}}
I J=0,maxw=0,baseline=0,R=0,maxC=0,heavy=0,rough=0,maxRoughW=0;for(int C=2*X;C<7*X;C+=2){I n=W[C/2];int r=min(w.spf[C-1],w.spf[C+1]);if(r>B){assert(n==0);continue;}baseline+=r;R+=r*n;if(n>maxw){maxw=n;maxC=C;}if(n>tau){J+=r*(n-tau);++heavy;}if(r>z){++rough;maxRoughW=max(maxRoughW,n);}}assert(elapsed<=2*R&&R<=tau*baseline+J);assert(travel==9*I(X)*X/16-5*I(X)/4);cout<<"X="<<X<<" B="<<B<<" tau="<<tau<<" maxW="<<maxw<<" maxC="<<maxC<<" maxRoughW="<<maxRoughW<<" rough="<<rough<<" total="<<total<<" heavy="<<heavy<<" J="<<J<<" base="<<baseline<<" R="<<R<<" elapsed="<<elapsed<<" bad="<<bad<<"\n";}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
