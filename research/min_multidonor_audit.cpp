#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using I=int64_t;
struct Hit{int t,p;bool operator==(Hit h)const{return t==h.t&&p==h.p;}};
struct State{int t,c;};
struct Wheel{
 int B;vector<int> spf;
 explicit Wheel(int X):B(int(ceil(sqrt(7.0*X)))),spf(7*X+64){for(int i=2;i<(int)spf.size();++i)if(!spf[i]){spf[i]=i;if(I(i)*i<(I)spf.size())for(I j=I(i)*i;j<(I)spf.size();j+=i)if(!spf[j])spf[j]=i;}}
 Hit hit(State s,int K)const{Hit best{K+1,0};for(int sign:{-1,1}){int z=s.c+sign;assert(z>0&&z<(int)spf.size());while(z>1){int p=spf[z];if(p>B)break;if(p>2){int m=2*p,r=sign==-1?0:p+2;int u=s.t+1+(r-(s.t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(z%p==0)z/=p;}}return best;}
 Hit literal(State s,int K)const{for(int n=s.t+1;n<=K;++n){int z=n%2?gcd(n-2,s.c+1):gcd(n,s.c-1);while(z>1){int p=spf[z];if(p>B)break;if(p>2)return {n,p};while(z%p==0)z/=p;}}return {K+1,0};}
 bool twin(int c)const{return spf[c-1]==c-1&&spf[c+1]==c+1;}
};
struct Event{int p,C,sign;};
struct Stats{I D=0,A=0,small=0,zero=0,one=0,same=0,mixed=0,two=0,twoSmall=0,twoClose=0,topTwo=0,oneLight=0,lightMulti=0,residual=0;vector<I> hist{0};
 void add(int n,int a){small+=n-1;A+=max(0,n-1-a);if(n>=(int)hist.size())hist.resize(n+1);++hist[n];}
 void out(int Q,int a,int P,int X){assert(D==small+zero+one+same+mixed);vector<I> tail(hist.size()+1);for(int k=(int)hist.size()-1;k>=1;--k)tail[k]=tail[k+1]+hist[k];double mx=0;for(int k=1;k<(int)hist.size();++k)if(2*k<(int)tail.size()&&tail[k])mx=max(mx,double(tail[2*k])/tail[k]);cout<<"Q="<<Q<<" a="<<a<<" D="<<D<<" A="<<A<<" small="<<small<<" zero="<<zero<<" one="<<one<<" same="<<same<<" mixed="<<mixed<<" two="<<two<<" twoSmall="<<twoSmall<<" twoClose="<<twoClose<<" topTwo="<<topTwo<<" oneLight="<<oneLight<<" lightMulti="<<lightMulti<<" residual="<<residual<<" smallMaxRatio="<<mx<<" A_over_XP="<<double(A)/(I(X)*P)<<"\n";}
};
void audit(int X){assert(X>=256&&X%4==0);Wheel w(X);int B=w.B,L=210,y=7;double logB=log(B);double cap=max(210.0,pow(logB,1.0/6));for(int p=11;p<=B;++p)if(w.spf[p]==p){if(I(L)*p>cap)break;L*=p;y=p;}
 int P=0;for(int p=y+1;p<=B;++p)if(w.spf[p]==p)++P;
 int Q[2]={int(ceil(B/pow(logB,1.0/3))),int(ceil(B/pow(logB,2.0/3)))};
 int a[2]={int(ceil(pow(logB,1.0/6))),int(ceil(pow(logB,1.0/3)))};
 int R[2]={max(31,int(ceil(logB))),max(31,int(ceil(pow(logB,1.0/4))))};int J=3*L+int(ceil(pow(logB,1.0/6)));Stats stats[2];
 vector<int> prev(B+1,-1),cnt(B+1),used;vector<Event> v;I checks=0,twins=0,stopped=0,returns=0,twoChecks=0;
 for(int M=X+1;M<2*X;M+=2){State s{M+2,2*M-2};int K=(7*M-1)/4;v.clear();used.clear();int lowGain=0;
  for(;;){Hit h=w.hit(s,K);if(X<=1024){assert(h==w.literal(s,K));++checks;}if(!h.p){++stopped;twins+=w.twin(s.c);break;}int p=h.p;if(p<=y){lowGain+=p-1;assert(lowGain<L);}else{lowGain=0;int sign=(s.c-1)%p==0?-1:1;assert((s.c+sign)%p==0);v.push_back({p,s.c,sign});assert(I(s.c-(2*M-2))<=I(2)*P*(B+L));if((int)v.size()==2*P)break;}s={h.t,s.c+p-1};assert(s.c<=2*s.t);}
  for(int j=0;j<(int)v.size();++j){int p=v[j].p;if(!cnt[p]++)used.push_back(p);int i=prev[p];prev[p]=j;if(i<0)continue;++returns;int E=v[j].C-v[i].C-(p-1);assert(E>=p-1);assert(((p-1)+E+v[j].sign-v[i].sign)%(2*p)==0);int m=j-i-1;bool same=m>=1;int maxq=0,largeIndex=-1;I highGain=0;
   for(int k=i+1;k<j;++k){int q=v[k].p;assert(q!=p);same=same&&q==v[i+1].p;highGain+=q-1;if(q>maxq){maxq=q;largeIndex=k;}}
   assert(E>=highGain&&E-highGain<I(m+1)*L);
   if(!m)assert(p-1<L);
   if(m>=2&&same){int q=v[i+1].p;assert(q-1<L);assert(E<I(L)*q);assert(p-1<I(L)*q);}
   if(m==2){++twoChecks;int q=v[i+1].p,r=v[i+2].p;int low=E-(q-1)-(r-1);int c=3-low+v[i].sign-v[j].sign;assert((q+r-c)%p==0);int k=(q+r-c)/p;assert(k>=1&&k%2==1);if(I(3)*p>=I(2)*B+3*L){assert(k==1);assert(2*min(q,r)<=p+5);}}
   for(int z=0;z<2;++z){auto &s0=stats[z];++s0.D;if(p<Q[z])continue;if(!m)++s0.zero;else if(m==1)++s0.one;else if(same)++s0.same;else ++s0.mixed;
    bool light=false,smallOrClose=false;
    if(m>=1){I other=E-(maxq-1);if(other<=J){light=true;int before=v[largeIndex].C-v[i].C-(p-1),after=v[j].C-v[largeIndex].C-(maxq-1);assert(before>=0&&after>=0&&I(before)+after==other);assert((maxq-2+before+after+v[j].sign-v[i].sign)%p==0);if(p>=2*J+2)assert(2*maxq>=p);++s0.oneLight;if(m>=2)++s0.lightMulti;}}
    if(m==2&&!same){++s0.two;int q=v[i+1].p,r=v[i+2].p;if(min(q,r)<=R[z]){smallOrClose=true;++s0.twoSmall;if(p>=2*(R[z]+3*L))assert(2*max(q,r)>=p);}if(abs(q-r)<=R[z]){smallOrClose=true;++s0.twoClose;}if(I(3)*p>=I(2)*B+3*L)++s0.topTwo;}
    if(m>=2&&!same&&!light&&!smallOrClose)++s0.residual;
   }
  }
  for(int p:used){for(int z=0;z<2;++z)if(p<Q[z])stats[z].add(cnt[p],a[z]);prev[p]=-1;cnt[p]=0;}
 }
 cout<<"X="<<X<<" B="<<B<<" y="<<y<<" L="<<L<<" P="<<P<<" R="<<R[0]<<","<<R[1]<<" J="<<J<<" stopped="<<stopped<<" twins="<<twins<<" literal="<<checks<<" returns="<<returns<<" twoChecks="<<twoChecks<<"\n";
 for(int z=0;z<2;++z)stats[z].out(Q[z],a[z],P,X);
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
