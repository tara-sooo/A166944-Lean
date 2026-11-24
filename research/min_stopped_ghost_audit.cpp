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
struct Choice{Hit h;int C;};
struct Ghost{Choice actual;bool risk=false,allRisk=false,smallRisk=false,largeRisk=false;};
bool bad(int p,int C,const vector<Event>&v,const vector<int>&prev,const vector<int>&cnt,int Q,int a,int J,int R){
 int i=prev[p];if(i<0)return false;if(p<Q)return cnt[p]>=a+1;
 int d=int(v.size())-i-1;if(d<2)return false;int E=C-v[i].C-(p-1),maxq=0;bool same=true;
 for(int k=i+1;k<(int)v.size();++k){int q=v[k].p;assert(q!=p);maxq=max(maxq,q);same=same&&q==v[i+1].p;}
 if(same||E-(maxq-1)<=J)return false;
 if(d==2&&(min(v[i+1].p,v[i+2].p)<=R||abs(v[i+1].p-v[i+2].p)<=R))return false;
 return true;
}
Ghost scan(const Wheel&w,State s,int K,int y,int L,int Q,int a,int J,int R,const vector<Event>&v,const vector<int>&prev,const vector<int>&cnt){
 Ghost g{{{K+1,0},s.c}};int start=s.c;
 for(;;){Hit low{K+1,0};vector<Hit> high;
  for(int sign:{-1,1}){int z=s.c+sign;while(z>1){int p=w.spf[z];if(p>w.B)break;if(p>2){int m=2*p,r=sign==-1?0:p+2,u=s.t+1+(r-(s.t+1)%m+m)%m;if(u<=K){if(p<=y){if(u<low.t||(u==low.t&&p<low.p))low={u,p};}else high.push_back({u,p});}}while(z%p==0)z/=p;}}
  Hit first=low;
  for(Hit h:high)if(h.t<low.t||(h.t==low.t&&h.p<low.p)){
   if(h.t<first.t||(h.t==first.t&&h.p<first.p))first=h;
   if(prev[h.p]>=0)g.allRisk=true;
   if(bad(h.p,s.c,v,prev,cnt,Q,a,J,R)){g.risk=true;if(h.p<Q)g.smallRisk=true;else g.largeRisk=true;}
  }
  if(!g.actual.h.p&&first.p>y)g.actual={first,s.c};
  if(!low.p)break;
  s={low.t,s.c+low.p-1};assert(s.c-start<L);
 }
 return g;
}
struct Layer {vector<I> active,risk,inc;void add(int r,bool x,bool b){if(r>=(int)active.size()){active.resize(r+1);risk.resize(r+1);inc.resize(r+1);}++active[r];risk[r]+=x;inc[r]+=b;assert(!b||x);}};
void audit(int X){Wheel w(X);int B=w.B,y=7,L=210;double logB=log(B);for(int p=11;p<=B;++p)if(w.spf[p]==p){if(I(L)*p>max(210.0,pow(logB,1.0/6)))break;L*=p;y=p;}int P=0;for(int p=y+1;p<=B;++p)if(w.spf[p]==p)++P;int Q=int(ceil(B/pow(logB,2.0/3))),a=int(ceil(pow(logB,1.0/3))),J=3*L+int(ceil(pow(logB,1.0/6))),R=max(31,int(ceil(pow(logB,1.0/4)))),m=2*P,b=(P+1)/2;I N=X/2;
 vector<Layer> badLayers(m),allLayers(m);vector<int> prev(B+1,-1),cnt(B+1),used;vector<Event> v;I tested=0,allRisk=0,allInc=0,risk=0,inc=0,smallRisk=0,largeRisk=0;
 for(int M=X+1;M<2*X;M+=2){State s{M+2,2*M-2};int K=(7*M-1)/4,cost=0,allCost=0;used.clear();v.clear();
  for(int j=0;j<m;++j){Ghost g=scan(w,s,K,y,L,Q,a,J,R,v,prev,cnt);Hit h;State oracle=s;for(;;){h=w.hit(oracle,K);if(!h.p||h.p>y)break;oracle={h.t,oracle.c+h.p-1};}assert(h==g.actual.h);++tested;if(!h.p){assert(!g.risk&&!g.allRisk);break;}assert(oracle.c==g.actual.C);int p=h.p,C=oracle.c;bool actual=bad(p,C,v,prev,cnt,Q,a,J,R),repeat=prev[p]>=0;
   if(cost<b){badLayers[j].add(cost,g.risk,actual);risk+=g.risk;inc+=actual;smallRisk+=g.smallRisk;largeRisk+=g.largeRisk;}
   if(allCost<P){allLayers[j].add(allCost,g.allRisk,repeat);allRisk+=g.allRisk;allInc+=repeat;}
   cost+=actual;allCost+=repeat;if(!cnt[p]++)used.push_back(p);prev[p]=j;v.push_back({p,C,(C-1)%p==0?-1:1});s={h.t,C+p-1};
  }for(int p:used){cnt[p]=0;prev[p]=-1;}
 }
 auto summary=[&](const vector<Layer>&layers,int cap,int eta){vector<I> mass(cap+1);mass[0]=N;I excess=0;double peak=0;for(auto &z:layers){vector<I> next=mass;I err=0,step=0;for(int r=0;r<cap;++r){I f=0,d=0;if(r<(int)z.active.size()){f=z.inc[r];d=z.risk[r];assert(z.active[r]<=mass[r]);}err=max(err,10*d-eta*mass[r]);next[r]-=f;next[r+1]+=f;step+=d;}excess+=err;peak=max(peak,double(step)/N);mass.swap(next);}cout<<" peak="<<peak<<" excess="<<double(excess)/(10*N)<<" killed="<<mass[cap];};
 cout<<"X="<<X<<" P="<<P<<" tested="<<tested<<" badRisk="<<risk<<" badInc="<<inc<<" smallRisk="<<smallRisk<<" largeRisk="<<largeRisk<<" allRisk="<<allRisk<<" allInc="<<allInc<<" bad(eta=.2)";summary(badLayers,b,2);cout<<" all(eta=.4)";summary(allLayers,P,4);cout<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
