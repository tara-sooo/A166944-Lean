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
struct Layer { vector<I> active,bad; void add(int r,bool inc){if(r>=(int)active.size()){active.resize(r+1);bad.resize(r+1);}++active[r];bad[r]+=inc;} };
void audit(int X){
 assert(X>=256&&X%4==0);Wheel w(X);int B=w.B,L=210,y=7;double logB=log(B);for(int p=11;p<=B;++p)if(w.spf[p]==p){if(I(L)*p>max(210.0,pow(logB,1.0/6)))break;L*=p;y=p;}
 int P=0;for(int p=y+1;p<=B;++p)if(w.spf[p]==p)++P;
 int Q=int(ceil(B/pow(logB,2.0/3))),a=int(ceil(pow(logB,1.0/3))),J=3*L+int(ceil(pow(logB,1.0/6))),R=max(31,int(ceil(pow(logB,1.0/4))));
 int b=max(1,(P+1)/2),m=2*P; I N=X/2;
 vector<Layer> layers(m), allLayers(m); vector<I> hard(m),soft(m),nActive(m),fullhist(m+1);vector<int> prev(B+1,-1),cnt(B+1),used;vector<Event> v;
 I checks=0,twins=0,ends=0,totalBad=0,stoppedBad=0,hardKilled=0,softKilled=0,A=0,res=0,cheap=0,baseline=0,remainingClean=0;int maxRank=0,maxCost=0,maxAll=0; I allKilled=0;
 for(int M=X+1;M<2*X;M+=2){State s{M+2,2*M-2};int K=(7*M-1)/4;v.clear();used.clear();
  for(;;){Hit h=w.hit(s,K);if(X<=1024){assert(h==w.literal(s,K));++checks;}if(!h.p){++ends;twins+=w.twin(s.c);break;}int p=h.p;if(p>y){v.push_back({p,s.c,(s.c-1)%p==0?-1:1});if((int)v.size()==m)break;}s={h.t,s.c+p-1};assert(s.c<=2*s.t);}
  int cost=0,sm=0,large=0,allCost=0; bool liveHard=true;
  for(int j=0;j<(int)v.size();++j){++nActive[j];int p=v[j].p;if(!cnt[p]++)used.push_back(p);int i=prev[p];prev[p]=j;bool inc=false,largeInc=false;
   if(i>=0){if(p<Q){inc=cnt[p]>a+1;if(inc){++sm;++A;}else ++baseline;}
    else{int E=v[j].C-v[i].C-(p-1),d=j-i-1,maxq=0;bool same=d>=1;for(int k=i+1;k<j;++k){int q=v[k].p;assert(q!=p);same=same&&q==v[i+1].p;maxq=max(maxq,q);}bool light=d>=1&&E-(maxq-1)<=J;bool special=d==2&&(min(v[i+1].p,v[i+2].p)<=R||abs(v[i+1].p-v[i+2].p)<=R);inc=largeInc=d>=2&&!same&&!light&&!special;if(inc){++large;++res;}else ++cheap;}}
   if(cost<b)layers[j].add(cost,inc);
   if(allCost<P)allLayers[j].add(allCost,i>=0);
   if(i>=0&&++allCost==P)++allKilled;
   if(liveHard&&(largeInc||sm>P/2)){++hard[j];++hardKilled;liveHard=false;}
   if(inc){++cost;if(cost==b){++soft[j];++softKilled;}}
  }
  assert(cost==sm+large);totalBad+=cost;stoppedBad+=min(cost,b);++fullhist[cost];maxCost=max(maxCost,cost);maxAll=max(maxAll,allCost);maxRank=max(maxRank,(int)v.size());remainingClean+=liveHard;for(int p:used){prev[p]=-1;cnt[p]=0;}
 }
 assert(totalBad==A+res);assert(remainingClean+hardKilled==N);
 // w[r] includes the already-terminal sources as frozen states. The last layer b is absorbed.
 vector<I> mass(b+1);mass[0]=N;I live=N,hardLive=N;double hardScaled=0,softScaled=0,incFrac=0; I maxInc=0; vector<int> eta={1,2,3,4}; // eta in tenths
 vector<I> excess10(eta.size());I totalFlow=0;int hardRank=0,softRank=0;
 for(int j=0;j<m;++j){const Layer &z=layers[j];I step=0;vector<I> next=mass;for(int r=0;r<(int)z.active.size();++r){assert(r<b&&z.active[r]<=mass[r]);I f=z.bad[r];assert(f<=z.active[r]);step+=f;next[r]-=f;next[r+1]+=f;}for(size_t k=0;k<eta.size();++k){I err=0;for(int r=0;r<b;++r){I f=r<(int)z.bad.size()?z.bad[r]:0;err=max(err,10*f-eta[k]*mass[r]);}excess10[k]+=err;}
  totalFlow+=step;maxInc=max(maxInc,step);assert(next[b]-mass[b]==soft[j]);mass.swap(next);assert(accumulate(mass.begin(),mass.end(),I(0))==N);
  if(hardLive&&double(hard[j])*P/hardLive>hardScaled){hardScaled=double(hard[j])*P/hardLive;hardRank=j+1;}if(live&&double(soft[j])*P/live>softScaled){softScaled=double(soft[j])*P/live;softRank=j+1;}if(live)incFrac=max(incFrac,double(step)/live);live-=soft[j];hardLive-=hard[j];
 }
 assert(mass[b]==softKilled&&totalFlow==stoppedBad);assert(live==N-softKilled);for(int r=0;r<b;++r)assert(mass[r]==fullhist[r]);
 vector<I> allMass(P+1);allMass[0]=N;vector<I> allExcess10(eta.size());double allMaxFrac=0,allActiveFrac=0,activeBadFrac=0;
 for(int j=0;j<m;++j){const Layer &z=allLayers[j];I step=0,active=0;vector<I> next=allMass;for(int r=0;r<(int)z.active.size();++r){assert(r<P&&z.active[r]<=allMass[r]);I f=z.bad[r];assert(f<=z.active[r]);step+=f;active+=z.active[r];next[r]-=f;next[r+1]+=f;}for(size_t k=0;k<eta.size();++k){I err=0;for(int r=0;r<P;++r){I f=r<(int)z.bad.size()?z.bad[r]:0;err=max(err,10*f-eta[k]*allMass[r]);}allExcess10[k]+=err;}
  if(N>allMass[P])allMaxFrac=max(allMaxFrac,double(step)/(N-allMass[P]));
  if(active)allActiveFrac=max(allActiveFrac,double(step)/active);
  const Layer &badLayer=layers[j]; I n0=accumulate(badLayer.active.begin(),badLayer.active.end(),I(0)),f0=accumulate(badLayer.bad.begin(),badLayer.bad.end(),I(0));if(n0)activeBadFrac=max(activeBadFrac,double(f0)/n0);
  allMass.swap(next);assert(accumulate(allMass.begin(),allMass.end(),I(0))==N);
 }assert(allMass[P]==allKilled);
 cout<<"X="<<X<<" B="<<B<<" P="<<P<<" b="<<b<<" N="<<N<<" maxRank="<<maxRank<<" maxCost="<<maxCost<<" twins="<<twins<<" ends="<<ends<<" checks="<<checks<<" A="<<A<<" res="<<res<<" cheap="<<cheap<<" baseline="<<baseline<<" hardKilled="<<hardKilled<<" softKilled="<<softKilled<<" totalBad="<<totalBad<<" stoppedBad="<<stoppedBad<<" hardScaled="<<hardScaled<<" hardRank="<<hardRank<<" softScaled="<<softScaled<<" softRank="<<softRank<<" maxIncFrac="<<incFrac<<" maxInc="<<maxInc<<" excessFrac=";for(size_t k=0;k<eta.size();++k)cout<<eta[k]<<":"<<double(excess10[k])/(10*N)<<",";cout<<" maxAll="<<maxAll<<" allKilled="<<allKilled<<" allMaxFrac="<<allMaxFrac<<" allActiveFrac="<<allActiveFrac<<" activeBadFrac="<<activeBadFrac<<" allExcessFrac=";for(size_t k=0;k<eta.size();++k)cout<<eta[k]<<":"<<double(allExcess10[k])/(10*N)<<",";cout<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
