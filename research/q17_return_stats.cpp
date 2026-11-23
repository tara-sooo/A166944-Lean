// Sampled q-return dynamics: exact original parity clipped-GCD clocks for S<=q.
// Verifies the q=13 graph against exhaustive prior certificate and probes q=17.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror q17_sample_return.cpp -o sample
// ./sample 17 200000
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <random>
#include <stdexcept>
#include <unordered_map>
#include <vector>
#include <string>
using namespace std;
using i64=long long;
static constexpr array<int,7> primes={3,5,7,11,13,17,19};
struct Result{int next;int events;int elapsed;int lowGrowth;int largeIncrement;};
int gap(int t,int p,int r){int v=(r-t)%(2*p);if(v<=0)v+=2*p;return v;}
struct Graph{
 int q,P,L,N,perTime,halfC,evenClasses,oddClasses;vector<int> times,tindex;
 Graph(int qq):q(qq),P(1){for(int p:primes){if(p>q)break;P*=p;}L=2*P;perTime=2*(P/q);halfC=P/q;N=perTime*halfC;
  tindex.assign(L,-1);
  for(int t=0;t<L;t++)if((t%2==0&&t%q==0)||(t%2==1&&(t-2+q)%q==0)){tindex[t]=int(times.size());times.push_back(t);}
  if(int(times.size())!=perTime)throw runtime_error("time list count");
  evenClasses=oddClasses=0;for(int t:times){if(t%2)oddClasses++;else evenClasses++;}
 }
 pair<int,int> state(int id)const{int ti=id/halfC,j=id%halfC,t=times[ti],k0=t%2?q-1:0,c=2*(k0+q*j);return {t+5*L,c+5*L};}
 Result next(int id)const{
  auto [t0,c0]=state(id);int t=t0,c=c0,steps=0,lowGrowth=0;
  for(int j=0;j<80;j++){
   int dt=numeric_limits<int>::max(),d=1;
   for(int p:primes){if(p>q)break;int r=-1;
    if((c-1)%p==0)r=0;else if((c+1)%p==0)r=p+2;
    if(r<0)continue;
    int dd=gap(t,p,r);
    if(dd<dt){dt=dd;d=p;}else if(dd==dt)d*=p;
   }
   if(dt==numeric_limits<int>::max())return {-1,steps,t-t0,lowGrowth,0};
   t+=dt;c+=d-1;steps++;
   if(d%q==0){int tm=t%L,cm=c%L,ti=tindex[tm];if(ti<0||cm%2)throw runtime_error("q post-state modular invalid");
    int k=cm/2,k0=tm%2?q-1:0;
    if(k<k0||(k-k0)%q)throw runtime_error("q post-C modular invalid");
    int out=ti*halfC+(k-k0)/q;
    if(out<0||out>=N)throw runtime_error("next id invalid");
    return {out,steps,t-t0,lowGrowth,d};
   }
   lowGrowth+=d-1;
  }
  throw runtime_error("low-only run exceeds80 events");
 }
 // Validate q activation from lower-only growth with FULL-WHEEL direct successor.
 Result by_low_trace(int id)const{
  auto [t0,c0]=state(id);int t=t0,c=c0,steps=0,lowGrowth=0;
  for(int j=0;j<80;j++){
   int nextLow=numeric_limits<int>::max(),lowD=1;
   for(int p:primes){if(p>=q)break;int r=-1;
    if((c-1)%p==0)r=0;else if((c+1)%p==0)r=p+2;
    if(r<0)continue;
    int dd=gap(t,p,r);
    if(dd<nextLow){nextLow=dd;lowD=p;}else if(dd==nextLow)lowD*=p;
   }
   const int off=t0%2? -2:0;
   int E=c-c0;
   bool activated=((c-1)%q==0||(c+1)%q==0);
   bool expected=((E+off-1)%q==0||(E+off+1)%q==0);
   if(activated!=expected)throw runtime_error("growth activation mismatch");
   int dq=numeric_limits<int>::max();
   if(activated){int r=(c-1)%q==0?0:q+2;dq=gap(t,q,r);}
   if(activated&&dq<=nextLow){if(dq==nextLow)lowD*=q;else lowD=q;
    t+=dq;c+=lowD-1;steps++;
    int tm=t%L,cm=c%L,ti=tindex[tm],k0=tm%2?q-1:0;
    if(ti<0||cm%2||(cm/2-k0)%q)throw runtime_error("low trace post q mismatch");
    int out=ti*halfC+(cm/2-k0)/q;
    return {out,steps,t-t0,lowGrowth,lowD};
   }
   if(nextLow==numeric_limits<int>::max())return {-1,steps,t-t0,lowGrowth,0};
   t+=nextLow;c+=lowD-1;steps++;lowGrowth+=lowD-1;
  }
  throw runtime_error("lower-only trace exceeds80 events");
 }
};
int main(int argc,char**argv){if(argc<2)return 2;int q=atoi(argv[1]);Graph g(q);
 if(argc==5&&string(argv[2])=="range"){
   int begin=atoi(argv[3]),end=atoi(argv[4]);
   if(begin<0||end>g.N||begin>=end)throw runtime_error("bad stats range");
   int maxEvents=0,maxElapsed=0,maxGrowth=0,maxDepth=0;
   int maxEventsId=-1,maxElapsedId=-1,maxGrowthId=-1,maxDepthId=-1;
   for(int id=begin;id<end;id++){
     int cur=id,ev=0,elapsed=0,growth=0,depth=0;
     for(int iter=0;iter<15;iter++){
       Result r=g.next(cur);
       ev+=r.events;elapsed+=r.elapsed;growth+=r.lowGrowth;
       if(r.next<0)break;
       growth+=r.largeIncrement-1;depth++;cur=r.next;
       if(iter==14)throw runtime_error("q chain longer than15 unexpected");
     }
     if(ev>maxEvents){maxEvents=ev;maxEventsId=id;}
     if(elapsed>maxElapsed){maxElapsed=elapsed;maxElapsedId=id;}
     if(growth>maxGrowth){maxGrowth=growth;maxGrowthId=id;}
     if(depth>maxDepth){maxDepth=depth;maxDepthId=id;}
   }
   cout<<"FULL_STATS_RANGE q="<<q<<" begin="<<begin<<" end="<<end
       <<" maxPostQEvents="<<maxEvents<<" maxPostQEventsId="<<maxEventsId
       <<" maxPostQElapsed="<<maxElapsed<<" maxPostQElapsedId="<<maxElapsedId
       <<" maxPostQGrowth="<<maxGrowth<<" maxPostQGrowthId="<<maxGrowthId
       <<" maxQReturnDepth="<<maxDepth<<" maxQReturnDepthId="<<maxDepthId<<"\n";
   return 0;
 }
 int samples=argc>=3?atoi(argv[2]):100000;
 cout<<"GRAPH_GEOMETRY q="<<q<<" states="<<g.N<<" timeClasses="<<g.perTime<<" cClasses="<<g.halfC<<" parityEven="<<g.evenClasses<<" parityOdd="<<g.oddClasses<<"\n";
 mt19937 gen(20261123);uniform_int_distribution<int> dist(0,g.N-1);int roots=0,term=0,maxDepth=0,maxSteps=0,maxWait=0,maxLowGrowth=0,cycleWitness=-1;long long totalDepth=0;array<long long,25>hist{};
 for(int k=0;k<samples;k++){
  int id=k<min(samples,1500)?int((int64_t)k*g.N/max(1,min(samples,1500))):dist(gen);
  auto first=g.next(id),second=g.by_low_trace(id);
  if(first.next!=second.next||first.events!=second.events||first.elapsed!=second.elapsed||first.lowGrowth!=second.lowGrowth||first.largeIncrement!=second.largeIncrement)throw runtime_error("exact low-trace successor mismatch");
  if(first.next>=0)roots++;else term++;
  int depth=0,x=id;unordered_map<int,int>seen;
  for(int iter=0;iter<80;iter++){
   if(seen.count(x)){cycleWitness=x;break;}
   seen[x]=depth;
   auto v=g.next(x);
   maxSteps=max(maxSteps,v.events);maxWait=max(maxWait,v.elapsed);maxLowGrowth=max(maxLowGrowth,v.lowGrowth);
   if(v.next<0)break;
   x=v.next;depth++;
  }
  if(cycleWitness>=0)break;
  maxDepth=max(maxDepth,depth);totalDepth+=depth;if(depth>=int(hist.size()))throw runtime_error("depth histogram overflow");hist[depth]++;
 }
 cout<<"SAMPLE_RETURN q="<<q<<" sampled="<<samples<<" immediateReturns="<<roots<<" terminal="<<term<<" maxFutureDepth="<<maxDepth<<" maxSegmentLowEvents="<<maxSteps<<" maxSegmentWait="<<maxWait<<" maxSegmentLowGrowth="<<maxLowGrowth<<" cycleWitness="<<cycleWitness<<" meanFutureDepth="<<double(totalDepth)/samples;
 for(int i=0;i<min(10,int(hist.size()));i++){cout<<" h"<<i<<"="<<hist[i];}cout<<"\n";
 if(q==13&&maxDepth>5)throw runtime_error("q13 previously certified depth violated");
 if(cycleWitness>=0)throw runtime_error("actual modular q recurrence cycle FOUND");
}
