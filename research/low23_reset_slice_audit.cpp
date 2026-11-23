// Exhaustive LOW wheel starting at real parity-compatible RESET manifold.
// This certifies ONLY RESET-slice initial states, not arbitrary charged high-post states.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low23_reset_slice_audit.cpp -o /tmp/reset23
// /tmp/reset23 17 510510; /tmp/reset23 19 9699690
// /tmp/reset23 23 75000000 0
// /tmp/reset23 23 150000000 75000000
// /tmp/reset23 23 223092870 150000000
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <algorithm>
#include <limits>
#include <stdexcept>
#include <vector>
using namespace std;
using i64=long long;
static const array<int,8> primes={3,5,7,11,13,17,19,23};
struct Result {int events,time,high,lastHigh,prefixGain,activeMaxZ; i64 growth; bool terminal;};
int gap(i64 t,int p,int r){int x=int((r-t)%(2LL*p));return x>0?x:x+2*p;}
Result run_one(int r,int P,int primeCut){
  int L=2*P,par=r&1,z=par?6:0;
  i64 t=5LL*L+r,c=2*t-z,start=t,c0=c;
  int ev=0,high=0,last=0,prefixGain=0,activeMaxZ=0;
  for(;ev<3000;){
    int delta=numeric_limits<int>::max(),d=1;
    for(int p:primes){if(p>primeCut)break;
      int rem=-1;
      if((c-1)%p==0)rem=0;
      else if((c+1)%p==0)rem=p+2;
      if(rem<0)continue;
      int w=gap(t,p,rem);
      if(w<delta){delta=w;d=p;}
      else if(w==delta)d*=p;
    }
    if(delta==numeric_limits<int>::max())return {ev,int(t-start),high,last,prefixGain,activeMaxZ,c-c0,true};
    prefixGain=max(prefixGain,int(2*(t-start)-(c-c0)));
    activeMaxZ=max(activeMaxZ,int(2*t-c));
    t+=delta;c+=d-1;ev++;
    if(d%primeCut==0){high++;last=int(t-start);}
  }
  return {ev,int(t-start),high,last,prefixGain,activeMaxZ,c-c0,false};
}
int main(int argc,char**argv){
 int primeCut=argc>1?atoi(argv[1]):19;
 int upto=argc>2?atoi(argv[2]):100000;
 int from=argc>3?atoi(argv[3]):0;
 if(primeCut!=17&&primeCut!=19&&primeCut!=23)
     throw runtime_error("primeCut must be 17, 19 or 23");
 int P=1;for(int p:primes){if(p>primeCut)break;P*=p;}
 int L=2*P;upto=min(upto,L);if(from<0||from>=upto)throw runtime_error("bad range");
 i64 term=0,nonterm=0,totalEvents=0,withQ=0,maxG=0;
 int maxEv=0,maxT=0,maxHigh=0,maxPrefixGain=0,maxActiveZ=0,maxEvAt=-1,maxTAt=-1,maxHAt=-1,maxGAt=-1,maxPrefixAt=-1,maxActiveZAt=-1;
 for(int r=from;r<upto;r++){
   Result a=run_one(r,P,primeCut);
   if(a.terminal)term++;else nonterm++;
   totalEvents+=a.events;withQ+=(a.high>0);
   if(a.events>maxEv){maxEv=a.events;maxEvAt=r;}
   if(a.time>maxT){maxT=a.time;maxTAt=r;}
   if(a.high>maxHigh){maxHigh=a.high;maxHAt=r;}
   if(a.growth>maxG){maxG=a.growth;maxGAt=r;}
   if(a.prefixGain>maxPrefixGain){maxPrefixGain=a.prefixGain;maxPrefixAt=r;}
   if(a.activeMaxZ>maxActiveZ){maxActiveZ=a.activeMaxZ;maxActiveZAt=r;}
   if((r+1)%1000000==0)cerr<<"SCANNED "<<r+1<<" / "<<upto<<"\n";
 }
 cout<<"RESET_SLICE q="<<primeCut<<" P="<<P<<" L="<<L<<" from="<<from<<" to="<<upto
     <<" terminal="<<term<<" nonterminal="<<nonterm
     <<" maxEvents="<<maxEv<<" maxEventsAt="<<maxEvAt
     <<" maxTime="<<maxT<<" maxTimeAt="<<maxTAt
     <<" maxQhits="<<maxHigh<<" maxQhitsAt="<<maxHAt
     <<" maxGrowth="<<maxG<<" maxGrowthAt="<<maxGAt
     <<" maxPrefixGain="<<maxPrefixGain<<" maxPrefixGainAt="<<maxPrefixAt
     <<" maxActiveZ="<<maxActiveZ<<" maxActiveZAt="<<maxActiveZAt
     <<" withQ="<<withQ<<" meanEvents="<<double(totalEvents)/(upto-from)<<"\n";
 if(nonterm)throw runtime_error("nonterminating RESET slice found");
 if(from==0 && upto==L){
   if(primeCut==17 && (maxEv!=40||maxT!=239||maxHigh!=4||maxG!=316||maxPrefixGain!=270||maxActiveZ!=270))
     throw runtime_error("LOW17 full RESET slice finite regression");
   if(primeCut==19 && (maxEv!=56||maxT!=388||maxHigh!=5||maxG!=568||maxPrefixGain!=418||maxActiveZ!=424))
     throw runtime_error("LOW19 full RESET slice finite regression");
   if(primeCut==23 && (maxEv!=88||maxT!=599||maxHigh!=6||maxG!=946||maxPrefixGain!=556||maxActiveZ!=558))
     throw runtime_error("LOW23 full RESET slice finite regression");
 }
 if(primeCut==23 && from==0 && upto==75000000 && (maxEv!=75||maxT!=599||maxHigh!=6||maxG!=820||maxPrefixGain!=552||maxActiveZ!=558))
    throw runtime_error("LOW23 reset partition 1 regression");
 if(primeCut==23 && from==75000000 && upto==150000000 && (maxEv!=68||maxT!=514||maxHigh!=5||maxG!=796||maxPrefixGain!=556||maxActiveZ!=556))
    throw runtime_error("LOW23 reset partition 2 regression");
 if(primeCut==23 && from==150000000 && upto==L && (maxEv!=88||maxT!=533||maxHigh!=6||maxG!=946||maxPrefixGain!=552||maxActiveZ!=558))
    throw runtime_error("LOW23 reset partition 3 regression");
}
