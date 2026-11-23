// EXHAUSTIVE exact {3,5,7,11,13} q=13 post-event renewal graph.
// All q13 event-post classes (t mod30030, C even mod30030): 2310*1155 nodes.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror q13_renewal_graph.cpp -o graph
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
static constexpr int P=15015,L=30030,N=2310*1155;
static constexpr array<int,5> ps={3,5,7,11,13};
int clk(int t,int q,int rem){int r=(rem-t)%(2*q);return r>0?r:r+2*q;}
int main(){
 vector<int> timeIndex(L,-1),timeValue;timeValue.reserve(2310);
 for(int t=0;t<L;t++)if((t%2==0&&t%13==0)||(t%2==1&&(t-2+13)%13==0)){
  timeIndex[t]=int(timeValue.size());timeValue.push_back(t);
 }
 if(timeValue.size()!=2310)throw runtime_error("time classes not2310");
 vector<int> nxt(N,-1),degree(N,0),lowCount(N,0),wait(N,0),segmentGrowth(N,0);int maxLow=0,maxSpan=0,terminal=0,multiple13=0;
 for(int ti=0;ti<2310;ti++){
  const int tm=timeValue[ti],k0=tm%2?12:0;
  for(int j=0;j<1155;j++){
   int k=k0+13*j,cmod=2*k,id=ti*1155+j;
   int t=tm+5*L,C=cmod+5*L,start=t,initialC=C;
   for(int events=0;events<24;events++){
    int dt=INT32_MAX,d=1;
    for(int q:ps){int rem=-1;if((C-1)%q==0)rem=0;else if((C+1)%q==0)rem=q+2;
      if(rem<0)continue;
      int v=clk(t,q,rem);
      if(v<dt){dt=v;d=q;}else if(v==dt)d*=q;
    }
    if(dt==INT32_MAX){terminal++;wait[id]=t-start;segmentGrowth[id]=C-initialC;break;}
    t+=dt;C+=d-1;
    if(d%13==0){int t2=t%L,c2=C%L,ti2=timeIndex[t2];if(ti2<0)throw runtime_error("next 13 time class invalid");
      int k2=c2/2,off=t2%2?12:0;
      if(k2<off||(k2-off)%13)throw runtime_error("next 13 post C class invalid");
      int j2=(k2-off)/13;
      if(j2>=1155)throw runtime_error("q13 class index invalid");
      int v=ti2*1155+j2;
      if(v==id){cout<<"SELF_CYCLE at node "<<id<<" t="<<tm<<" c="<<cmod<<" elapsed="<<t-start<<"\n";}
      nxt[id]=v;degree[v]++;wait[id]=t-start;segmentGrowth[id]=C-initialC;maxSpan=max(maxSpan,t-start);
      if(d!=13)multiple13++;
      break;
    }
    lowCount[id]++;maxLow=max(maxLow,lowCount[id]);
    if(events==23)throw runtime_error("q13-free low stage exceeded 24 events");
   }
  }
 }
 vector<int>order;order.reserve(N);
 for(int i=0;i<N;i++)if(degree[i]==0)order.push_back(i);
 for(size_t i=0;i<order.size();i++){int v=nxt[order[i]];if(v>=0&&--degree[v]==0)order.push_back(v);}
 int cycles=N-int(order.size());int maxFollow13=0,maxId=-1,maxPostElapsed=0,maxPostEvents=0,maxPostGrowth=0,maxElapsedId=-1;array<int,7> depthHistogram{};
 if(cycles==0){vector<int> dp(N),et(N),tm(N),gr(N);
 for(int i=N-1;i>=0;i--){int u=order[i],v=nxt[u];
  dp[u]=(v<0?0:1+dp[v]);
  et[u]=lowCount[u]+(v<0?0:1+et[v]);
  tm[u]=wait[u]+(v<0?0:tm[v]);
  gr[u]=segmentGrowth[u]+(v<0?0:gr[v]);
  if(dp[u]>maxFollow13){maxFollow13=dp[u];maxId=u;}
  if(dp[u]>=int(depthHistogram.size()))throw runtime_error("unexpected depth");
  depthHistogram[dp[u]]++;
  if(tm[u]>maxPostElapsed){maxPostElapsed=tm[u];maxElapsedId=u;}
  maxPostEvents=max(maxPostEvents,et[u]);maxPostGrowth=max(maxPostGrowth,gr[u]);
 }
}
 cout<<"Q13_RENEWAL_GRAPH states="<<N<<" terminal="<<terminal<<" edges="<<N-terminal
  <<" acyclicNodes="<<order.size()<<" cycleNodes="<<cycles<<" maxLowEventsInStage="<<maxLow
  <<" maxWaitToNext13="<<maxSpan<<" maxFollowing13Events="<<maxFollow13<<" maxDepthNode="<<maxId
  <<" maxPost13Events="<<maxPostEvents<<" maxPost13Elapsed="<<maxPostElapsed<<" maxPost13Growth="<<maxPostGrowth<<" longestElapsedNode="<<maxElapsedId<<" multi13CompositeEvents="<<multiple13
  <<" depth0="<<depthHistogram[0]<<" depth1="<<depthHistogram[1]<<" depth2="<<depthHistogram[2]<<" depth3="<<depthHistogram[3]<<" depth4="<<depthHistogram[4]<<" depth5="<<depthHistogram[5]<<"\n";
 if(cycles==0){
   if(maxFollow13!=5||maxPostEvents!=40||maxPostElapsed!=222||maxPostGrowth!=1406||depthHistogram[0]!=2216514)throw runtime_error("q13 finite certificate regression");
   cout<<"Q13_UNIVERSAL_CONSEQUENCE total13<=6 totalEvents<="<<23+maxPostEvents
     <<" totalElapsed<="<<159+maxPostElapsed
     <<" totalGrowth<="<<1156+15014+maxPostGrowth<<"\n";
 }else {int a=-1;for(int i=0;i<N;i++)if(degree[i]>0){a=i;break;}if(a>=0){cout<<"CYCLE_NODE t="<<timeValue[a/1155]<<" c="<<(timeValue[a/1155]%2?24:0)+26*(a%1155)<<"\n";}}
}
