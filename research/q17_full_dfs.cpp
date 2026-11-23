// Full q17 post-event graph cycle check in O(N) transitions, O(N) bytes (not O(N) edges).
// q13 regression also works. Uses exact original parity-based squarefree clipped GCD.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror q17_full_dfs.cpp -o q17_full
// ./q17_full 17
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
static constexpr array<int,7> primes={3,5,7,11,13,17,19};
static int gap(int t,int p,int r){int v=(r-t)%(2*p);if(v<=0)v+=2*p;return v;}
struct Result{int next,events,elapsed,lowGrowth,increment;};
struct Graph{
 int q,P,L,N,perTime,halfC;vector<int>times,tindex;
 explicit Graph(int qq):q(qq),P(1){for(int p:primes){if(p>q)break;P*=p;}L=2*P;perTime=2*(P/q);halfC=P/q;N=perTime*halfC;
  tindex.assign(L,-1);
  for(int t=0;t<L;t++)if((t%2==0&&t%q==0)||(t%2==1&&(t-2+q)%q==0)){tindex[t]=int(times.size());times.push_back(t);}
  if(int(times.size())!=perTime)throw runtime_error("q-time classes differ");
 }
 Result next(int id)const{
  int ti=id/halfC,j=id%halfC,tmod=times[ti],cmod=2*((tmod%2?q-1:0)+q*j),t=tmod+5*L,c=cmod+5*L;
  int initialT=t,steps=0,lowGrowth=0;
  for(int k=0;k<80;k++){
   int dt=numeric_limits<int>::max(),d=1;
   for(int p:primes){if(p>q)break;int r=-1;
    if((c-1)%p==0)r=0;else if((c+1)%p==0)r=p+2;
    if(r<0)continue;
    const int dg=gap(t,p,r);
    if(dg<dt){dt=dg;d=p;}else if(dg==dt)d*=p;
   }
   if(dt==numeric_limits<int>::max())return {-1,steps,t-initialT,lowGrowth,0};
   t+=dt;c+=d-1;steps++;
   if(d%q==0){int tm=t%L,cm=c%L,ti2=tindex[tm],k0=(tm%2?q-1:0);
    if(ti2<0||cm%2||(cm/2-k0)<0||(cm/2-k0)%q)throw runtime_error("q post invalid");
    int other=ti2*halfC+(cm/2-k0)/q;
    if(other<0||other>=N)throw runtime_error("out-of-bounds successor");
    return {other,steps,t-initialT,lowGrowth,d};
   }
   lowGrowth+=d-1;
  }
  throw runtime_error("base-low segment exceeded80 events");
 }
};
struct Node{uint32_t id;Result edge;};
struct Checkpoint {uint32_t magic,q,N,nextRoot;uint64_t terminal,edges,totalProcessed,cycles;int32_t maxD,maxId,maxWait,maxLowGrowth,maxSteps,maxIncrement;uint64_t hist[64];};

int main(int argc,char**argv){if(argc<2)return 2;int q=atoi(argv[1]);Graph g(q);
 const int stop=(argc>=3?atoi(argv[2]):g.N);
 if(stop<1||stop>g.N)throw runtime_error("invalid checkpoint stop");
 const char* checkpointFile=(argc>=4?argv[3]:nullptr);

  vector<uint8_t> status(g.N,0),depth(g.N,0);
  vector<Node>path;path.reserve(128);
  uint64_t terminal=0,edges=0,totalProcessed=0,cycles=0;int maxD=0,maxId=-1,maxWait=0,maxLowGrowth=0,maxSteps=0,maxIncrement=0;
  array<uint64_t,64>hist{};int startRoot=0;
  if(checkpointFile){FILE* f=fopen(checkpointFile,"rb");if(f){Checkpoint ck{};
    if(fread(&ck,sizeof(ck),1,f)!=1||ck.magic!=0xA1669417||ck.q!=uint32_t(q)||ck.N!=uint32_t(g.N))throw runtime_error("checkpoint header invalid");
    if(fread(status.data(),status.size(),1,f)!=1||fread(depth.data(),depth.size(),1,f)!=1)throw runtime_error("checkpoint body invalid");
    fclose(f);startRoot=int(ck.nextRoot);terminal=ck.terminal;edges=ck.edges;totalProcessed=ck.totalProcessed;cycles=ck.cycles;
    maxD=ck.maxD;maxId=ck.maxId;maxWait=ck.maxWait;maxLowGrowth=ck.maxLowGrowth;maxSteps=ck.maxSteps;maxIncrement=ck.maxIncrement;
    copy(begin(ck.hist),end(ck.hist),hist.begin());
    cerr<<"CHECKPOINT_RESTORED q="<<q<<" nextRoot="<<startRoot<<" finished="<<totalProcessed<<"\n";
  }}
  cerr<<"FULL_START q="<<q<<" states="<<g.N<<" bytes="<<2ULL*g.N<<"\n";
  for(int root=startRoot;root<stop;root++){
   if(status[root])continue;
   int x=root,downstream=-1;path.clear();
   while(x>=0 && status[x]==0){
    status[x]=1;Result a=g.next(x);
    if(a.next<0)terminal++;else edges++;
    maxWait=max(maxWait,a.elapsed);maxLowGrowth=max(maxLowGrowth,a.lowGrowth);maxSteps=max(maxSteps,a.events);maxIncrement=max(maxIncrement,a.increment);
    path.push_back({uint32_t(x),a});x=a.next;
   }
   if(x>=0&&status[x]==1){
    cycles++;cerr<<"CYCLE_WITNESS q="<<q<<" node="<<x<<" root="<<root<<" pathLen="<<path.size()<<"\n";
    for(const auto& k:path)if(k.id==unsigned(x)){cerr<<"CYCLE_REACHES "<<k.id<<"\n";break;}
    return 3;
   }
   if(x>=0&&status[x]==2)downstream=depth[x];
   for(auto it=path.rbegin();it!=path.rend();++it){
     if(it->edge.next<0)downstream=0;
     else downstream++;
     if(downstream>=int(hist.size()))throw runtime_error("unexpected >63 q-return chain");
     depth[it->id]=uint8_t(downstream);status[it->id]=2;
     hist[downstream]++;if(downstream>maxD){maxD=downstream;maxId=int(it->id);}
   }
   totalProcessed+=path.size();
   if((root%30000000)==0&&root>0){cerr<<"PROGRESS q="<<q<<" scanned="<<root<<" finished="<<totalProcessed<<" maxDepth="<<maxD<<"\n";}
  }
  if(stop<g.N){
    if(!checkpointFile)throw runtime_error("need checkpoint path for partial scan");
    Checkpoint ck{};ck.magic=0xA1669417;ck.q=q;ck.N=g.N;ck.nextRoot=stop;ck.terminal=terminal;ck.edges=edges;ck.totalProcessed=totalProcessed;ck.cycles=cycles;
    ck.maxD=maxD;ck.maxId=maxId;ck.maxWait=maxWait;ck.maxLowGrowth=maxLowGrowth;ck.maxSteps=maxSteps;ck.maxIncrement=maxIncrement;
    copy(hist.begin(),hist.end(),begin(ck.hist));
    FILE* f=fopen(checkpointFile,"wb");if(!f)throw runtime_error("unable to open checkpoint for write");
    if(fwrite(&ck,sizeof(ck),1,f)!=1||fwrite(status.data(),status.size(),1,f)!=1||fwrite(depth.data(),depth.size(),1,f)!=1)throw runtime_error("checkpoint write failed");
    if(fclose(f)!=0)throw runtime_error("checkpoint close failure");
    cout<<"CHECKPOINT_SAVED q="<<q<<" nextRoot="<<stop<<" finished="<<totalProcessed<<" terminal="<<terminal<<" edges="<<edges<<" maxDepth="<<maxD<<"\n";
    return 0;
  }
  if(totalProcessed!=uint64_t(g.N)||edges+terminal!=uint64_t(g.N)||cycles)throw runtime_error("full exhaustiveness discrepancy");
  cout<<"FULL_Q_RENEWAL_PASS q="<<q<<" nodes="<<g.N<<" edges="<<edges<<" terminal="<<terminal<<" cycleNodes=0 maxDepth="<<maxD<<" maxDepthNode="<<maxId<<" maxStageEvents="<<maxSteps<<" maxStageWait="<<maxWait<<" maxStageLowGrowth="<<maxLowGrowth<<" maxStageIncrement="<<maxIncrement;
  for(int i=0;i<=maxD;i++){cout<<" hist"<<i<<"="<<hist[i];}cout<<"\n";
  if(q==13&&(terminal!=2216514||maxD!=5))throw runtime_error("q13 regression mismatch");
}
