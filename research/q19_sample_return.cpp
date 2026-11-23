// Exploratory q19 next-return sampler; NOT an exhaustive q19 certificate.
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
using namespace std;
using u64=uint64_t;
static constexpr array<int,7>ps={3,5,7,11,13,17,19};
int gap(int t,int p,int r){int v=(r-t)%(2*p);if(v<=0)v+=2*p;return v;}
struct Graph{
 int P=1,L=0,q=19,perTime=0,half=0;u64 N=0;vector<int>time,tindex;
 Graph(){for(int p:ps)P*=p;L=2*P;half=P/q;perTime=2*half;N=u64(perTime)*half;
  tindex.assign(L,-1);time.reserve(perTime);
  for(int t=0;t<L;t++)if((t%2==0&&t%q==0)||(t%2==1&&(t-2+q)%q==0)){tindex[t]=int(time.size());time.push_back(t);}
  if(int(time.size())!=perTime||N!=130310230050ULL)throw runtime_error("q19 geometry mismatch");}
 u64 next(u64 id){u64 ti=id/half;int j=int(id%half);int r=time[ti];int t=r+3*L,c=2*((r%2?q-1:0)+q*j)+3*L;
  for(int k=0;k<160;k++){
   int dt=numeric_limits<int>::max(),d=1;
   for(int p:ps){int side=-1;if((c-1)%p==0)side=0;else if((c+1)%p==0)side=p+2;if(side<0)continue;
    int w=gap(t,p,side);if(w<dt){dt=w;d=p;}else if(w==dt)d*=p;
   }
   if(dt==numeric_limits<int>::max())return UINT64_MAX;
   t+=dt;c+=d-1;
   if(d%q==0){int tm=t%L,cm=c%L,index=tindex[tm],k0=tm%2?q-1:0;
    if(index<0||cm%2||(cm/2-k0)<0||(cm/2-k0)%q)throw runtime_error("q post invalid");
    u64 ret=u64(index)*half+(cm/2-k0)/q;
    if(ret>=N)throw runtime_error("next state out of range");
    return ret;
   }
  }
  throw runtime_error("lower prime trajectory exceeded160 events");
 }
};
int main(int argc,char**argv){int n=argc>1?atoi(argv[1]):1000000;Graph g;mt19937_64 gen(20261123);uniform_int_distribution<u64>dis(0,g.N-1);
 u64 no=0,returns=0,seenCycles=0;int maxDepth=0;array<u64,32>hist{};
 for(int i=0;i<n;i++){
  u64 x=dis(gen);u64 y=g.next(x);returns+=(y!=UINT64_MAX);no+=(y==UINT64_MAX);
  int depth=0;unordered_map<u64,int>visited;
  while(y!=UINT64_MAX){if(visited.count(y)){seenCycles++;break;}visited[y]=depth++;if(depth>30)throw runtime_error("unexpected deep q19 path");y=g.next(y);}
  if(seenCycles)break;
  maxDepth=max(maxDepth,depth);hist[depth]++;
 }
 cout<<"Q19_SAMPLE_ONLY states="<<g.N<<" sampled="<<n<<" immediateReturns="<<returns<<" terminal="<<no<<" maxQ19ReturnDepth="<<maxDepth<<" witnessedCycles="<<seenCycles;
 for(int i=0;i<=maxDepth;i++){cout<<" depth"<<i<<"="<<hist[i];}cout<<"\n";
}
