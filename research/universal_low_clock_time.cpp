// Exhaustive 2,668,050-state low-wheel time-span certificate.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr int P=1155,L=2310,N=L*P;
constexpr array<int,4> primes={3,5,7,11};
int gap(int t,int q,int r){int x=(r-t)%(2*q);if(x<=0)x+=2*q;return x;}
int main(){
 vector<int> next(N,-1),steps(N,0),d(N,0),in(N,0);
 int sinks=0;
 for(int t=0;t<L;t++)for(int half=0;half<P;half++){
  int c=2*half,idx=t*P+half,dt=INT32_MAX,prod=1;
  for(int q:primes){int r=-1;
    if((c-1)%q==0)r=0;
    else if((c+1)%q==0)r=q+2;
    if(r<0)continue;
    int z=gap(t,q,r);
    if(z<dt){dt=z;prod=q;}else if(z==dt)prod*=q;
  }
  if(dt==INT32_MAX){sinks++;continue;}
  int j=((t+dt)%L)*P+((c+prod-1)%L)/2;
  next[idx]=j;steps[idx]=dt;d[idx]=prod-1;in[j]++;
 }
 vector<int>order;order.reserve(N);
 for(int i=0;i<N;i++)if(in[i]==0)order.push_back(i);
 for(size_t k=0;k<order.size();k++)if(next[order[k]]>=0&&--in[next[order[k]]]==0)order.push_back(next[order[k]]);
 if(int(order.size())!=N)throw runtime_error("low-wheel directed cycle");
 vector<int>event(N),growth(N),elapsed(N),gainActive(N),gainAny(N);
 int me=0,mg=0,mt=0,ma=0,ms=0;int idxE=-1,idxG=-1,idxT=-1,idxA=-1,idxS=-1;
 for(int k=N-1;k>=0;k--){int x=order[k],j=next[x];if(j>=0){event[x]=1+event[j];growth[x]=d[x]+growth[j];elapsed[x]=steps[x]+elapsed[j];
    int w=2*steps[x]-d[x];
    gainAny[x]=max(0,w+gainAny[j]);
    gainActive[x]=max(0,w+gainActive[j]);
    if(next[j]<0)gainActive[x]=0;
   }
  if(event[x]>me){me=event[x];idxE=x;}
  if(growth[x]>mg){mg=growth[x];idxG=x;}
  if(elapsed[x]>mt){mt=elapsed[x];idxT=x;}
  if(gainActive[x]>ma){ma=gainActive[x];idxA=x;}
  if(gainAny[x]>ms){ms=gainAny[x];idxS=x;}
 }
 cout<<"ALL_LOW states="<<N<<" sinks="<<sinks<<" maxEvents="<<me<<" maxGrowth="<<mg<<" maxElapsed="<<mt<<" at="<<idxT/P<<","<<2*(idxT%P)<<" maxGainActive="<<ma<<" atActive="<<idxA/P<<","<<2*(idxA%P)<<" maxGainAny="<<ms<<" atAny="<<idxS/P<<","<<2*(idxS%P)<<" indices="<<idxE<<","<<idxG<<"\n";
 if(me!=22||mg!=1156||mt!=133||ma!=172||ms!=192||sinks!=311850)
  throw runtime_error("exhaustive finite-wheel regression mismatch");
}
