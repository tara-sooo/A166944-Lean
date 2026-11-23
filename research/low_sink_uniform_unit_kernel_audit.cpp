// Finite kernel: sink C residue -> prime-unit (odd d mod 2310) pulse -> low-only retraction.
// THIS IS AN ARTIFICIAL UNIFORM-UNIT RESIDUE MARKOV KERNEL, NOT THE TRUE ADAPTIVE GCD.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
static constexpr int P=1155,L=2310,N=P,ROWS=135,UNITS=480;
int gap(int t,int q,int r){int d=(r-t)%(2*q);if(d<=0)d+=2*q;return d;}
int low_terminal(int t0,int c0){int t=t0,c=c0,k=0;while(true){int dt=INT32_MAX,d=1;for(int q:{3,5,7,11}){int r=-1;if((c-1)%q==0)r=0;else if((c+1)%q==0)r=q+2;if(r<0)continue;int v=gap(t,q,r);if(v<dt){dt=v;d=q;}else if(v==dt)d*=q;}if(dt==INT32_MAX)return c;if(++k>22)throw runtime_error("low chain cap");t+=dt;c+=d-1;}}
int main(){vector<int> sink,units;for(int c=0;c<L;c+=2)if(gcd(c-1,P)==1&&gcd(c+1,P)==1)sink.push_back(c);for(int d=1;d<L;d+=2)if(gcd(d,P)==1)units.push_back(d);if(sink.size()!=ROWS||units.size()!=UNITS)throw runtime_error("dimension mismatch");
 long long directCount=0;int minDirectOverlap=ROWS,maxDirectOverlap=0;
 vector<vector<int>> direct(ROWS,vector<int>(ROWS,0));
 for(int a=0;a<ROWS;a++)for(int b=0;b<ROWS;b++)if(gcd((sink[b]-sink[a]+1+L)%L,P)==1){direct[a][b]=1;directCount++;}
 for(int a=0;a<ROWS;a++)for(int b=a+1;b<ROWS;b++){
   int overlap=0;for(int y=0;y<ROWS;y++)overlap+=direct[a][y]*direct[b][y];
   minDirectOverlap=min(minDirectOverlap,overlap);maxDirectOverlap=max(maxDirectOverlap,overlap);
 }
 cout<<"CRT_DIRECT_PASS sinkClasses="<<ROWS<<" unitResidues="<<UNITS
    <<" directInactivePairs="<<directCount
    <<" directInactiveProbability="<<double(directCount)/(ROWS*UNITS)
    <<" minimalCommonTerminalOutputs="<<minDirectOverlap
    <<" directDoeblinOverlap="<<double(minDirectOverlap)/UNITS
    <<" maxCommonTerminalOutputs="<<maxDirectOverlap<<"\n";
 if(directCount!=13024||minDirectOverlap!=42||maxDirectOverlap!=135)throw runtime_error("CRT direct values differ");
 for(int t0:{0,1,2,13,97,1840,2309}){
  vector<int> low(N);for(int i=0;i<N;i++){int c=2*i+10*L;low[i]=(low_terminal(t0+10*L,c))%L;}
  for(int i=0;i<N;i++){int y=low[i];if(low[y/2]!=y)throw runtime_error("Low terminal map not idempotent");}
  vector<vector<int>> row(ROWS,vector<int>(ROWS));int minsupport=ROWS,maxsupport=0,maxEntry=0,minEntry=UNITS,missingpairs=0,fullrows=0;
  for(int a=0;a<ROWS;a++)for(int d:units){int c1=(sink[a]+d-1)%L;int c2=low[c1/2];auto it=lower_bound(sink.begin(),sink.end(),c2);if(it==sink.end()||*it!=c2)throw runtime_error("terminal class error");row[a][it-sink.begin()]++;}
  for(int a=0;a<ROWS;a++){int support=0;for(int v:row[a]){if(v)++support;maxEntry=max(maxEntry,v);if(v)minEntry=min(minEntry,v);}minsupport=min(minsupport,support);maxsupport=max(maxsupport,support);if(support==ROWS)fullrows++;}
  int minOverlap=UNITS,maxOverlap=0;long long ovSum=0;int ovPairs=0;
  for(int a=0;a<ROWS;a++)for(int b=a+1;b<ROWS;b++){int overlap=0;for(int j=0;j<ROWS;j++)overlap+=min(row[a][j],row[b][j]);minOverlap=min(minOverlap,overlap);maxOverlap=max(maxOverlap,overlap);ovSum+=overlap;ovPairs++;if(overlap==0)missingpairs++;}
  if(missingpairs||minOverlap<minDirectOverlap)throw runtime_error("No overlap despite CRT theorem");
  cout<<"UNIFORM_UNIT_KERNEL_PASS tmod="<<t0<<" sinkClasses="<<ROWS<<" units="<<UNITS<<" minRowSupport="<<minsupport<<" maxRowSupport="<<maxsupport<<" fullRowSupport="<<fullrows<<" minPairOverlapCount="<<minOverlap<<" minPairOverlapFraction="<<setprecision(8)<<double(minOverlap)/UNITS<<" avgOverlap="<<double(ovSum)/ovPairs/UNITS<<" noOverlapPairs="<<missingpairs<<" maxEntry="<<maxEntry<<" minPositiveEntry="<<minEntry<<"\n";
 }
}
