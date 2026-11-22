// Original parity-clipped squarefree GCD: shifted canonical-source correlations
// decomposed into common future RESET nodes and disjoint histories.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror reset_shift_pair_audit.cpp -o /tmp/shift_audit
// /tmp/shift_audit 4096 16384 65536 262144
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#define main reset_origin_dispersion_embedded_main
#include "reset_origin_dispersion_audit.cpp"
#undef main
#pragma GCC diagnostic pop
#include <complex>
#include <fstream>
#include <array>

static int band_index(int q,int B){
 if(q*4<B)return 0;
 if(q*2<B)return 1;
 return 2;
}
struct ShiftNode {int t,z;int width;ll h=0;array<ll,3> b{{0,0,0}};};
struct StartPath {vector<int> nodes;ll load=0;array<ll,3> b{{0,0,0}};};
static bool intersects(const vector<int>&a,const vector<int>&b){
 size_t i=0,j=0;
 while(i<a.size()&&j<b.size()){
   if(a[i]==b[j])return true;
   if(a[i]<b[j])++i;else ++j;
 }
 return false;
}
static void run_pairs(int X,const string&csvPrefix){
 const int B=int(ceill(sqrtl(7.L*X))), N=X/2;
 qs.clear();for(int q=103;q<=B;q+=2)if(spf[q]==q)qs.push_back(q);
 Stat stat;auto records=collect(X,B,stat);
 vector<vector<int>> pref(2*L);
 vector<int> widths(2*L);
 for(int z:{0,6})for(int r=0;r<L;r++){
   int k=r+(z==6?L:0);pref[k]=low_prefix_growths(r,z);
   vector<int> all;
   for(int e:pref[k]){all.push_back(e-1);all.push_back(e+1);}
   sort(all.begin(),all.end());all.erase(unique(all.begin(),all.end()),all.end());
   widths[k]=int(all.size());
   if(widths[k]<2||widths[k]>31)throw runtime_error("width regression");
 }
 vector<ShiftNode> nodes;
 unordered_map<int,int> id;
 vector<StartPath> starts(N);
 vector<ll> visitCounts;
 for(const auto&r:records){
   int key=2*r.t+(r.z==6);
   auto it=id.find(key);
   if(it==id.end()){
     int c=r.t%L+(r.z==6?L:0);
     int j=int(nodes.size());id.emplace(key,j);
     nodes.push_back({r.t,r.z,widths[c]});visitCounts.push_back(0);it=id.find(key);
   }
   int j=(r.M-X-1)/2;
   if(j<0||j>=N)throw runtime_error("bad source index");
   starts[j].nodes.push_back(it->second);visitCounts[it->second]++;
 }
 for(int q:qs){
   vector<vector<int>> roots(2*L);vector<unsigned char> seen(2*L,0);
   int band=band_index(q,B);
   for(auto &node:nodes){
     int k=node.t%L+(node.z==6?L:0);
     if(!seen[k]){roots[k]=rootsets(node.z,pref[k],q);seen[k]=1;
       // Universal 55-residue confinement, independent of the adaptive history.
       const int center=(q+1)/2;
       for(int u:roots[k]){
         bool inUniversal=false;
         for(int shift=-51;shift<=3;shift++)
           if((center+shift%q+q)%q==u){inUniversal=true;break;}
         if(!inUniversal)throw runtime_error("universal q root interval violated");
       }
     }
     bool hit=binary_search(roots[k].begin(),roots[k].end(),node.t%q);
     const ll d=(hit?q:0)-node.width;
     node.h+=d;node.b[band]+=d;
   }
 }
 ll signedAll=0,seenVisits=0;
 for(auto &p:starts){
  for(int j:p.nodes){p.load+=nodes[j].h;
   for(int b=0;b<3;b++)p.b[b]+=nodes[j].b[b];
   seenVisits++;
  }
  signedAll+=p.load;
 }
 const struct {int X;ll s,e,g,r;} regressions[]={
  {4096,-10777,29349,399142,2865},
  {16384,-501858,171428,2915326,14422},
  {65536,-398293,795689,19826998,73941},
  {262144,194316,4082904,138903880,360413}
 };
 for(const auto&r:regressions)if(r.X==X && (signedAll!=r.s||stat.events!=r.e||stat.growth!=r.g||stat.reset!=r.r))
   throw runtime_error("historical original GCD regression mismatch");
 if(seenVisits!=stat.reset)throw runtime_error("reset visit mismatch");
 // Source pathways must be sorted by absolute time, and intersecting pathways
 // have common suffix until the earlier source exits (deterministic forward map).
 for(auto &p:starts){
   sort(p.nodes.begin(),p.nodes.end(),[&](int a,int b){return nodes[a].t<nodes[b].t;});
   for(size_t i=1;i<p.nodes.size();i++)if(nodes[p.nodes[i-1]].t>=nodes[p.nodes[i]].t)
     throw runtime_error("time not strictly increasing");
 }
// A pair of reset q-candidate nodes can only differ by up to 54 (mod q).
 // Check this for sampled pairs of FIRST reset nodes at all studied source shifts.
 std::vector<std::vector<uint64_t>> candidateMasks(nodes.size(),vector<uint64_t>((qs.size()+63)/64,0));
 for(size_t qi=0;qi<qs.size();qi++){
   int q=qs[qi];vector<vector<int>> roots(2*L);vector<unsigned char> seen(2*L,0);
   for(size_t ni=0;ni<nodes.size();ni++){
     const auto&node=nodes[ni];int k=node.t%L+(node.z==6?L:0);
     if(!seen[k]){roots[k]=rootsets(node.z,pref[k],q);seen[k]=1;}
     if(binary_search(roots[k].begin(),roots[k].end(),node.t%q))
       candidateMasks[ni][qi/64]|=uint64_t(1)<<(qi%64);
   }
 }
 const long double mean=static_cast<long double>(signedAll)/N;
 long double variance=0,bandVar[3]={},bandSigned[3]={};
 ll collisionEnergy=0;
 for(ll m:visitCounts)collisionEnergy+=m*m;
 long double M4=0,M2=0;
 for(const auto&p:starts){const long double x=p.load;M2+=x*x;M4+=x*x*x*x;}
 cout<<fixed<<setprecision(8)<<"PAIR_MOMENTS X="<<X<<" B="<<B
    <<" resetCollisionEnergy="<<collisionEnergy
    <<" collisionOverXB="<<double(collisionEnergy/(static_cast<long double>(X)*B))
    <<" fourthOverXB4="<<double(M4/(X*powl(static_cast<long double>(B),4)))
    <<" secondOverXB2="<<double(M2/(static_cast<long double>(X)*B*B))<<"\n";
 for(int h : {B,int(powl((long double)B,1.25L)),int(powl((long double)B,1.5L))}){
    const int H=min(N,max(1,h));
    long double rolling=0,Q=0;
    for(int k=0;k<N+H-1;k++){
     if(k<N)rolling+=starts[k].load;
     if(k>=H)rolling-=starts[k-H].load;
     Q+=rolling*rolling;
    }
    const long double vdC=sqrtl((N+H-1)*Q)/H;
    if((signedAll*static_cast<long double>(signedAll))>vdC*vdC+10)
      throw runtime_error("block-scale Fejer inequality regression");
    cout<<"PAIR_WINDOW X="<<X<<" H="<<H<<" scaledMeanBound="<<double(vdC/(X*static_cast<long double>(B)))
     <<" scaledBlockEnergy="<<double(Q/(X*powl((long double)B,2)*H*H))<<"\n";
 }
 
 for(auto &p:starts){variance+=(p.load-mean)*(p.load-mean);
  for(int b=0;b<3;b++){bandSigned[b]+=p.b[b];bandVar[b]+=static_cast<long double>(p.b[b])*p.b[b];}}
 cout<<fixed<<setprecision(8)<<"SHIFTPAIR_PASS X="<<X<<" B="<<B<<" N="<<N<<" resets="<<stat.reset<<" states="<<nodes.size()<<" signed="<<signedAll<<" mean="<<double(mean)<<" centeredRms="<<double(sqrtl(variance/N))
  <<" bandSum="<<double(bandSigned[0])<<","<<double(bandSigned[1])<<","<<double(bandSigned[2])<<"\n";
 for(int ell:{1,2,3,4,5,8,16,24,32,48,64,96,128,192,256,384,512,768,1024,1154,1155,1156,1536,2048,4096,B}){
  if(ell>=N)continue;
  long double total=0,center=0,merged=0,disjoint=0,mergC=0,disC=0,weightedL2=0;
  ll mergedCount=0,disCount=0,pairedFirstQ=0,pairedFirstQDisjoint=0,firstNodePairs=0;
  long double bands[3][3]={{}};
  for(int j=0;j+ell<N;j++){
   const auto&a=starts[j], &b=starts[j+ell];
   long double u=a.load,w=b.load;
   bool shared=intersects(a.nodes,b.nodes);
   total+=u*w;center+=(u-mean)*(w-mean);
   if(!a.nodes.empty()&&!b.nodes.empty()){
     firstNodePairs++;
     int na=a.nodes.front(),nb=b.nodes.front();
     for(size_t wd=0;wd<candidateMasks[na].size();wd++){
       uint64_t bits=candidateMasks[na][wd] & candidateMasks[nb][wd];
       while(bits){unsigned bit=__builtin_ctzll(bits);size_t qi=wd*64+bit;
         bits&=bits-1;
         if(qi>=qs.size())throw runtime_error("bit mask bad index");
         int q=qs[qi];int delta=(nodes[nb].t-nodes[na].t)%q;
         if(delta<0)delta+=q;
         if(delta>54&&delta<q-54)throw runtime_error("q-shared CRT candidate short shift exclusion failed");
         pairedFirstQ++;
         if(!shared)pairedFirstQDisjoint++;
       }
     }
   }
   if(shared){merged+=u*w;mergC+=(u-mean)*(w-mean);mergedCount++;}
   else{disjoint+=u*w;disC+=(u-mean)*(w-mean);disCount++;}
   weightedL2+=(u-mean)*(u-mean)+(w-mean)*(w-mean);
   for(int x=0;x<3;x++)for(int y=0;y<3;y++)bands[x][y]+=static_cast<long double>(a.b[x])*b.b[y];
  }
  if(mergedCount+disCount!=N-ell || fabsl(merged+disjoint-total)>0.01L ||fabsl(mergC+disC-center)>0.01L)
   throw runtime_error("pair partition mismatch");
  cout<<"SHIFT_PAIR X="<<X<<" ell="<<ell<<" n="<<N-ell
    <<" shareCount="<<mergedCount<<" shareRate="<<double(mergedCount/static_cast<long double>(N-ell))
    <<" rawMeanPair="<<double(total/(N-ell))
    <<" centeredPair="<<double(center/(N-ell))
    <<" rawMerged="<<double(merged/(N-ell))
    <<" rawDisjoint="<<double(disjoint/(N-ell))
    <<" centerMerged="<<double(mergC/(N-ell))
    <<" centerDisjoint="<<double(disC/(N-ell))
    <<" ccNorm="<<double(2*center/weightedL2)
    <<" firstResetPairQ="<<pairedFirstQ<<" firstResetPairQDisjoint="<<pairedFirstQDisjoint<<" firstResetPairs="<<firstNodePairs
    <<" diagBand00="<<double(bands[0][0]/(N-ell))
    <<" diagBand11="<<double(bands[1][1]/(N-ell))
    <<" diagBand22="<<double(bands[2][2]/(N-ell))
    <<"\n";
 }
 if(!csvPrefix.empty()){
  ofstream out(csvPrefix+"_X"+to_string(X)+".csv");out<<"M,source_load,lower_prime_band,middle_prime_band,upper_prime_band,reset_count,first_reset,last_reset\n";
  for(int j=0;j<N;j++){
   const auto&p=starts[j];
   out<<X+1+2*j<<","<<p.load<<","<<p.b[0]<<","<<p.b[1]<<","<<p.b[2]<<","<<p.nodes.size()<<","<<(p.nodes.empty()?-1:nodes[p.nodes.front()].t)<<","<<(p.nodes.empty()?-1:nodes[p.nodes.back()].t)<<"\n";
  }
  if(!out)throw runtime_error("csv write error");
 }
}
int main(int argc,char **argv){
 if(argc<2)return 2;
 int mx=0;vector<int>xs;string prefix;
 for(int i=1;i<argc;i++){
  string s=argv[i];
  if(s.rfind("--csv=",0)==0){prefix=s.substr(6);continue;}
  int X=stoi(s);if(X<2048||(X&1)||X>524288)return 2;mx=max(mx,X);xs.push_back(X);
 }
 if(!mx)return 2;
 setup(mx);
 for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=event_growth(M,41))throw runtime_error("independent original-GCD literal regression");
 for(int X:xs)run_pairs(X,prefix);
}
