// A166944 research: scalar centered divisor load on merged reset states;
// exact split of reset-origin CRT discrepancies into
// unweighted STATE-SUPPORT bias and state-MULTIPLICITY bias.
// Requires original sibling research/reset_origin_dispersion_audit.cpp.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror reset_coalescence_variance_audit.cpp -o audit
// ./audit 4096 16384 65536 262144 500000
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#define main prior_dispersion_audit_entry
#include "reset_origin_dispersion_audit.cpp"
#undef main
#pragma GCC diagnostic pop
#include <unordered_set>
#include <limits>
struct Node { int t,z,depth; int n=0; };
static void coalescence_X(int X) {
 const int B=int(ceill(sqrtl(7.L*X)));
 qs.clear();for(int q=103;q<=B;q+=2)if(spf[q]==q)qs.push_back(q);
 Stat st;const vector<Record> recs=collect(X,B,st);
 unordered_map<int,int> pos;pos.reserve(recs.size());vector<Node> nodes;
 for(const auto&r:recs){int id=r.t*2+(r.z==6);auto it=pos.find(id);
  if(it==pos.end()){pos.emplace(id,int(nodes.size()));nodes.push_back({r.t,r.z,r.depth,1});}
  else nodes.at(it->second).n++;
 }
 const ll R=ll(recs.size()),V=ll(nodes.size());if(!R||!V)throw runtime_error("empty reset population");
 const struct {int X;ll high,reset,events,growth;} regressions[] = {
   {4096,7675,2865,29349,399142},
   {16384,45343,14422,171428,2915326},
   {65536,224221,73941,795689,19826998},
   {262144,1198498,360413,4082904,138903880}
 };
 for(const auto& e:regressions)if(X==e.X &&
    (st.high!=e.high||st.reset!=e.reset||st.events!=e.events||st.growth!=e.growth))
   throw runtime_error("full original wheel growth/reset historical regression failed");
 vector<vector<int>> prefixes(2*L),stableWidths(2*L);
 for(int z:{0,6})for(int r=0;r<L;r++){
  int cell=r+(z==6?L:0);prefixes[cell]=low_prefix_growths(r,z);
  for(int e:prefixes[cell]){stableWidths[cell].push_back(e-1);stableWidths[cell].push_back(e+1);}
  auto&x=stableWidths[cell];sort(x.begin(),x.end());x.erase(unique(x.begin(),x.end()),x.end());
  if(x.empty()||x.size()>31)throw runtime_error("stable width checkpoint failed");
 }
 const long double mean=static_cast<long double>(R)/V;
 long double collision=0,centered=0;vector<int> ms;
 for(const auto&v:nodes){collision+=static_cast<long double>(v.n)*v.n;
  centered+=(v.n-mean)*(v.n-mean);ms.push_back(v.n);
 }
 sort(ms.rbegin(),ms.rend());ll top1=0;for(int j=0;j<max(1,int(V/100));j++)top1+=ms[j];
 long double weightedObs=0,weightedPhase=0,uniqueObs=0,uniquePhase=0;
 long double absWeighted=0,absUniqueScaled=0,absMultiplicity=0,signedWeighted=0,signedUnique=0,signedMultiplicity=0;
 long double squaredRaw=0,squaredUnique=0,squaredMult=0;
 ll discrepancyChecks=0;int maxUniqueRatioQ=0;
 long double maxUniqueRatio=0;
 for(int q:qs){
  vector<vector<int>> roots(2*L);vector<unsigned char> init(2*L,0);
  ll A=0,a=0,weightedWidth=0,uniqueWidth=0;
  for(const Node&v:nodes){int cell=v.t%L+(v.z==6?L:0);
    if(!init[cell]){roots[cell]=rootsets(v.z,prefixes[cell],q);init[cell]=1;
     if(roots[cell].size()!=stableWidths[cell].size())throw runtime_error("q>=103 width mismatch");}
    bool hit=binary_search(roots[cell].begin(),roots[cell].end(),v.t%q);
    if(hit){A+=v.n;a++;}
    weightedWidth+=ll(roots[cell].size())*v.n;
    uniqueWidth+=ll(roots[cell].size());
  }
  const long double expected=static_cast<long double>(weightedWidth)/q;
  const long double expectedUnique=static_cast<long double>(uniqueWidth)/q;
  const long double delta=static_cast<long double>(A)-expected;
  const long double uniqdelta=static_cast<long double>(a)-expectedUnique;
  const long double md=delta-mean*uniqdelta;
  // Exact decomposition: A-mu_width/q = mean*(a-width/q) + covariance term.
  const long double independentCheck=mean*uniqdelta+md;
  if(fabsl(independentCheck-delta)>1e-9L)throw runtime_error("coalescence decomposition discrepancy");
  discrepancyChecks++;
  weightedObs+=q*A;weightedPhase+=q*expected;
  uniqueObs+=q*a;uniquePhase+=q*expectedUnique;
  absWeighted+=q*fabsl(delta);absUniqueScaled+=q*fabsl(mean*uniqdelta);absMultiplicity+=q*fabsl(md);
  signedWeighted+=q*delta;signedUnique+=q*mean*uniqdelta;signedMultiplicity+=q*md;
  squaredRaw+=q*q*delta*delta;squaredUnique+=q*q*mean*mean*uniqdelta*uniqdelta;
  squaredMult+=q*q*md*md;
  if(expectedUnique>=25){long double r=a/expectedUnique;
    if(r>maxUniqueRatio){maxUniqueRatio=r;maxUniqueRatioQ=q;}}
 }
 if(fabsl(signedWeighted-signedUnique-signedMultiplicity)>0.01L)throw runtime_error("global exact decomposition failure");
 cout<<fixed<<setprecision(7)<<"COALESCE_PASS X="<<X<<" B="<<B<<" resetVisits="<<R<<" nodes="<<V
  <<" avgMultiplicity="<<double(mean)<<" top1PctVisitsShare="<<double(top1)/R
  <<" collisionEnergy="<<double(collision)<<" centeredEnergy="<<double(centered)
  <<" maxMultiplicity="<<ms.front()<<" qChecks="<<discrepancyChecks
  <<" weightedCandidate="<<double(weightedObs)<<" weightedPhase="<<double(weightedPhase)
  <<" weightedSignedOverPhase="<<double(signedWeighted/weightedPhase)
  <<" weightedAbsOverPhase="<<double(absWeighted/weightedPhase)
  <<" uniqueCandidate="<<double(uniqueObs)<<" uniquePhase="<<double(uniquePhase)
  <<" uniqueSignedOverPhase="<<double((uniqueObs-uniquePhase)/uniquePhase)
  <<" uniqueAbsOverPhase="<<double((absUniqueScaled/mean)/uniquePhase)
  <<" supportTermAbsOverWeightedPhase="<<double(absUniqueScaled/weightedPhase)
  <<" multiplicityTermAbsOverWeightedPhase="<<double(absMultiplicity/weightedPhase)
  <<" weightedL2Sq="<<double(squaredRaw)<<" supportL2Sq="<<double(squaredUnique)
  <<" multiplicityL2Sq="<<double(squaredMult)
  <<" maxDistinctNodeQRatio="<<double(maxUniqueRatio)<<" maxRatioQ="<<maxUniqueRatioQ<<"\n";
 // Coalescence-compatible scalar observable H_B(t,z): one summed high-prime load.
 // Rather than separate q-wise absolute discrepancies, measure cancellation
 // after summing q at EVERY reset state. Weighted paths matter.
 vector<ll> scalar(nodes.size(),0);
 for(int q:qs){
   vector<vector<int>> roots(2*L);vector<uint8_t> init(2*L,0);
   for(size_t j=0;j<nodes.size();j++){
    const Node&v=nodes[j];const int cell=v.t%L+(v.z==6?L:0);
    if(!init[cell]){roots[cell]=rootsets(v.z,prefixes[cell],q);init[cell]=1;}
    if(binary_search(roots[cell].begin(),roots[cell].end(),v.t%q))scalar[j]+=q;
   }
 }
 long double weightedScalarAbsolute=0,unweightedScalarAbsolute=0,varianceWeighted=0,positiveMass=0,negativeMass=0;
 ll weightedScalarSigned=0,unweightedScalarSigned=0;
 vector<long double> loads(nodes.size());
 for(size_t j=0;j<nodes.size();j++){
   const Node&v=nodes[j];const int cell=v.t%L+(v.z==6?L:0);
   const int w=int(stableWidths[cell].size());
   const ll h=scalar[j]-ll(qs.size())*w;
   loads[j]=h;
   weightedScalarAbsolute+=static_cast<long double>(v.n)*llabs(h);
   unweightedScalarAbsolute+=llabs(h);
   weightedScalarSigned+=v.n*h;
   unweightedScalarSigned+=h;
   varianceWeighted+=static_cast<long double>(v.n)*h*h;
   if(h>=0)positiveMass+=v.n*h;else negativeMass-=v.n*h;
 }
 if(fabsl(weightedScalarSigned-signedWeighted)>0.1L||fabsl(unweightedScalarSigned-(uniqueObs-uniquePhase))>0.1L)
   throw runtime_error("scalar transport q aggregation mismatch");
 unordered_map<int,int> predecessorToNext;predecessorToNext.reserve(nodes.size());
 ll edges=0;long double edgeCross=0,edgeLeft2=0,edgeRight2=0;
 for(const auto&r:recs)if(r.nextResetT){int a=r.t*2+(r.z==6),b=r.nextResetT*2+(r.nextResetZ==6);
  if(!predecessorToNext.count(a))predecessorToNext.emplace(a,b);
  else if(predecessorToNext.at(a)!=b)throw runtime_error("functional reset edge not unique");
 }
 unordered_map<int,int> indegree;indegree.reserve(nodes.size());
 for(const auto&[a,b]:predecessorToNext){indegree[b]++;auto i=pos.find(a),j=pos.find(b);
  if(i!=pos.end()&&j!=pos.end()){
    const ll m=nodes[i->second].n;
    edgeCross+=static_cast<long double>(m)*loads[i->second]*loads[j->second];
    edgeLeft2+=static_cast<long double>(m)*loads[i->second]*loads[i->second];
    edgeRight2+=static_cast<long double>(m)*loads[j->second]*loads[j->second];
    ++edges;
  }
 }
 vector<ll> sourceLoad(X/2,0);
 for(const auto&r:recs){int idx=(r.M-(X+1))/2;
    if(idx<0||idx>=X/2)throw runtime_error("source index out of range");
    int id=r.t*2+(r.z==6);
    auto it=pos.find(id);if(it==pos.end())throw runtime_error("reset state missing from source map");
    ll h=ll(loads[it->second]);
    sourceLoad[idx]+=h;
 }
 long double sourceAbs=0,sourceSq=0,positiveSource=0,negativeSource=0;
 ll nonzeroSources=0,maxSource=0,sourceTotal=0;
 for(size_t k=0;k<sourceLoad.size();++k){ll h=sourceLoad[k];sourceAbs+=llabs(h);
    sourceSq+=static_cast<long double>(h)*h;
    sourceTotal+=h;if(h>0)positiveSource+=h;else negativeSource-=h;
    if(h)++nonzeroSources;
    maxSource=max(maxSource,llabs(h));
 }
 if(sourceTotal!=weightedScalarSigned)throw runtime_error("source path telescope mismatch");
 ll multiIndegree=0,maxIndegree=0;
 for(const auto&[b,d]:indegree){if(d>1)multiIndegree++;maxIndegree=max(maxIndegree,ll(d));}
 cout<<fixed<<setprecision(8)<<"SCALAR_PASS X="<<X<<" B="<<B<<" visits="<<R<<" nodes="<<V
   <<" signedWeighted="<<weightedScalarSigned<<" signedOverPhase="<<double(weightedScalarSigned/weightedPhase)
   <<" absPerNodeWeighted="<<double(weightedScalarAbsolute)<<" absNodeOverPhase="<<double(weightedScalarAbsolute/weightedPhase)
   <<" scalarCancellation="<<double(fabsl(weightedScalarSigned)/weightedScalarAbsolute)
   <<" absUnweighted="<<double(unweightedScalarAbsolute)
   <<" signedUnweighted="<<unweightedScalarSigned
   <<" rootSecondMoment="<<double(varianceWeighted)
   <<" positiveMass="<<double(positiveMass)<<" negativeMass="<<double(negativeMass)
   <<" knownSuccessorStates="<<predecessorToNext.size()
   <<" distinctEdges="<<edges<<" nodesIndegreeGt1="<<multiIndegree<<" maxIndegree="<<maxIndegree
   <<" edgeSignCorrelation="<<double(edgeCross/sqrtl(edgeLeft2*edgeRight2))
   <<" sourcePathAbs="<<double(sourceAbs)
   <<" pathAbsOverNodeAbs="<<double(sourceAbs/weightedScalarAbsolute)
   <<" acrossSourcesCancellation="<<double(fabsl(sourceTotal)/sourceAbs)
   <<" pathRms="<<double(sqrtl(sourceSq/(X/2)))
   <<" maxPathAbs="<<maxSource
   <<" nonzeroSourcePaths="<<nonzeroSources
   <<" sourcePositiveSum="<<double(positiveSource)
   <<" sourceNegativeSum="<<double(negativeSource)<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;vector<int>xs;int mx=0;
 for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||(X&1)||X>524288)return 2;xs.push_back(X);mx=max(mx,X);}
 setup(mx);
 for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=event_growth(M,41))throw runtime_error("literal parity-GCD mismatch");
 for(int X:xs)coalescence_X(X);
}
