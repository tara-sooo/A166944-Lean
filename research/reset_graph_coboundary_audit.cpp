// A166944: exact reset graph flow / coboundary / boundary-transport audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/reset_graph_coboundary_audit.cpp -o /tmp/reset_graph_coboundary_audit
// The sibling reset_origin_dispersion_audit.cpp is a mandatory dependency.
// ./audit 4096 16384 65536 262144 500000
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#define main reset_origin_dispersion_original_main
#include "reset_origin_dispersion_audit.cpp"
#undef main
#pragma GCC diagnostic pop
#include <unordered_set>
struct Vertex {
 int t,z,mu=0,first=0,through=0,dead=0,next=-1;
 ll h=0,pot=0;
};
static void run_flow(int X){
 const int B=int(ceill(sqrtl(7.L*X)));
 qs.clear();for(int q=103;q<=B;q+=2)if(spf[q]==q)qs.push_back(q);
 Stat stats;const vector<Record> recs=collect(X,B,stats);
 unordered_map<int,int> dict;dict.reserve(recs.size());vector<Vertex> v;v.reserve(recs.size());
 for(const auto& r:recs){
  const int key=r.t*2+(r.z==6);
  auto [it,ins]=dict.emplace(key,int(v.size()));
  if(ins)v.push_back({r.t,r.z});
  v[it->second].mu++;
 }
 if(v.empty())throw runtime_error("no reset records");
 const int V=int(v.size());
 vector<vector<int>> prefixes(2*L);vector<int> widths(2*L);
 for(int z:{0,6})for(int r=0;r<L;r++){
  const int cell=r+(z==6?L:0);prefixes[cell]=low_prefix_growths(r,z);
  vector<int> a;for(int e:prefixes[cell]){a.push_back(e-1);a.push_back(e+1);}
  sort(a.begin(),a.end());a.erase(unique(a.begin(),a.end()),a.end());widths[cell]=int(a.size());
  if(widths[cell]<2||widths[cell]>31)throw runtime_error("root width mismatch");
 }
 // h_B(v)=sum_q q*1{t modq in U_(q,r,z)}-pi_[103,B]*u(r,z).
 for(int i=0;i<V;i++)v[i].h=-ll(qs.size())*widths[v[i].t%L+(v[i].z==6?L:0)];
 for(int q:qs){
  vector<vector<int>> roots(2*L);vector<bool> seen(2*L,false);
  for(auto&x:v){int c=x.t%L+(x.z==6?L:0);
   if(!seen[c]){roots[c]=rootsets(x.z,prefixes[c],q);seen[c]=true;}
   if(binary_search(roots[c].begin(),roots[c].end(),x.t%q))x.h+=q;
  }
 }
 vector<int> firstIndex(X/2,-1),lastIndex(X/2,-1);
 // Exact observed forward map and observed real traffic (not the ungated full map).
 for(const auto&r:recs){
  const int u=dict.at(r.t*2+(r.z==6));
  const int j=(r.M-(X+1))/2;
  if(j<0||j>=X/2)throw runtime_error("source index invalid");
  if(firstIndex[j]<0){firstIndex[j]=u;v[u].first++;}
  if(lastIndex[j]>=0){const int prev=lastIndex[j];
   if(v[prev].next>=0&&v[prev].next!=u)throw runtime_error("same state successor conflict");
   v[prev].next=u;
   v[prev].through++;
  }
  lastIndex[j]=u;
  if(r.nextResetT){
   int key=r.nextResetT*2+(r.nextResetZ==6);
   auto it=dict.find(key);if(it==dict.end())throw runtime_error("missing named next reset");
   if(v[u].next>=0&&v[u].next!=it->second)throw runtime_error("record successor conflict");
   v[u].next=it->second;
  }
 }
 // Every source which does not continue to a NEXT reset terminates at its last visited reset.
 for(auto&x:v){x.dead=x.mu-x.through;
  if(x.dead<0)throw runtime_error("negative exit flow");
  if(x.through>0&&x.next<0)throw runtime_error("traffic to unknown successor");
 }
 ll firstTotal=0,deadTotal=0,massTotal=0,stepTotal=0,mixedCutoff=0;
 for(auto&x:v){firstTotal+=x.first;deadTotal+=x.dead;massTotal+=x.mu;stepTotal+=x.through;
  if(x.dead>0&&x.through>0)mixedCutoff++;}
 if(firstTotal!=deadTotal||massTotal!=(ll)recs.size()||massTotal-stepTotal!=deadTotal)throw runtime_error("flow conservation failed");
 // Verify node-by-node mass balance, incl. start injections and transported traffic.
 vector<ll> arrivals(V,0);
 for(int i=0;i<V;i++)if(v[i].next>=0)arrivals[v[i].next]+=v[i].through;
 for(int i=0;i<V;i++)if(v[i].mu!=arrivals[i]+v[i].first)throw runtime_error("local flow law fails");
 // Finite support graph is acyclic: reset time increases strictly at each successor.
 vector<int> order(V);iota(order.begin(),order.end(),0);
 sort(order.begin(),order.end(),[&](int a,int b){return v[a].t>v[b].t;});
 for(int i:order){const int j=v[i].next;
  if(j>=0&&v[j].t<=v[i].t)throw runtime_error("nonincreasing reset edge");
  v[i].pot=v[i].h+(j<0?0:v[j].pot);
 }
 // Solves exactly h(v)=G(v)-G(F(v));  G(sink)=0.  Note G has arithmetic content.
 ll S=0,birthBoundary=0,exitBoundary=0,sourceSum=0,weightedAbsolute=0;
 vector<ll> sourceSignal(X/2,0);
 long double perSourceAbs=0,perSourceRmsSq=0,birthAbs=0,exitAbs=0,potSq=0;
 ll maxPot=0,maxH=0;
 for(int i=0;i<V;i++){
  const auto&x=v[i];S+=ll(x.mu)*x.h;weightedAbsolute+=ll(x.mu)*llabs(x.h);
  birthBoundary+=ll(x.first)*x.pot;
  if(x.next>=0)exitBoundary+=ll(x.dead)*v[x.next].pot;
  birthAbs+=ll(x.first)*llabs(x.pot);
  if(x.next>=0)exitAbs+=ll(x.dead)*llabs(v[x.next].pot);
  maxPot=max(maxPot,llabs(x.pot));maxH=max(maxH,llabs(x.h));
  potSq+=static_cast<long double>(x.first)*x.pot*x.pot;
 }
 if(S!=birthBoundary-exitBoundary)throw runtime_error("exact boundary coboundary equality fails");
 const struct Regression{int X;ll events,growth,resets,signedLoad;}regression[]={
  {4096,29349,399142,2865,-10777},
  {16384,171428,2915326,14422,-501858},
  {65536,795689,19826998,73941,-398293},
  {262144,4082904,138903880,360413,194316}
 };
 for(const auto& r:regression)if(X==r.X &&
   (stats.events!=r.events||stats.growth!=r.growth||stats.reset!=r.resets||S!=r.signedLoad))
  throw runtime_error("historical original-GCD/scalar regression failed");

 for(int j=0;j<X/2;j++)if(firstIndex[j]>=0){
  const int a=firstIndex[j],b=lastIndex[j],c=v[b].next;
  const ll viaBoundary=v[a].pot-(c<0?0:v[c].pot);
  ll direct=0;int index=a;int count=0;
  while(true){direct+=v[index].h;count++;
   if(index==b)break;
   index=v[index].next;
   if(index<0||count>500)throw runtime_error("path not connected");
  }
  if(viaBoundary!=direct)throw runtime_error("individual source boundary mismatch");
  sourceSignal[j]=direct;perSourceAbs+=llabs(direct);
  perSourceRmsSq+=static_cast<long double>(direct)*direct;
  sourceSum+=direct;
 }
 if(sourceSum!=S)throw runtime_error("whole-source scalar mismatch");
 // Every target accumulates an incoming measure from many predecessor states.
 // Jensen gives an exact L^2 energy contraction under reverse conditional averaging.
 vector<long double> incoming(V,0), incomingH(V,0), incomingH2(V,0);
 long double allEdgeEnergy=0;
 for(int i=0;i<V;i++){const int j=v[i].next;
  if(j>=0&&v[i].through>0){
   const ll f=v[i].through;
   incoming[j]+=f;incomingH[j]+=static_cast<long double>(f)*v[i].h;
   incomingH2[j]+=static_cast<long double>(f)*v[i].h*v[i].h;
   allEdgeEnergy+=static_cast<long double>(f)*v[i].h*v[i].h;
  }
 }
 long double avgEnergy=0,dissipation=0;
 long double targetPairCov=0,sourcePairL2=0,targetPairL2=0;
 for(int j=0;j<V;j++)if(incoming[j]>0){
  const long double avg=incomingH[j]/incoming[j];
  const long double variance=incomingH2[j]-incomingH[j]*incomingH[j]/incoming[j];
  if(variance< -0.001L)throw runtime_error("negative Jensen variance");
  dissipation+=max(0.L,variance);
  avgEnergy+=incoming[j]*avg*avg;
  targetPairCov+=incomingH[j]*v[j].h;
  sourcePairL2+=incomingH2[j];
  targetPairL2+=incoming[j]*v[j].h*v[j].h;
 }
 if(fabsl(allEdgeEnergy-avgEnergy-dissipation)>0.05L)
  throw runtime_error("reverse transfer energy identity failed");
 long double rawSq=0,mu=static_cast<long double>(sourceSum)/(X/2);
 for(ll a:sourceSignal)rawSq+=(static_cast<long double>(a)-mu)*(a-mu);
 for(int lag:{1,2,4,8,16,32,64,128,256,512,768,1024,1154,1155,1156,1280,1536,2048}){
  if(lag>=X/2)continue;
  long double cross=0,leftSq=0,rightSq=0,rawCross=0,rawLeft=0,rawRight=0;
  for(int i=0;i+lag<X/2;i++){
   const long double a=static_cast<long double>(sourceSignal[i])-mu;
   const long double b=static_cast<long double>(sourceSignal[i+lag])-mu;
   cross+=a*b;leftSq+=a*a;rightSq+=b*b;
   const long double u=sourceSignal[i],w=sourceSignal[i+lag];
   rawCross+=u*w;rawLeft+=u*u;rawRight+=w*w;
  }
  cout<<"START_SHIFT X="<<X<<" lag="<<lag
      <<" centeredCorr="<<double(cross/sqrtl(leftSq*rightSq))
      <<" rawCorr="<<double(rawCross/sqrtl(rawLeft*rawRight))<<"\n";
 }
 const long double totalSigned=static_cast<long double>(sourceSum);
 for(int HH : {8,32,128,256,512,1024,2048,4096,B}){
  if(HH>X/2)continue;
  const int N=X/2;
  long double window=0,Q=0,A2=0;
  for(ll a:sourceSignal)A2+=static_cast<long double>(a)*a;
  for(int k=0;k<N+HH-1;k++){
    if(k<N)window+=sourceSignal[k];
    if(k>=HH)window-=sourceSignal[k-HH];
    Q+=window*window;
  }
  if(Q+1.0L < HH*HH*totalSigned*totalSigned/(N+HH-1))
   throw runtime_error("van der Corput inequality failed");
  // This is the exact Fejer autocorrelation quadratic form, no mean subtraction.
  const long double upper=sqrtl((N+HH-1)*Q)/HH;
  cout<<"SHIFT_BOUND X="<<X<<" H="<<HH
      <<" vdcUpperOverXB="<<double(upper/(X*static_cast<long double>(B)))
      <<" actualOverXB="<<double(fabsl(totalSigned)/(X*static_cast<long double>(B)))
      <<" FejerMassOverXB4="<<double(Q/(X*powl((long double)B,4)))
      <<" blockMeanRMSoverB="<<double(sqrtl(Q/(N+HH-1))/HH/B)
      <<" sourceRMSoverB="<<double(sqrtl(A2/N)/B)
      <<"\n";
 }
 // k-step reverse-transport contraction; every source supplies its true observed paths.
 for(int lag: {1,2,4,8,16}){
  vector<long double> n(V,0), sum(V,0), sq(V,0);
  ll samples=0;
  for(int j=0;j<X/2;j++)if(firstIndex[j]>=0){
   vector<int> path;int u=firstIndex[j];
   while(true){path.push_back(u);if(u==lastIndex[j])break;
    u=v[u].next;
    if(u<0||path.size()>500)throw runtime_error("invalid lagged path");
   }
   for(size_t k=0;k+lag<path.size();k++){
     const int target=path[k+lag], source=path[k];
     n[target]++;sum[target]+=v[source].h;sq[target]+=static_cast<long double>(v[source].h)*v[source].h;
     samples++;
   }
  }
  long double left=0,right=0;
  for(int i=0;i<V;i++)if(n[i]>0){left+=sq[i];right+=sum[i]*sum[i]/n[i];}
  if(left>0){
   if(right>left+0.05L)throw runtime_error("higher-lag Jensen violated");
   cout<<"LAG X="<<X<<" lag="<<lag<<" pairs="<<samples
       <<" reverseVarianceRetention="<<double(right/left)
       <<" dissipation="<<double(1-right/left)<<"\n";
  }
 }
 // Synthetic source-specific truncation tests the nonzero exit term of the theorem.
 // It deliberately does NOT model the canonical cutoff; only verifies flow algebra.
 if(X==4096){
  vector<ll> syntheticVisits(V,0),syntheticFlows(V,0),syntheticBegins(V,0);
  ll syntheticSigned=0,syntheticBeginPotential=0,syntheticExitPotential=0;
  for(int j=0;j<X/2;j++)if(firstIndex[j]>=0){
   int u=firstIndex[j];syntheticBegins[u]++;
   while(true){syntheticVisits[u]++;syntheticSigned+=v[u].h;
    if(j%3!=0||u==lastIndex[j])break;
    syntheticFlows[u]++;
    u=v[u].next;
    if(u<0)throw runtime_error("invalid synthetic forward path");
   }
  }
  int mixed=0;
  for(int i=0;i<V;i++){
   syntheticBeginPotential+=syntheticBegins[i]*v[i].pot;
   const ll death=syntheticVisits[i]-syntheticFlows[i];
   if(death>0&&syntheticFlows[i]>0)mixed++;
   if(v[i].next>=0)syntheticExitPotential+=death*v[v[i].next].pot;
  }
  if(syntheticSigned!=syntheticBeginPotential-syntheticExitPotential||mixed==0||syntheticExitPotential==0)
   throw runtime_error("synthetic source truncation failed the nonzero exit check");
  cout<<"SYNTHETIC_CUTOFF_PASS mixedNodes="<<mixed
      <<" signed="<<syntheticSigned<<" begin="<<syntheticBeginPotential
      <<" exit="<<syntheticExitPotential<<"\n";
 }
 // Fraction of total flow carried by a reset graph edge, and direct boundary estimate.
 cout<<fixed<<setprecision(8)<<"COBOUNDARY_PASS X="<<X<<" B="<<B
  <<" visits="<<massTotal<<" nodes="<<V<<" startsWithReset="<<firstTotal
  <<" flowEdges="<<stepTotal<<" exits="<<deadTotal
  <<" signed="<<S<<" signedStartBoundary="<<birthBoundary
  <<" signedExitBoundary="<<exitBoundary
  <<" absNode="<<weightedAbsolute<<" absPath="<<double(perSourceAbs)
  <<" absBirthPotential="<<double(birthAbs)<<" absExitPotential="<<double(exitAbs)
  <<" boundaryL1OverNodeL1="<<double((birthAbs+exitAbs)/weightedAbsolute)
  <<" mixedCutoffNodes="<<mixedCutoff
  <<" reverseEdgeL2Ratio="<<double(avgEnergy/allEdgeEnergy)
  <<" reverseEdgeDissipation="<<double(dissipation/allEdgeEnergy)
  <<" reverseEdgeSignCorr="<<double(targetPairCov/sqrtl(sourcePairL2*targetPairL2))
  <<" signedOverNodeAbs="<<double((long double)llabs(S)/weightedAbsolute)
  <<" maxH="<<maxH<<" maxPotential="<<maxPot
  <<" firstPotentialRMS="<<double(sqrtl(potSq/firstTotal))
  <<" sourcePathRMS="<<double(sqrtl(perSourceRmsSq/(X/2)))<<"\n";
}
int main(int argc,char **argv){
 if(argc<2)return 2;
 int mx=0;vector<int>xs;
 for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<2048||(X&1)||X>524288)return 2;xs.push_back(X);mx=max(mx,X);}
 setup(mx);for(int M=7;M<=119;M+=2)if(literal_growth(M,41)!=event_growth(M,41))throw runtime_error("literal original parity GCD mismatch");
 for(int X:xs)run_flow(X);
}
