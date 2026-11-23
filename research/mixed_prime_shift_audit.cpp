// A166944: exact pairwise same-prime/off-prime signed reset-load covariance.
// Compiled with g++ -std=c++17 -O3 -Wall -Wextra -Werror
// Requires committed sibling research/reset_origin_dispersion_audit.cpp
// ./mixed_prime_shift_audit 4096 16384 65536 262144
// Finite original parity-specific clipped-squarefree GCD; not asymptotic theorem.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"
#define main original_reset_origin_audit_main
#include "reset_origin_dispersion_audit.cpp"
#undef main
#pragma GCC diagnostic pop
#include <array>
#include <limits>
#include <unordered_set>
using std::array;
struct Start {vector<int> path;ll load=0;array<ll,3> bands{{0,0,0}};};
struct Vertex {int t,z,cell;};
static bool path_overlap(const vector<int>&a,const vector<int>&b,const vector<Vertex>&v){
  size_t i=0,j=0;
  while(i<a.size()&&j<b.size()){
    int ta=v[a[i]].t,tb=v[b[j]].t;
    if(ta==tb){if(a[i]==b[j])return true;++i;++j;}
    else if(ta<tb)++i;else ++j;
  }
  return false;
}


// Exact Parseval identity for the distribution of ACTUAL merged reset weights
// on every low-wheel cell and every prime modulus. This is an arithmetic
// Fourier energy; no stochastic assumption about the original paths.
static void audit_transport_spectrum(int X,int B,const vector<int>&qList,
  const vector<Vertex>&vertices,const vector<int>&nodeMultiplicity,
  const vector<int>&width,ll signedTotal){
  vector<ll> cellTotal(2*L,0);
  for(size_t vi=0;vi<vertices.size();++vi)
    cellTotal[vertices[vi].cell]+=nodeMultiplicity[vi];
  long double cellTotalSquares=0;
  for(ll x:cellTotal)cellTotalSquares+=(long double)x*x;
  long double spectral=0,coeffEnergy=0;
  for(int q:qList){
    unordered_map<uint64_t,ll> buckets;
    buckets.reserve(vertices.size()*2);
    for(size_t vi=0;vi<vertices.size();++vi){
      const Vertex&v=vertices[vi];
      uint64_t key=uint64_t(v.cell)*q+(v.t%q);
      buckets[key]+=nodeMultiplicity[vi];
    }
    long double residueSquares=0;
    for(const auto&[key,v]:buckets){(void)key;residueSquares+=(long double)v*v;}
    const long double energy=q*residueSquares-cellTotalSquares;
    if(energy<-0.01L)throw runtime_error("Parseval energy below zero");
    spectral+=energy;
    for(int u:width)coeffEnergy+=(long double)q*u-(long double)u*u;
  }
  const long double Bnorm=(long double)X*B;
  const long double logB=logl(B);
  const long double absBound=sqrtl(spectral*coeffEnergy);
  if(fabsl((long double)signedTotal)>absBound+1)
    throw runtime_error("Fourier Parseval/Cauchy signed bound invalid");
  cout<<fixed<<setprecision(7)<<"SPECTRUM_PASS X="<<X
      <<" spectralEnergy="<<double(spectral)
      <<" coefficientEnergy="<<double(coeffEnergy)
      <<" spectralOverX2logB="<<double(spectral/((long double)X*X*logB))
      <<" FourierCauchyBoundOverXB="<<double(absBound/Bnorm)
      <<" actualSignedOverXB="<<double(signedTotal/Bnorm)<<"\n";
}

// For scans where every visited reset node has an identical continuation status
// for all sources, two paths share a node iff they have the same final reset node.
// This is checked dynamically; it is NOT claimed for all canonical windows.
static long double fejer_q(const vector<int>&F,int N,int Q,int index,int H){
  long double rolling=0,squares=0,diagonal=0;
  for(int j=0;j<N;j++){
    long double val=F[size_t(j)*Q+index];diagonal+=val*val;
  }
  for(int n=0;n<N+H-1;n++){
    if(n<N)rolling+=F[size_t(n)*Q+index];
    if(n>=H)rolling-=F[size_t(n-H)*Q+index];
    squares+=rolling*rolling;
  }
  return (squares-H*diagonal)/2;
}
static long double fejer_total(const vector<Start>&starts,int H){
  const int N=starts.size();long double rolling=0,squares=0,diagonal=0;
  for(const auto&s:starts){const long double a=s.load;diagonal+=a*a;}
  for(int n=0;n<N+H-1;n++){
    if(n<N)rolling+=starts[n].load;
    if(n>=H)rolling-=starts[n-H].load;
    squares+=rolling*rolling;
  }
  return (squares-H*diagonal)/2;
}
template<class Getter>
static long double fejer_joined(const vector<vector<int>>&groups,int H,const Getter&get){
  long double sum=0;
  for(const auto&g:groups){
    size_t left=0;long double xSum=0,ixSum=0;
    for(int j:g){
      while(left<g.size()&&g[left]<j-H+1){
        int k=g[left++];long double x=get(k);
        xSum-=x;ixSum-=k*x;
      }
      const long double x=get(j);
      sum+=x*((H-j)*xSum+ixSum);
      xSum+=x;ixSum+=j*x;
    }
  }
  return sum;
}

static void audit(int X){
  const int B=int(ceill(sqrtl(7.L*X))),N=X/2;
  qs.clear();for(int q=103;q<=B;q+=2)if(spf[q]==q)qs.push_back(q);
  const int Q=int(qs.size());
  Stat stat;const auto records=collect(X,B,stat);
  vector<vector<int>> prefixes(2*L);
  vector<int> width(2*L,0);
  for(int z:{0,6})for(int r=0;r<L;r++){
    int c=r+(z==6?L:0);
    prefixes[c]=low_prefix_growths(r,z);
    vector<int> offsets;
    for(int e:prefixes[c]){offsets.push_back(e-1);offsets.push_back(e+1);}
    sort(offsets.begin(),offsets.end());
    offsets.erase(unique(offsets.begin(),offsets.end()),offsets.end());
    width[c]=int(offsets.size());
    if(width[c]<2||width[c]>31)throw runtime_error("low-wheel finite root width failed");
  }
  vector<Vertex> vertices;
  vector<Start> starts(N);
  unordered_map<int,int> byKey;
  byKey.reserve(records.size());
  for(const auto&r:records){
    int key=2*r.t+(r.z==6),si=(r.M-X-1)/2;
    auto it=byKey.find(key);
    if(it==byKey.end()){
      int id=int(vertices.size());
      byKey.emplace(key,id);
      vertices.push_back({r.t,r.z,r.t%L+(r.z==6?L:0)});
      it=byKey.find(key);
    }
    starts[si].path.push_back(it->second);
  }
  for(auto &s:starts){
    for(size_t i=1;i<s.path.size();++i)
      if(vertices[s.path[i-1]].t>=vertices[s.path[i]].t)
        throw runtime_error("reset path not time-increasing");
  }
  vector<int> pqLoad(size_t(N)*Q,0);
  vector<long double> anchorAdjustment(vertices.size(),0);
  long long forbiddenNodePrimePairs=0,weightedForbiddenVisits=0;
  vector<int> nodeMultiplicity(vertices.size(),0);
  for(const auto&x:starts)for(int vi:x.path)nodeMultiplicity[vi]++;
  for(int qIndex=0;qIndex<Q;qIndex++){
    int q=qs[qIndex];
    vector<vector<int>> roots(2*L);
    vector<unsigned char> initialized(2*L,0);
    vector<int> vertexLoad(vertices.size());
    for(size_t vi=0;vi<vertices.size();++vi){
      const auto&v=vertices[vi];int c=v.cell;
      if(!initialized[c]){
        roots[c]=rootsets(v.z,prefixes[c],q);
        if(int(roots[c].size())!=width[c])throw runtime_error("stable candidate width violated");
        initialized[c]=1;
      }
      bool hit=binary_search(roots[c].begin(),roots[c].end(),v.t%q);
      const int anchor=(v.z==0?v.t:v.t-2);
      const bool forbidden=(anchor%q)==0;
      if(forbidden&&hit)throw runtime_error("reset anchor-forbidden q was candidate");
      if(forbidden){
        ++forbiddenNodePrimePairs;
        weightedForbiddenVisits+=nodeMultiplicity[vi];
        anchorAdjustment[vi]+=width[c];
      }else anchorAdjustment[vi]-=static_cast<long double>(width[c])/(q-1);
      vertexLoad[vi]=(hit?q:0)-width[c];
    }
    for(int j=0;j<N;j++){
      ll sum=0;
      for(int vi:starts[j].path)sum+=vertexLoad[vi];
      if(sum<INT32_MIN||sum>INT32_MAX)throw runtime_error("int overflow in q path");
      pqLoad[size_t(j)*Q+qIndex]=int(sum);
      starts[j].load+=sum;
      const int band=(q*4<B)?0:(q*2<B)?1:2;
      starts[j].bands[band]+=sum;
    }
  }
  ll signedTotal=0, resetTotal=0;long double conditionedSigned=0;
  for(const auto&s:starts){signedTotal+=s.load;resetTotal+=s.path.size();
    long double value=s.load;for(int vi:s.path)value+=anchorAdjustment[vi];
    conditionedSigned+=value;
  }
  const struct Check {int X;ll signedLoad,events,growth,resets;} checkpoints[] = {
    {4096,-10777,29349,399142,2865},
    {16384,-501858,171428,2915326,14422},
    {65536,-398293,795689,19826998,73941},
    {262144,194316,4082904,138903880,360413}
  };
  for(const auto&c:checkpoints)if(c.X==X&&
   (signedTotal!=c.signedLoad||stat.events!=c.events||stat.growth!=c.growth||resetTotal!=c.resets))
    throw runtime_error("original GCD and previous signed scalar regression violated");
  audit_transport_spectrum(X,B,qs,vertices,nodeMultiplicity,width,signedTotal);
  cout<<fixed<<setprecision(7)<<"MIXED_PASS X="<<X<<" B="<<B<<" starts="<<N<<" qCount="<<Q
      <<" resetVisits="<<resetTotal<<" nodes="<<vertices.size()<<" signed="<<signedTotal<<"\n";
  unordered_map<int,int> nextStatus;
  ll partialVertices=0;
  for(const auto&r:records){
    const int id=2*r.t+(r.z==6);
    const int next=r.nextResetT ? 2*r.nextResetT+(r.nextResetZ==6) : -1;
    auto [it,inserted]=nextStatus.emplace(id,next);
    if(!inserted&&it->second!=next){partialVertices++;}
  }
  // Partial cutoff vertices require a more elaborate pair-intersection algorithm.
  // Do not apply same-terminal grouping when the check fails.
  if(partialVertices==0){
    unordered_map<int,int> sinkGroup;
    vector<vector<int>> groups;
    for(int j=0;j<N;j++){
      if(starts[j].path.empty())continue;
      const int sink=starts[j].path.back();
      auto it=sinkGroup.find(sink);
      if(it==sinkGroup.end()){
        int id=int(groups.size());sinkGroup.emplace(sink,id);
        groups.push_back({j});
      }else groups[it->second].push_back(j);
    }
    for(int lag:{1,2,16,32,256,1155})if(lag<N){
      for(int j=0;j+lag<N;j++){
        bool overlap=path_overlap(starts[j].path,starts[j+lag].path,vertices);
        bool endSame=!starts[j].path.empty()&&!starts[j+lag].path.empty()&&
          starts[j].path.back()==starts[j+lag].path.back();
        if(overlap!=endSame)throw runtime_error("terminal grouping vs pair intersection mismatch");
      }
    }
    for(int H : {B,int(powl((long double)B,1.25L)),int(powl((long double)B,1.5L))}){
      H=min(N,max(1,H));
      long double all=fejer_total(starts,H),
                  join=fejer_joined(groups,H,[&](int j){return (long double)starts[j].load;});
      long double diagAll=0,diagJoin=0;
      for(int qi=0;qi<Q;qi++){
        diagAll+=fejer_q(pqLoad,N,Q,qi,H);
        diagJoin+=fejer_joined(groups,H,[&](int j){return (long double)pqLoad[size_t(j)*Q+qi];});
      }
      long double dis=all-join,disSame=diagAll-diagJoin,
        disMixed=dis-disSame;
      const long double scale=(long double)X*B*B*H*H;
      cout<<"MIXED_FEJER X="<<X<<" H="<<H
          <<" totalOffDiagScaled="<<double(all/scale)
          <<" joinedScaled="<<double(join/scale)
          <<" disjointScaled="<<double(dis/scale)
          <<" disjointSamePrimeScaled="<<double(disSame/scale)
          <<" disjointDifferentPrimeScaled="<<double(disMixed/scale)
          <<" samePrimeAllScaled="<<double(diagAll/scale)
          <<" mixedPrimeAllScaled="<<double((all-diagAll)/scale)
          <<" groupedTerminalNodes="<<groups.size()<<" partialVertices="<<partialVertices<<"\n";
    }
  }else cout<<"MIXED_PARTIAL_VERTEX X="<<X<<" partial="<<partialVertices<<" [no grouped Fejer decomposition]"<<"\n";
  cout<<"ANCHOR_PASS X="<<X<<" forcedPrimeNodePairs="<<forbiddenNodePrimePairs
      <<" weightedForcedVisits="<<weightedForbiddenVisits
      <<" signedOriginal="<<signedTotal
      <<" signedAnchorAdjusted="<<double(conditionedSigned)
      <<" normalizedOriginal="<<double(signedTotal/(static_cast<long double>(X)*B))
      <<" normalizedAdjusted="<<double(conditionedSigned/(static_cast<long double>(X)*B))<<"\n";
  // Every pair contribution is RAW and uncentered, suitable for the Fejer form.
  for(int ell:{1,2,4,8,16,32,64,128,256,512,1155,B}){
    if(ell>=N)continue;
    long double rawJoined=0,rawDisjoint=0,sameJoined=0,sameDisjoint=0;
    ll joinedPairs=0,nonjoinedPairs=0;
    long double disBand[3][3]={{}};
    unordered_map<uint64_t,int> coarseCells;
    for(int j=0;j+ell<N;j++){
      const auto&a=starts[j],&b=starts[j+ell];
      const bool joined=path_overlap(a.path,b.path,vertices);
      long double diagonal=0;
      const int*ra=pqLoad.data()+size_t(j)*Q;
      const int*rb=pqLoad.data()+size_t(j+ell)*Q;
      for(int qi=0;qi<Q;qi++)diagonal+=static_cast<long double>(ra[qi])*rb[qi];
      const long double full=static_cast<long double>(a.load)*b.load;
      if(joined){joinedPairs++;rawJoined+=full;sameJoined+=diagonal;}
      else{nonjoinedPairs++;rawDisjoint+=full;sameDisjoint+=diagonal;
        if(!a.path.empty()&&!b.path.empty()){
          const int ta=vertices[a.path.front()].t;
          const int tb=vertices[b.path.front()].t;
          uint64_t key=(uint64_t(ta%L)<<32)|uint32_t(tb-ta);
          coarseCells[key]++;
        }
        for(int x=0;x<3;x++)for(int y=0;y<3;y++)
          disBand[x][y]+=static_cast<long double>(a.bands[x])*b.bands[y];
      }
    }
    const long double denom=N-ell;
    if(joinedPairs+nonjoinedPairs!=N-ell)throw runtime_error("pair partition mismatch");
    ll singleton=0,coarseMax=0;
    for(const auto&item:coarseCells){
      singleton+=(item.second==1);
      coarseMax=max(coarseMax,ll(item.second));
    }
    cout<<"MIXED_LAG X="<<X<<" ell="<<ell
      <<" shared="<<joinedPairs<<" nonshared="<<nonjoinedPairs
      <<" disjointTotalRawMean="<<double(rawDisjoint/denom)
      <<" disjointSamePrimeRawMean="<<double(sameDisjoint/denom)
      <<" disjointDifferentPrimeRawMean="<<double((rawDisjoint-sameDisjoint)/denom)
      <<" joinTotalRawMean="<<double(rawJoined/denom)
      <<" joinSamePrimeRawMean="<<double(sameJoined/denom)
      <<" joinDifferentPrimeRawMean="<<double((rawJoined-sameJoined)/denom)
      <<" totalRawMean="<<double((rawDisjoint+rawJoined)/denom)
      <<" disBand00="<<double(disBand[0][0]/denom)
      <<" disBand11="<<double(disBand[1][1]/denom)
      <<" disBand22="<<double(disBand[2][2]/denom)
      <<" disBandCross="<<double((rawDisjoint-disBand[0][0]-disBand[1][1]-disBand[2][2])/denom)
      <<" firstResetCRTCells="<<coarseCells.size()
      <<" singletonCRTCells="<<singleton
      <<" maxCRTCellOccupancy="<<coarseMax
      <<"\n";
  }
}

// Exact mixed-prime CRT orthogonality at a fixed (r,z),(r',z') pair and
// a fixed time difference delta. NOT a claim about adaptive source pairs.
static void unit_test_two_prime_crt(){
  for(const auto& primePair:array<array<int,2>,3>{{{{103,107}},{{103,109}},{{107,109}}}}){
    const int q=primePair[0],p=primePair[1];
    for(int r:{1,5,387,1255})for(int delta:{-32,1,32,1155,2310})
      for(int z:{0,6})for(int zz:{0,6}){
        int rr=(r+delta)%L;if(rr<0)rr+=L;
        const vector<int> U=rootsets(z,low_prefix_growths(r,z),q);
        const vector<int> V=rootsets(zz,low_prefix_growths(rr,zz),p);
        ll cross=0;
        for(int k=0;k<q*p;k++){
          const ll t=r+4LL*L+1LL*L*k;
          const int fq=(binary_search(U.begin(),U.end(),int(t%q))?q:0)-int(U.size());
          const ll t2=t+delta;
          const int rem=int((t2%p+p)%p);
          const int fp=(binary_search(V.begin(),V.end(),rem)?p:0)-int(V.size());
          cross+=1LL*fq*fp;
        }
        if(cross!=0)throw runtime_error("two distinct prime CRT test failed");
      }
  }
  for(int q:{103,211})for(int delta:{0,1,32,100}){
    const int r=127, rr=(r+delta)%L;
    const vector<int> U=rootsets(0,low_prefix_growths(r,0),q);
    const vector<int> V=rootsets(6,low_prefix_growths(rr,6),q);
    ll sum=0,intersection=0;
    for(int k=0;k<q;k++){
      const int a=(r+L*k)%q,b=(a+delta)%q;
      const bool ua=binary_search(U.begin(),U.end(),a);
      const bool vb=binary_search(V.begin(),V.end(),b);
      sum+=1LL*((ua?q:0)-int(U.size()))*((vb?q:0)-int(V.size()));
      intersection+=(ua&&vb);
    }
    const ll expected=1LL*q*(1LL*q*intersection-1LL*U.size()*V.size());
    if(sum!=expected)throw runtime_error("same-prime shifted CRT identity mismatch");
    if(q==211&&delta==100&&intersection!=0)
      throw runtime_error("same-prime nonresonant exclusion failed");
  }
  cout<<"CRT_ORTHOGONALITY_PASS primePairs=3 fixed_shift_cases=240 full_periods=true samePrimeCases=8"<<"\n";
}

int main(int argc,char **argv){
  if(argc<2)return 2;
  int mx=0;vector<int>xs;
  for(int i=1;i<argc;i++){
    int X=atoi(argv[i]);if(X<2048||(X&1)||X>524288)return 2;
    xs.push_back(X);mx=max(mx,X);
  }
  setup(mx);
  unit_test_two_prime_crt();
  for(int M=7;M<=119;M+=2)
    if(literal_growth(M,41)!=event_growth(M,41))throw runtime_error("original literal-step parity GCD regression");
  for(int X:xs)audit(X);
}
