// Exact capped-gcd A166944 wheel insertion with FIRST-HIT factor clocks.
// Run: g++ -O3 -std=c++17 research/adaptive_wheel_insertion_audit.cpp -o /tmp/wheel_adapt
//      /tmp/wheel_adapt 512     # or 256,1024,2048,4096
// Tests growth-adaptive theorem: if q>6*G_old+7 then
// fresh p: G_new>=G_old, nonzero gain>=p-1; existing p: NO change.
// Finite arithmetic checks, NOT Cap B or twin-prime infinitude.
#include <bits/stdc++.h>
using namespace std;
using i64=long long;
vector<int> spf, exponent;
vector<pair<int,int>> powers;
vector<int> distinct_factors(int n) {
  vector<int> out;
  while(n>1) {
    int p=spf[n];
    out.push_back(p);
    do {n/=p;} while(n%p==0);
  }
  return out;
}
int capped_gcd(int a,int b) {
  int d=gcd(a,b),res=1;
  while(d>1) {
    int p=spf[d], k=0;
    do {d/=p; ++k;} while(d%p==0);
    for(int j=0;j<min(k,exponent[p]);++j)res*=p;
  }
  return res;
}
i64 next_clock(i64 pos,int p,i64 residue) {
  i64 mod=2LL*p,delta=(residue-pos)%mod;
  if(delta<=0)delta+=mod;
  return pos+delta;
}
int wheel_growth(int M) {
  i64 s=M+2, K=(7LL*M-1)/4, pos=s, C=2LL*M-2;
  while(pos<K) {
    i64 next=K+1;
    for(int p:distinct_factors(int(C-1)))
      if(exponent[p]) next=min(next,next_clock(pos,p,0));
    for(int p:distinct_factors(int(C+1)))
      if(exponent[p]) next=min(next,next_clock(pos,p,p+2));
    if(next>K)break;
    int e=capped_gcd(int((next&1)? next-2:next),
                     int((next&1)? C+1:C-1));
    if(e<=1)throw runtime_error("invalid first hit");
    pos=next;C+=e-1;
  }
  return int(C-(2LL*M-2));
}
int original_growth(int M) {
  i64 c=2LL*M-2, K=(7LL*M-1)/4;
  for(int n=M+3;n<=K;++n) {
    int e=int((n&1)?gcd(i64(n-2),c+1):gcd(i64(n),c-1));
    c+=e-1;
  }
  return int(c-(2LL*M-2));
}
int main(int argc,char**argv) {
  int X=argc>1?atoi(argv[1]):512;
  if(X<128 || X>4096 || (X&1))return 2;
  int limit=7*X+10;
  spf.resize(limit);
  iota(spf.begin(),spf.end(),0);
  for(int p=2;p*p<limit;++p)
    if(spf[p]==p)
      for(int x=p*p;x<limit;x+=p)
        if(spf[x]==x)spf[x]=p;
  exponent.assign(limit,0);
  for(int p=3;p<=4*X;p+=2)
    if(spf[p]==p)
      for(i64 q=p;q<=4LL*X;q*=p)
        powers.push_back({int(q),p});
  sort(powers.begin(),powers.end());
  vector<int> starts;
  for(int M=X+1;M<2*X;M+=2) starts.push_back(M);
  vector<int> before(starts.size(),0);
  i64 pos=0,neg=0,safe=0,safeFreshPositive=0,
      safeHighPowerZero=0,unsafeNegative=0;
  for(auto [q,p]:powers) {
    ++exponent[p];
    for(size_t i=0;i<starts.size();++i) {
      int after=wheel_growth(starts[i]);
      int diff=after-before[i];
      if(q>6LL*before[i]+7) {
        ++safe;
        if(exponent[p]==1) {
          if(diff<0 || (diff>0&&diff<p-1))
            throw runtime_error("fresh-prime sign theorem failed");
          if(diff>0)++safeFreshPositive;
        } else {
          if(diff!=0)
            throw runtime_error("higher-power inertia theorem failed");
          ++safeHighPowerZero;
        }
      } else if(diff<0)++unsafeNegative;
      pos+=max(0,diff);
      neg+=max(0,-diff);
      before[i]=after;
    }
  }
  i64 net=accumulate(before.begin(),before.end(),0LL);
  if(pos-neg!=net)throw runtime_error("signed telescoping failed");
  for(size_t i=0;i<starts.size();++i)
    if(before[i]!=original_growth(starts[i]))
      throw runtime_error("capped wheel final path differs from original");
  struct Row {int x,stages; i64 safe,fresh,higher,negUnsafe,pos,neg,net;};
  const vector<Row> refs={
    {256,188,11735,16,838,15,12658,372,12286},
    {512,329,60918,28,2912,53,25622,6342,19280},
    {1024,592,248304,67,9519,40,50044,2340,47704},
    {2048,1065,935126,184,25891,113,159740,13134,146606},
    {4096,1947,3510359,455,66110,352,549928,52092,497836}
  };
  for(auto row:refs)if(X==row.x) {
    if((int)powers.size()!=row.stages || safe!=row.safe
       ||safeFreshPositive!=row.fresh ||safeHighPowerZero!=row.higher
       ||unsafeNegative!=row.negUnsafe ||pos!=row.pos
       ||neg!=row.neg ||net!=row.net)
      throw runtime_error("finite expected counts mismatch");
  }
  cout<<"PASS X="<<X<<" starts="<<starts.size()
      <<" inserted_prime_powers="<<powers.size()
      <<" comparisons="<<starts.size()*powers.size()
      <<" safe="<<safe<<" fresh_positive="<<safeFreshPositive
      <<" high_power_inert="<<safeHighPowerZero
      <<" all_negative_in_unsafe="<<unsafeNegative
      <<" sum_positive="<<pos<<" sum_negative="<<neg
      <<" sum_growth="<<net
      <<" quarter_sum_M="<<i64(3)*X*X/16<<"\n";
}
