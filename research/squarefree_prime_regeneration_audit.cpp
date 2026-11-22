// Exact squarefree-prime insertion, 4-state X reset and canonical
// regeneration audit for the original parity-dependent A166944 gcd.
// Build: g++ -O3 -std=c++17 research/squarefree_prime_regeneration_audit.cpp -o /tmp/sqregen
// Run: /tmp/sqregen 4096 ; /tmp/sqregen 16384
// Finite integer checks ONLY; global mean/Cap B/twin infinitude OPEN.
#include <bits/stdc++.h>
using namespace std;
using i64=long long;
vector<int> spf;
vector<int> factors(int n) {
  vector<int> result;
  while (n>1) {
    int p=spf[n];
    result.push_back(p);
    do { n/=p; } while(n%p==0);
  }
  return result;
}
i64 next_clock(i64 pos,int p,i64 r) {
  i64 modulus=2LL*p, delta=(r-pos)%modulus;
  if(delta<=0)delta+=modulus;
  return pos+delta;
}
struct Replay { int growth, prime_hits; i64 last; };
Replay replay(int M,int P,int watched=0,i64 explicitK=0) {
  i64 start=M+2,K=explicitK?explicitK:(7LL*M-1)/4;
  if(K<start)throw runtime_error("cutoff before seed");
  i64 pos=start,C=2LL*M-2,last=start;
  int watched_hits=0;
  while(pos<K) {
    i64 next=K+1;
    for(int p:factors(int(C-1)))
      if(p<=P)next=min(next,next_clock(pos,p,0));
    for(int p:factors(int(C+1)))
      if(p<=P)next=min(next,next_clock(pos,p,p+2));
    if(next>K)break;
    int raw=int(gcd((next&1)?next-2:next,(next&1)?C+1:C-1));
    int e=1;
    for(int p:factors(raw))if(p<=P)e*=p;
    if(e<=1)throw runtime_error("wrong first-hit event");
    if(watched && e%watched==0)++watched_hits;
    C+=e-1;
    // Universal p-hit congruence, including all UNSAFE multi-prime events.
    for(int q:factors(e)) {
      i64 deficit=2*next-C;
      bool correct=(next&1)?((deficit-6)%(2*q)==0)
                            :(deficit%(2*q)==0);
      if(!correct)throw runtime_error("universal post-hit X mod 2p failed");
    }
    pos=last=next;
  }
  return {int(C-(2LL*M-2)),watched_hits,last};
}
struct Counts {
  i64 safe=0,splits=0,early=0,late=0,plus=0,minus=0;
  i64 plus_oneshot=0,plus_actual_refires=0;
  i64 minus_bridge=0,minus_oneshot=0,minus_bridge_refires=0;
  i64 bridge3=0,bridge5=0,bridge7=0;
  i64 minus_all_oneshot=0,minus_all_refires=0;
};
int main(int argc,char**argv) {
  int X=argc>1?atoi(argv[1]):4096;
  if(X!=4096 && X!=16384)return 2;
  int bound=int(7LL*X+10000), B=int(ceil(sqrt(7.0*X)));
  spf.resize(bound);
  iota(spf.begin(),spf.end(),0);
  for(int p=2;1LL*p*p<bound;p++)if(spf[p]==p)
    for(int j=p*p;j<bound;j+=p)if(spf[j]==j)spf[j]=p;
  vector<int> primes;
  for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);
  Counts out;
  for(size_t j=0;j<primes.size();++j) {
    int p=primes[j], oldP=j?primes[j-1]:1;
    for(int M=X+1;M<2*X;M+=2) {
      Replay old=replay(M,oldP);
      int h=old.growth;
      if(p<=6LL*h+7)continue;
      ++out.safe;
      i64 s=M+2,K=(7LL*M-1)/4,T=K-s,C=2LL*M-2+h;
      bool isMinus=(C-1)%p==0,isPlus=(C+1)%p==0;
      if(isMinus&&isPlus)throw runtime_error("same p divides both neighbors");
      if(!isMinus&&!isPlus)continue;
      i64 a=(p+h-1)/2;
      int eps=int(a%2);
      i64 t=a+(isMinus?-3:0)+eps*p;
      if(t<=old.last-s)throw runtime_error("split clock before old freeze");
      if(t>T)continue;
      ++out.splits;
      if(eps)++out.late;else ++out.early;
      i64 n=s+t;
      int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
      if(raw%p)throw runtime_error("p did not trigger");
      int expectedX=(isPlus?6:0)+2*eps*p;
      if(2*n-(C+p-1)!=expectedX)throw runtime_error("wrong deficit reset");
      Replay newer=replay(M,p,p);
      if(newer.prime_hits<1 || newer.growth<h+p-1)
        throw runtime_error("predicted split missing");
      if(eps)continue;
      i64 u=M+a;
      if((u&1)==0 || u!=(C+p+1)/2)
        throw runtime_error("bad canonical regeneration map");
      if(isPlus) {
        ++out.plus;
        if(u!=n-2 || u%p!=0 || expectedX!=6)
          throw runtime_error("plus seed failed");
        int tail=replay(int(u),oldP,0,K).growth;
        if(tail<p+1) {
          ++out.plus_oneshot;
          if(newer.growth!=h+p-1+tail)
            throw runtime_error("plus one-shot identity failed");
        }
        if(newer.prime_hits>1)++out.plus_actual_refires;
      } else {
        ++out.minus;
        if(u!=n+1 || u%p!=1 || expectedX!=0)
          throw runtime_error("minus seed failed");
        // UNIVERSAL seven-step bridge from an even X(n)=0:
        // Until X=6, only e=1,3,5 may occur. This includes both
        // 3-step-quiet and 3/5-interrupted bridges (p>=11 cannot refire).
        int x=0,bridgeGrowth=0,k=0;
        i64 at=n;
        while(x!=6) {
          ++at;++k;
          int raw=(at&1)?int(gcd(at-2,i64(abs(x-3))))
                         :int(gcd(at,i64(x+3)));
          int e=1;
          for(int q:factors(raw))if(q<=oldP)e*=q;
          if(e!=1&&e!=3&&e!=5)
            throw runtime_error("unexpected non-small bridge factor");
          x+=3-e;bridgeGrowth+=e-1;
          if(k>7)throw runtime_error("universal bridge exceeded seven");
        }
        if(bridgeGrowth!=2*k-6 || (k!=3&&k!=5&&k!=7)
           || (at&1)==0 || i64(2*at-6)!=2*(at-2)-2)
          throw runtime_error("universal bridge identity failed");
        if(k==3)++out.bridge3;
        if(k==5)++out.bridge5;
        if(k==7)++out.bridge7;
        if(k==3)++out.minus_bridge;
        if(at>K)continue;
        int v=int(at-2);
        if(v!=u+bridgeGrowth/2 || v%p!=(1+bridgeGrowth/2)%p)
          throw runtime_error("bounded canonical target wrong");
        int tail=replay(v,oldP,0,K).growth;
        // The post-p even horizon is 0 mod p: p cannot refire if
        // the total hypothetical L-only growth stays below p-1.
        if(bridgeGrowth+tail<p-1) {
          ++out.minus_all_oneshot;
          if(k==3)++out.minus_oneshot;
          if(newer.growth!=h+p-1+bridgeGrowth+tail)
            throw runtime_error("universal minus one-shot identity failed");
        }
        if(newer.prime_hits>1) {
          ++out.minus_all_refires;
          if(k==3)++out.minus_bridge_refires;
        }
      }
    }
  }
  if(out.splits!=out.early+out.late || out.early!=out.plus+out.minus)
    throw runtime_error("count partition wrong");
  Counts expected;
  if(X==4096) {
    expected={12030,501,254,247,128,126,77,3,111,62,3,
              111,2,13,67,3};
  } else {
    expected={105280,2463,1183,1280,597,586,356,18,498,266,22,
              498,37,51,322,26};
  }
  if(tie(out.safe,out.splits,out.early,out.late,out.plus,out.minus,
         out.plus_oneshot,out.plus_actual_refires,out.minus_bridge,
         out.minus_oneshot,out.minus_bridge_refires,
         out.bridge3,out.bridge5,out.bridge7,
         out.minus_all_oneshot,out.minus_all_refires)
     !=tie(expected.safe,expected.splits,expected.early,expected.late,
         expected.plus,expected.minus,expected.plus_oneshot,
         expected.plus_actual_refires,expected.minus_bridge,
         expected.minus_oneshot,expected.minus_bridge_refires,
         expected.bridge3,expected.bridge5,expected.bridge7,
         expected.minus_all_oneshot,expected.minus_all_refires))
    throw runtime_error("finite regression counts changed");
  cout<<"PASS X="<<X<<" safe="<<out.safe<<" first_p_splits="<<out.splits
      <<" early="<<out.early<<" late="<<out.late
      <<" plus="<<out.plus<<" minus="<<out.minus
      <<" plus_one_shot="<<out.plus_oneshot
      <<" plus_actual_refires="<<out.plus_actual_refires
      <<" minus_quiet_bridge="<<out.minus_bridge
      <<" minus_one_shot="<<out.minus_oneshot
      <<" minus_actual_refires="<<out.minus_bridge_refires
      <<" bridge3="<<out.bridge3<<" bridge5="<<out.bridge5
      <<" bridge7="<<out.bridge7
      <<" minus_all_oneshot="<<out.minus_all_oneshot
      <<" minus_all_refires="<<out.minus_all_refires<<"\n"
      <<"Universal dyadic mean bound remains UNPROVED\n";
}
