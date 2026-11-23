// Cross-Issue #3/#4 squarefree-wheel ledger, C++17.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_signed_and_composite_ledger.cpp -o /tmp/twin_ledger
// /tmp/twin_ledger 256 512 1024 4096 16384 65536 262144
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll = long long;
vector<int> spf;
void sieve(int n) {
  spf.resize(n); iota(spf.begin(), spf.end(), 0);
  for (int p=2; 1LL*p*p<n; ++p) if (spf[p]==p)
    for (int k=p*p; k<n; k+=p) if (spf[k]==k) spf[k]=p;
}
void factor(int n, vector<int>& primes) {
  primes.clear();
  while (n>1) {
    int p=spf.at(n); primes.push_back(p);
    do { n/=p; } while (n%p==0);
  }
}
int wait_clock(ll t, int p, int residue) {
  int gap=int((residue-t)%(2LL*p)); return gap>0?gap:gap+2*p;
}
struct Path {
  ll grow=0, linear=0, excess=0;
  int hits_at_cutoff=0;
};
Path stage_path(int M, int cutoff) {
  Path s; ll t=M+2, C=2LL*M-2, K=(7LL*M-1)/4;
  vector<int> f;
  while (t<K) {
    ll n=K+1;
    factor(int(C-1), f);
    for (int p:f) if (p<=cutoff) n=min(n,t+wait_clock(t,p,0));
    factor(int(C+1), f);
    for (int p:f) if (p<=cutoff) n=min(n,t+wait_clock(t,p,p+2));
    if (n>K) break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
    factor(raw,f); int d=1,lin=0;
    for (int p:f) if (p<=cutoff) {
      d*=p; lin+=p-1; if (p==cutoff) ++s.hits_at_cutoff;
    }
    if (d<=1) throw runtime_error("clock mismatch");
    s.grow+=d-1; s.linear+=lin; s.excess+=d-1-lin;
    C+=d-1; t=n;
  }
  if (s.grow!=s.linear+s.excess) throw runtime_error("factor ledger mismatch");
  return s;
}
void audit(int X) {
  int B=int(ceill(sqrtl(7.L*X)));
  vector<int> primes;
  for (int p=3;p<=B;p+=2) if (spf[p]==p) primes.push_back(p);
  vector<Path> old(X/2);
  ll positive=0,negative=0,stageFirst=0,stageRepeat=0,jointPositive=0;
  ll pNew=0,oldShift=0,compositeShift=0;
  bool stageScanned=(X<=16384);
  for (int p:primes) {
    if (!stageScanned) break;
    for (int i=0;i<X/2;++i) {
      int M=X+1+2*i; Path now=stage_path(M,p), prev=old[i];
      ll delta=now.grow-prev.grow;
      ll fresh=ll(p-1)*now.hits_at_cutoff;
      ll drift=now.linear-fresh-prev.linear;
      ll nonlinear=now.excess-prev.excess;
      if (delta!=fresh+drift+nonlinear) throw runtime_error("stage identity failed");
      positive+=max(0LL,delta); negative+=max(0LL,-delta);
      pNew+=fresh; oldShift+=drift; compositeShift+=nonlinear;
      stageFirst+=ll(p-1)*(now.hits_at_cutoff>0);
      stageRepeat+=ll(p-1)*max(now.hits_at_cutoff-1,0);
      jointPositive+=max(0LL,drift+nonlinear);
      old[i]=now;
    }
  }
  ll W=0,Lin=0,Ex=0,PairCap=0,Fw=0,Rw=0,events=0,composites=0,H=0,F=0,Z=0;
  vector<int> qhit(B+1,0),touched,f;
  for (int M=X+1;M<2*X;M+=2) {
    ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
    touched.clear();
    while (t<K) {
      ll n=K+1;
      factor(int(C-1),f);
      for (int p:f) if (p<=B) n=min(n,t+wait_clock(t,p,0));
      factor(int(C+1),f);
      for (int p:f) if (p<=B) n=min(n,t+wait_clock(t,p,p+2));
      if (n>K) break;
      int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
      factor(raw,f); int d=1,lin=0,omega=0;
      vector<int> labels;
      for (int p:f) if (p<=B) {
        d*=p; lin+=p-1; ++omega; labels.push_back(p);
        if (qhit[p]++==0) touched.push_back(p);
      }
      if (d<=1) throw runtime_error("final clock mismatch");
      ++events; composites+=omega>=2;
      for (size_t i=0;i<labels.size();++i)
        for (size_t j=i+1;j<labels.size();++j)
          PairCap+=ll(d/labels[i]/labels[j])*(labels[i]-1)*(labels[j]-1);
      W+=d-1; Lin+=lin; Ex+=d-1-lin;
      C+=d-1; t=n;
    }
    for (int p:touched) {
      int v=qhit[p]; qhit[p]=0;
      Fw+=p-1; Rw+=ll(p-1)*(v-1);
      if (p>=19) {H+=v; ++F; Z+=ll(v)*v;}
    }
  }
  if (W!=Lin+Ex||Lin!=Fw+Rw||Ex>PairCap||
      (stageScanned && (W!=positive-negative||
      W!=pNew+oldShift+compositeShift||Ex!=compositeShift||
      positive>stageFirst+stageRepeat+jointPositive)))
    throw runtime_error("combined ledger mismatch");
  if ((X==256&&(W!=10222||Ex!=500||H!=163||F!=128||Z!=233))||
      (X==512&&(W!=20048||Ex!=948||H!=265||F!=265||Z!=265))||
      (X==1024&&(W!=39940||Ex!=1164||H!=640||F!=577||Z!=778))||
      (X==4096&&(W!=399142||H!=5391||F!=4823||Z!=6751))||
      (X==16384&&(W!=2915326||H!=31042||F!=25450||Z!=47482)))
    throw runtime_error("historical regression failed");
  cout<<"LEDGER_PASS X="<<X<<" B="<<B<<" stageScanned="<<stageScanned<<" W="<<W<<" firstW="<<Fw
      <<" repeatW="<<Rw<<" nonlinear="<<Ex<<" pairUpper="<<PairCap<<" events="<<events
      <<" compositeEvents="<<composites<<" highH="<<H<<" highF="<<F
      <<" highZ="<<Z<<" stagePositive="<<positive<<" stageNegative="<<negative
      <<" stageFirst="<<stageFirst<<" stageRepeat="<<stageRepeat
      <<" interactionPositive="<<jointPositive<<" stageBound="
      <<stageFirst+stageRepeat+jointPositive<<" stageNew="<<pNew
      <<" oldDisplacement="<<oldShift<<" excessDisplacement="<<compositeShift<<"\n";
}
int main(int argc,char**argv) {
  if (argc<2) return 2;
  int largest=0;
  for (int i=1;i<argc;++i) {
    int X=atoi(argv[i]);
    if (X<256||X>262144||X%4) return 2;
    largest=max(largest,X);
  }
  sieve(8*largest+1000);
  for (int i=1;i<argc;++i) audit(atoi(argv[i]));
}
