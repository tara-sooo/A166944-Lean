// Exact 4-residue old-squarefree-wheel G_L(u)^2 moments for early p regeneration.
// Build: g++ -O3 -std=c++17 research/four_residue_squarefree_growth_moment_audit.cpp -o /tmp/four_moment
// Run: /tmp/four_moment 4096 ; /tmp/four_moment 16384 ; /tmp/four_moment 65536
// Finite observations, NOT a uniform-in-X theorem or twin prime proof.
#include <bits/stdc++.h>
using namespace std;
using i64=long long;
static vector<int> spf;
static vector<int> distinct_factors(int n) {
  vector<int> v;
  while(n>1) {
    int p=spf[n];v.push_back(p);
    do {n/=p;} while(n%p==0);
  }
  return v;
}
static i64 next_hit(i64 pos,int p,i64 residue) {
  i64 m=2LL*p,d=(residue-pos)%m;
  if(d<=0)d+=m;
  return pos+d;
}
static int squarefree_growth(int M,int maxPrime) {
  i64 start=M+2,K=(7LL*M-1)/4,pos=start,C=2LL*M-2;
  while(pos<K) {
    i64 nxt=K+1;
    for(int p:distinct_factors(int(C-1)))
      if(p<=maxPrime)nxt=min(nxt,next_hit(pos,p,0));
    for(int p:distinct_factors(int(C+1)))
      if(p<=maxPrime)nxt=min(nxt,next_hit(pos,p,p+2));
    if(nxt>K)break;
    int g=int(gcd((nxt&1)?nxt-2:nxt,(nxt&1)?C+1:C-1));
    int e=1;
    for(int p:distinct_factors(g))if(p<=maxPrime)e*=p;
    if(e<=1)throw runtime_error("not exact first nonunit hit");
    C+=e-1;pos=nxt;
  }
  return int(C-(2LL*M-2));
}
int main(int argc,char**argv) {
  int X=argc>1?atoi(argv[1]):4096;
  if(X!=4096 && X!=16384 && X!=65536)return 2;
  int B=int(ceil(sqrt(7.0*X))),limit=7*X+10000;
  spf.resize(limit);
  iota(spf.begin(),spf.end(),0);
  for(int p=2;1LL*p*p<limit;p++)if(spf[p]==p)
    for(int k=p*p;k<limit;k+=p)if(spf[k]==k)spf[k]=p;
  vector<int> primes;
  for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);
  long double bestRatio=-1;
  int bestP=0,bestCount=0; i64 bestMoment=0;
  for(size_t j=0;j<primes.size();++j) {
    int p=primes[j], oldPrime=j?primes[j-1]:1;
    if(p<11)continue;
    int count=0; i64 sumSq=0;
    for(int u=X+1;u<2*X+7*B/12+5;u+=2) {
      int r=u%p;
      if(r!=0 && r!=1 && r!=3 && r!=5)continue;
      int h=squarefree_growth(u,oldPrime);
      sumSq+=1LL*h*h;
      ++count;
    }
    long double ratio=(long double)sumSq*p/((long double)X*B*B);
    if(ratio>bestRatio) {
      bestRatio=ratio;bestP=p;bestMoment=sumSq;bestCount=count;
    }
  }
  if((X==4096 && (B!=170 || bestP!=167 || bestMoment!=6500616 || bestCount!=49))
    ||(X==16384 && (B!=339 || bestP!=257 || bestMoment!=109069248 || bestCount!=131))
    ||(X==65536 && (B!=678 || bestP!=587 || bestMoment!=305057696 || bestCount!=224)))
    throw runtime_error("finite 4-residue second-moment regression mismatch");
  cout<<setprecision(8)<<"PASS X="<<X<<" B="<<B
      <<" max_p*T/(X*B^2)="<<(double)bestRatio
      <<" at p="<<bestP<<" T="<<bestMoment
      <<" #target_starts="<<bestCount<<"\n"
      <<"Uniform restricted growth L2 estimate OPEN; twin-prime infinitude OPEN\n";
}
