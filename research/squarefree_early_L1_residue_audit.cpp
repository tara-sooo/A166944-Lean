// A166944 exact squarefree-prefix first moments over 4 regeneration residues.
// Build: g++ -std=c++17 -O3 research/squarefree_early_L1_residue_audit.cpp -o l1_audit
// Run: ./l1_audit 4096 ; ./l1_audit 16384 ; ./l1_audit 65536
// Finite arithmetic observations only, not a bound as X->infinity.
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
vector<int> spf;
vector<int> fac(int n) {
  vector<int> o;
  while(n>1) {
    int p=spf[n];o.push_back(p);
    do { n/=p; } while(n%p==0);
  }
  return o;
}
ll next_hit(ll pos,int p,int r) {
  ll d=(r-pos)%(2LL*p);
  if(d<=0)d+=2LL*p;
  return pos+d;
}
int growth(int m,int P) {
  ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;
  while(pos<K) {
    ll n=K+1;
    for(int p:fac(int(C-1)))if(p<=P)n=min(n,next_hit(pos,p,0));
    for(int p:fac(int(C+1)))if(p<=P)n=min(n,next_hit(pos,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
    for(int p:fac(raw))if(p<=P)e*=p;
    if(e<=1)throw runtime_error("wrong first event");
    C+=e-1;pos=n;
  }
  return int(C-(2LL*m-2));
}
int main(int argc,char**argv) {
  int X=argc>1?atoi(argv[1]):4096;
  if(X!=4096 && X!=16384 && X!=65536)return 2;
  int B=int(ceil(sqrt(7.0*X))),Z=7*X+10000;
  spf.resize(Z);
  iota(spf.begin(),spf.end(),0);
  for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)
    for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;
  ll bestSum=0;int bestP=0,bestCount=0,stages=0;
  double bestRatio=-1,averaged=0;
  int upper=2*X+7*B/12+4;
  for(int p=11;p<=B;p+=2)if(spf[p]==p) {
    int prev=1;
    for(int j=3;j<p;j+=2)if(spf[j]==j)prev=j;
    ll sum=0;int count=0;
    for(int u=X+1;u<upper;u+=2) {
      int r=u%p;
      if(r!=0 && r!=1 && r!=3 && r!=5)continue;
      int h=growth(u,prev);
      sum+=h;++count;
    }
    double R=double(p)*sum/(double(X)*B);
    averaged+=R;++stages;
    if(R>bestRatio){bestRatio=R;bestP=p;bestSum=sum;bestCount=count;}
  }
  const struct {int x,b,n,p,sum,count;} regression[]={
    {4096,170,35,149,13330,56},
    {16384,339,64,269,56968,124},
    {65536,678,119,619,148714,215}
  };
  for(auto q:regression)if(X==q.x)
    if(B!=q.b||stages!=q.n||bestP!=q.p
        ||bestSum!=q.sum||bestCount!=q.count)
      throw runtime_error("four-AP L1 exact regression changed");
  cout<<setprecision(11)<<"PASS X="<<X<<" B="<<B
      <<" prime_stages="<<stages
      <<" max_p_times_AP_L1_over_XB="<<bestRatio
      <<" at_p="<<bestP<<" total_growth="<<bestSum
      <<" #old_wheel_targets="<<bestCount
      <<" mean_normalized_ratio="<<averaged/stages<<"\n";
  cout<<"Uniform dyadic four-AP L1 bound remains OPEN\n";
}
