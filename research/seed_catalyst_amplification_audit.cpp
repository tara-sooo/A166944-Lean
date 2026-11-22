// A166944 squarefree wheel: exact canonical seed-catalyst amplification audit.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror seed_catalyst_amplification_audit.cpp -o audit
// for X in 512 1024 4096 8192 16384 32768 65536 131072 262144; do ./audit "$X"; done
// Finite computation; neither the asymptotic amplification bound nor twin primes are proved.
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
vector<int> spf,ps;
vector<int> factors(int n){vector<int> v;while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}return v;}
ll next_hit(ll at,int p,ll residue){ll d=(residue-at)%(2LL*p);if(d<=0)d+=2LL*p;return at+d;}
ll jump_growth(int M,int B){
 ll at=M+2,K=(7LL*M-1)/4,C=2LL*M-2,initial=C;
 while(at<K){ll n=K+1;
  for(int p:factors(int(C-1)))if(p<=B)n=min(n,next_hit(at,p,0));
  for(int p:factors(int(C+1)))if(p<=B)n=min(n,next_hit(at,p,p+2));
  if(n>K)break;
  int raw=gcd(int((n&1)?n-2:n),int((n&1)?C+1:C-1)),d=1;
  for(int p:factors(raw))if(p<=B)d*=p;
  if(d==1)throw runtime_error("jump event did not increase growth");
  C+=d-1;at=n;
 }
 return C-initial;
}
ll literal_growth(int M,int B){ll C=2LL*M-2,K=(7LL*M-1)/4,initial=C;
 for(ll n=M+3;n<=K;n++){
  int raw=gcd(int((n&1)?n-2:n),int((n&1)?C+1:C-1)),d=1;
  for(int p:factors(raw))if(p<=B)d*=p;
  C+=d-1;
 }
 return C-initial;
}
int power_mod(int a,int b,int mod){ll v=1,x=a;while(b){if(b&1)v=v*x%mod;x=x*x%mod;b>>=1;}return int(v);}
ll residue_count(ll N,int r,int p){return r<N?1+(N-1-r)/p:0;}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 int X=atoi(argv[1]);
 if(X<256||X>262144||(X&1))return 2;
 int B=int(ceil(sqrt(7.0*X))),Z=8*X+1000;
 spf.resize(Z);iota(spf.begin(),spf.end(),0);
 for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;
 for(int p=3;p<=B;p+=2)if(spf[p]==p)ps.push_back(p);
 for(int M=7;M<=119;M+=2)if(jump_growth(M,B)!=literal_growth(M,B))throw runtime_error("literal step mismatch");
 ll N=X/2,R=0,W=0,exceptional=0,zeros=0,maxRatioM=0,maxRatioW=0,maxRatioG=0;
 ll maxBadWeight=0,maxBadM=0,lowCount=0,lowGrowth=0;
 long double maxRatio=0,energy=0,highEnergy=0;
 long double logX=log((long double)X), lowCut=logX*logX;
 for(int M=X+1;M<2*X;M+=2){
  ll C0=2LL*M-2,w=0;
  for(int p:ps)if((C0-1)%p==0||(C0+1)%p==0)w+=p-1;
  ll g=jump_growth(M,B);
  if(g<0||g>3LL*X||(!w&&g))throw runtime_error("growth/support/horizon invariant failure");
  if(g>1LL*B*w){
   exceptional++;
   if(w>maxBadWeight){maxBadWeight=w;maxBadM=M;}
  }
  if(w<=lowCut){lowCount++;lowGrowth+=g;}
  else highEnergy+=(long double)g*g/w;
  if(w){energy+=(long double)g*g/w;
   if((long double)g/w>maxRatio){maxRatio=(long double)g/w;maxRatioM=M;maxRatioW=w;maxRatioG=g;}}
  else zeros++;
  R+=w;W+=g;
 }
 // Independently count initial root weights using the two modular classes in j=(M-X-1)/2.
 ll Rmod=0;
 for(int p:ps){int inverse4=power_mod(4,p-2,p);
  int a=int(((ll)(p-(2LL*X-1)%p)*inverse4)%p);
  int b=int(((ll)(p-(2LL*X+1)%p)*inverse4)%p);
  if(a==b)throw runtime_error("distinct root classes collapsed");
  Rmod+=(p-1LL)*(residue_count(N,a,p)+residue_count(N,b,p));
 }
 if(Rmod!=R)throw runtime_error("independent CRT root total mismatch");
 if(W>1LL*B*R+3LL*X*exceptional)throw runtime_error("exceptional decomposition inequality failed");
 struct Expected{int X;ll R,W,E;} expected[]={
  {512,7544,20048,6},{1024,21450,39940,5},
  {4096,149886,399142,29},{8192,406116,1084898,57},
  {16384,1072888,2915326,79},{32768,2929084,6569168,91},
  {65536,7889844,19826998,219},{131072,20881044,45835016,212},
  {262144,56172030,138903880,446}};
 for(auto r:expected)if(X==r.X&&(R!=r.R||W!=r.W||exceptional!=r.E))throw runtime_error("root amplification regression failed");
 cout<<fixed<<setprecision(7)<<"PASS X="<<X<<" B="<<B<<" starts="<<N
     <<" initial_weight="<<R<<" full_growth="<<W<<" ratio="<<(double)W/R
     <<" exceptions_G_gt_Bw="<<exceptional<<" exception_share="<<(double)exceptional/N
     <<" initial_no_root="<<zeros<<" weighted_energy="<<(double)energy
     <<" energy_over_XB2="<<(double)(energy/(X*1.L*B*B))
     <<" max_G_over_w="<<(double)maxRatio<<" worst_M="<<maxRatioM
     <<" worst_w="<<maxRatioW<<" worst_G="<<maxRatioG
     <<" max_bad_weight="<<maxBadWeight<<" max_bad_at_M="<<maxBadM
     <<" low_count="<<lowCount<<" low_growth="<<lowGrowth
     <<" high_energy_over_XB2="<<(double)(highEnergy/(X*1.L*B*B))<<"\n";
}
