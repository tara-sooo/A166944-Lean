// A166944 squarefree clipped parity-GCD: preload initially inactive primes at zero cost.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror seed_catalyst_preload_audit.cpp -o /tmp/seed_catalyst_preload_audit
// /tmp/seed_catalyst_preload_audit 4096
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
vector<int> spf;
vector<int> factors(int a){vector<int> r;while(a>1){int p=spf.at(a);r.push_back(p);do{a/=p;}while(a%p==0);}return r;}
ll firstAfter(ll pos,int p,ll residue){ll d=(residue-pos)%(2LL*p);if(d<=0)d+=2LL*p;return pos+d;}
int growth(int M,const vector<unsigned char>& mask){ll C=2LL*M-2,pos=M+2,K=(7LL*M-1)/4;
 while(pos<K){ll n=K+1;for(int p:factors(int(C-1)))if(p<(int)mask.size()&&mask[p])n=min(n,firstAfter(pos,p,0));for(int p:factors(int(C+1)))if(p<(int)mask.size()&&mask[p])n=min(n,firstAfter(pos,p,p+2));if(n>K)break;
 int d=1;ll raw=gcd((n&1)?n-2:n,(n&1)?C+1:C-1);for(int p:factors(int(raw)))if(p<(int)mask.size()&&mask[p])d*=p;
 if(d<=1)throw runtime_error("invalid first-event jump");
 pos=n;C+=d-1;}
 return int(C-(2LL*M-2));}
int literal(int M,const vector<unsigned char>& mask){ll C=2LL*M-2,K=(7LL*M-1)/4;for(ll n=M+3;n<=K;n++){ll raw=gcd((n&1)?n-2:n,(n&1)?C+1:C-1);int d=1;for(int p:factors(int(raw)))if(p<(int)mask.size()&&mask[p])d*=p;C+=d-1;}return int(C-(2LL*M-2));}
int main(int argc,char**argv){int X=argc>1?atoi(argv[1]):4096;if(X<256||X>65536||X%2)return 2;
 int B=int(ceil(sqrt(7.0*X))),Z=8*X+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;
 vector<int>ps;vector<unsigned char>all(B+1);for(int p=3;p<=B;p+=2)if(spf[p]==p){ps.push_back(p);all[p]=1;}
 for(int M=7;M<=119;M+=2)if(growth(M,all)!=literal(M,all))throw runtime_error("literal gcd check failed");
 ll Wfull=0,Pseed=0,Nseed=0,seedSum=0,seedWeightSum=0,nZero=0,nOne=0,nTwo=0,nThreePlus=0,nWithNeg=0,seedStageNonzero=0,seedStageZero=0,maxSeeds=0,maxWeighted=0,firstTwinM=0;vector<ll> hist(32,0);
 for(int M=X+1;M<2*X;M+=2){int C0=2*M-2;vector<int>seed;vector<unsigned char> mask(B+1);
  int weight=0;for(int p:ps){if((C0-1)%p==0||(C0+1)%p==0){seed.push_back(p);weight+=p;}else mask[p]=1;}
  if(weight>7*B)throw runtime_error("seed prime weight bound failed");
  int before=growth(M,mask);if(before!=0)throw runtime_error("initially inactive prime preloading changed canonical path");
  int W=0,P=0,N=0;for(int p:seed){mask[p]=1;int after=growth(M,mask);int delta=after-before;if(delta>0)P+=delta;else N-=delta;if(delta==0)seedStageZero++;else seedStageNonzero++;before=after;}
  W=growth(M,all);if(before!=W||P-N!=W)throw runtime_error("seed-only chain terminal growth mismatch");
  if(seed.empty()&&!firstTwinM)firstTwinM=M;
  Wfull+=W;Pseed+=P;Nseed+=N;seedSum+=seed.size();seedWeightSum+=weight;maxSeeds=max(maxSeeds,ll(seed.size()));maxWeighted=max(maxWeighted,ll(weight));
  if(seed.size()==0)nZero++;else if(seed.size()==1)nOne++;else if(seed.size()==2)nTwo++;else nThreePlus++;
  if(N>0)nWithNeg++;
  hist.at(seed.size())++;
  if(M==4727||M==19583)cout<<"EXAMPLE M="<<M<<" seed_count="<<seed.size()<<" weight="<<weight<<" full_growth="<<W<<" seed_order_P="<<P<<" seed_order_negative="<<N<<"\n";
 }
 const struct {int X;ll W,P,Neg;ll zero,maxk;} regressions[]={{1024,39940,44044,4104,22,6},{4096,399142,452722,53580,52,7},{8192,1084898,1291454,206556,106,8},{16384,2915326,3422986,507660,192,8}};
 for(const auto& row:regressions)if(row.X==X&&(Wfull!=row.W||Pseed!=row.P||Nseed!=row.Neg||nZero!=row.zero||maxSeeds!=row.maxk))throw runtime_error("seed preload regression failed");
 cout<<"PASS X="<<X<<" B="<<B<<" starts="<<X/2<<" Wfull="<<Wfull<<" Pseed="<<Pseed<<" Negseed="<<Nseed<<" avgSeed="<<double(seedSum)/(X/2)<<" avgWeight="<<double(seedWeightSum)/(X/2)<<" maxSeed="<<maxSeeds<<" maxWeight="<<maxWeighted<<" seed0="<<nZero<<" seed1="<<nOne<<" seed2="<<nTwo<<" seed3plus="<<nThreePlus<<" startsWithNeg="<<nWithNeg<<" zeroStages="<<seedStageZero<<" nonzeroStages="<<seedStageNonzero<<" firstTwinSource="<<firstTwinM<<"\n";
 cout<<"HIST";for(size_t i=0;i<hist.size();i++)if(hist[i])cout<<" count"<<i<<"="<<hist[i];cout<<"\n";
}
