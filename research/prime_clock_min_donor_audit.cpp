// MIN-PRIME controlled squarefree clipped GCD wheel: all event gains p-1 (p prime).
// Verify LOW7 blocks have growth <=34, repeated-q donor words are ALWAYS linear.
#include <algorithm>
#include <cmath>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
vector<int>spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
vector<int>factors(int n){vector<int>v;while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}return v;}
ll gap(ll t,int p,int r){ll z=(r-t)%(2LL*p);return z>0?z:z+2LL*p;}
struct Ev{int t,p;};
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;for(int i=1;i<argc;i++)mx=max(mx,atoi(argv[i]));sieve(8*mx+500);
 for(int ai=1;ai<argc;ai++){int X=atoi(argv[ai]),B=ceil(sqrt(7.*X));ll F=0,R=0,events=0,m0=0,m1=0,m2=0,m3=0,oneDonorTop=0,oneDonorTopNear=0,largeQWithoutDonor=0,topR=0,meanG=0,maxR=0;
  for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;vector<int>last(B+1,-1);vector<Ev>es;int localR=0;
   while(t<K){ll n=K+1;for(int p:factors((int)(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));for(int p:factors((int)(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
    int raw=gcd((int)((n&1)?n-2:n),(int)((n&1)?C+1:C-1));int chosen=0;for(int p:factors(raw))if(p<=B){chosen=p;break;}
    if(!chosen)throw runtime_error("no chosen prime");
    int idx=es.size();
    if(chosen>=11){int before=last[chosen];if(before<0)F++;else{R++;localR++;if(2*chosen>=B)topR++;
      int m=0,L=0,sumHigh=0,onlyR=0;for(int k=before+1;k<idx;k++){int p=es[k].p;if(p>=11){m++;sumHigh+=p;onlyR=p;}else L+=p-1;}
      if(L>34LL*(m+1))throw runtime_error("LOW7 block growth exceeded 34");
      int c=es[before].t%2==0 ? (n%2==0?1:-1) : (n%2==0?3:1);
      int E=sumHigh-m+L;
      if((E-c)%chosen)throw runtime_error("q reset congruence");
      if(m==0){m0++;if(chosen>=37){largeQWithoutDonor++;throw runtime_error("q>=37 repeated without foreign high donation");}}
      else if(m==1){m1++;if(2*chosen>B+68){oneDonorTop++;if(chosen-onlyR< -4||chosen-onlyR>68)throw runtime_error("near-prime donor");oneDonorTopNear++;}}
      else if(m==2)m2++;else m3++;
     }last[chosen]=idx;}
    C+=chosen-1;t=n;es.push_back({(int)n,chosen});events++;if(C>2*n)throw runtime_error("cone bound failed");
   }
   meanG+=C-(2LL*M-2);maxR=max(maxR,(ll)localR);
  }
  if(F+R>events)throw runtime_error("bad high ledger");
  if(R!=m0+m1+m2+m3)throw runtime_error("donor ledger");
  cout<<"MIN_DONOR_PASS X="<<X<<" B="<<B<<" F="<<F<<" R="<<R<<" R_over_F="<<double(R)/F<<" meanGrowth="<<double(meanG)/(X/2)<<" events="<<events<<" m0="<<m0<<" m1="<<m1<<" m2="<<m2<<" m3plus="<<m3<<" topR="<<topR<<" oneDonorTopNear="<<oneDonorTopNear<<" oneDonorTopTotal="<<oneDonorTop<<" q>=37_m0="<<largeQWithoutDonor<<" maxR="<<maxR<<"\n";
 }
}