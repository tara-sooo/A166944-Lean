// Original full clipped parity GCD wheel: classify consecutive q-return
// excursions by intervening donor events with exactly one foreign high prime.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_linear_donor_word_audit.cpp -o /tmp/linear
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int z=p*p;z<n;z+=p)if(spf[z]==z)spf[z]=p;}
static vector<int> factors(int n){vector<int> f;while(n>1){int p=spf[n];f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
static int gap(ll t,int p,int r){ll g=(r-t)%(2LL*p);return int(g>0?g:g+2*p);}
int main(int argc,char** argv){
 if(argc<2)return 2;
 int mx=0;for(int i=1;i<argc;i++)mx=max(mx,atoi(argv[i]));sieve(8*mx+300);
 for(int ai=1;ai<argc;ai++){
  int X=atoi(argv[ai]),B=int(ceill(sqrtl(7.L*X)));
  ll count=0,zero=0,linear=0,nonlinear=0;
  ll m0=0,m1=0,m2=0,m3=0;
  for(int M=X+1;M<2*X;M+=2){
   ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
   vector<vector<int>> hs;vector<int> last(B+1,-1);
   while(t<K){ll n=K+1;
    for(int p:factors(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
    for(int p:factors(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;
    vector<int> here;
    for(int p:factors(raw))if(p<=B){d*=p;if(p>=11)here.push_back(p);}
    if(d<=1)return 3;
    for(int q:here){int prev=last[q];if(prev>=0){
       count++;int donors=0;bool compositeHigh=false;
       for(int j=prev+1;j<int(hs.size());j++)if(!hs[j].empty()){
        donors++;if(hs[j].size()>1)compositeHigh=true;
       }
       if(!donors){zero++;m0++;}
       else{
        if(compositeHigh)nonlinear++;else linear++;
        if(donors==1)m1++;else if(donors==2)m2++;else m3++;
       }
      }last[q]=int(hs.size());
    }
    hs.push_back(here);C+=d-1;t=n;
   }
  }
  if(count!=zero+linear+nonlinear||count!=m0+m1+m2+m3)return 4;
  cout<<"DONOR_LINEAR_PASS X="<<X<<" B="<<B<<" returns="<<count<<" zero="<<zero
      <<" highSingleFactorOnly="<<linear<<" hasHighComposite="<<nonlinear
      <<" donors1="<<m1<<" donors2="<<m2<<" donors3plus="<<m3<<"\n";
 }
}
