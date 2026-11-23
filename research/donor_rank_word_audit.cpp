// Original final clipped GCD wheel. Counts q-return donor-word modular rank.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/donor_rank_word_audit.cpp -o /tmp/donor_rank
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
static vector<int>spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
static vector<int> fac(int n){vector<int>f;while(n>1){int p=spf[n];f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
static int gap(ll t,int p,int r){ll v=(r-t)%(2LL*p);return int(v>0?v:v+2*p);}
struct E{int t,d;vector<int>hi;};
struct S{ll total=0,zero=0,linear=0,nonlinear=0,nontrivial=0,degenerate=0,singleton=0,shortWord=0,donors=0,largeWord=0;int largestM=0,witnessM=0,witnessQ=0,witnessWord=0;};
int main(int argc,char**argv){if(argc<2)return 2;int mx=0;for(int i=1;i<argc;i++)mx=max(mx,atoi(argv[i]));sieve(8*mx+300);
 for(int ai=1;ai<argc;ai++){
 int X=atoi(argv[ai]);int B=int(ceill(sqrtl(7.L*X)));S res[3];
 for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;vector<E>es;vector<int>last(B+1,-1);
 while(t<K){ll n=K+1;for(int p:fac(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));for(int p:fac(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;
  int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;vector<int>h;
  for(int p:fac(raw))if(p<=B){d*=p;if(p>=11)h.push_back(p);}
  if(d<=1)throw runtime_error("event d=1");
  for(int q:h){int prev=last[q];if(prev>=0){S&st=res[4*q<B?0:2*q<B?1:2];st.total++;
    int m=0,L=0,Egrowth=0;bool nonlinear=false;map<int,int>coeff,occ;
    for(int k=prev+1;k<(int)es.size();k++){
      const E&e=es[k];Egrowth+=e.d-1;
      if(e.hi.empty()){L+=e.d-1;continue;}
      m++;if(e.hi.size()>1){nonlinear=true;continue;}
      int r=e.hi[0],a=e.d/r;if(a<1||a>105||105%a)throw runtime_error("a not 105 divisor");
      coeff[r]+=a;occ[r]++;
    }
    if(m==0){st.zero++;}
    else if(nonlinear){st.nonlinear++;}
    else{st.linear++;st.donors+=m;
       int c=(es[prev].t%2==0)?((n%2==0)?1:-1):((n%2==0)?3:1);
       if(((Egrowth-c)%q+q)%q)throw runtime_error("q-growth congruence mismatch");
       int D=L-m-c;for(auto [r,a]:coeff)D+=r*a;
       if(((D%q)+q)%q)throw runtime_error("linear donor congruence mismatch");
       bool single=false,nonzero=false;for(auto [r,a]:coeff){if(occ[r]==1)single=true;if(a%q)nonzero=true;}
       if(single)st.singleton++;
       if(nonzero)st.nontrivial++;
       else{st.degenerate++;if(!st.witnessM){st.witnessM=M;st.witnessQ=q;st.witnessWord=m;}}
       if(105LL*m<q){st.shortWord++;if(!nonzero)throw runtime_error("shortWord degenerate");}
       if(m>st.largestM)st.largestM=m;
       if(105LL*m>=q)st.largeWord++;
    }
   }last[q]=es.size();}
  C+=d-1;t=n;es.push_back({int(n),d,h});
 }
 }
 cout<<"DONOR_RANK_PASS X="<<X<<" B="<<B;
 ll totals=0;
 for(int i=0;i<3;i++){S &s=res[i];if(s.total!=s.zero+s.linear+s.nonlinear||s.linear!=s.nontrivial+s.degenerate)throw runtime_error("bad accounting");totals+=s.total;
  cout<<" band="<<i<<"[total="<<s.total<<",zero="<<s.zero<<",linear="<<s.linear<<",nonlinear="<<s.nonlinear<<",nontrivial="<<s.nontrivial<<",degenerate="<<s.degenerate<<",singleton="<<s.singleton<<",short="<<s.shortWord<<",large="<<s.largeWord<<",max_m="<<s.largestM<<",witness="<<s.witnessM<<":"<<s.witnessQ<<":"<<s.witnessWord<<"]";
 }
 if(X==4096 && totals!=2034)throw runtime_error("X4096 regression");
 if(X==16384 && totals!=17717)throw runtime_error("X16384 regression");
 if(X==65536 && totals!=84076)throw runtime_error("X65536 regression");
 if(X==262144 && totals!=499788)throw runtime_error("X262144 regression");
 cout<<"\n";
 }
}
