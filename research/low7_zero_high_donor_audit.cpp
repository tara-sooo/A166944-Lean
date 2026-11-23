// Exact original final-squarefree B wheel: consecutive q-hit returns WITHOUT
// an intervening event carrying another high prime >=11.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low7_zero_high_donor_audit.cpp -o /tmp/zero
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>
using namespace std;
using ll = long long;
static vector<int> spf;
static void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int v=p*p;v<n;v+=p)if(spf[v]==v)spf[v]=p;}
static vector<int> factors(int n){vector<int> f;while(n>1){int p=spf[n];f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
static int gap(ll t,int p,int r){ll g=(r-t)%(2LL*p);return int(g>0?g:g+2*p);}
int main(int argc,char **argv){
  if(argc<2)return 2;
  int maxX=0;for(int i=1;i<argc;i++)maxX=max(maxX,atoi(argv[i]));
  sieve(8*maxX+100);
  const vector<int> exceptional={11,13,17,19,23,29,31,37,41,43,101,103,107};
  for(int ai=1;ai<argc;ai++){
    int X=atoi(argv[ai]),B=int(ceil(sqrtl(7.L*X)));map<int,ll> counts;
    ll total=0,highEvents=0;
    for(int M=X+1;M<2*X;M+=2){
      ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;
      vector<int> last(B+1,-1);
      vector<vector<int>> labels;
      while(t<K){ll n=K+1;
        for(int p:factors(int(C-1)))if(p<=B)n=min(n,t+gap(t,p,0));
        for(int p:factors(int(C+1)))if(p<=B)n=min(n,t+gap(t,p,p+2));
        if(n>K)break;
        int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));int d=1;
        vector<int> high;
        for(int p:factors(raw))if(p<=B){d*=p;if(p>=11)high.push_back(p);}
        if(d<=1){cerr<<"bad empty event\n";return 3;}
        for(int q:high){if(last[q]>=0){bool donor=false;
          for(int j=last[q]+1;j<int(labels.size());j++)if(!labels[j].empty()){donor=true;break;}
          if(!donor){counts[q]++;total++;if(!binary_search(exceptional.begin(),exceptional.end(),q)){
              cerr<<"COUNTEREXAMPLE q="<<q<<" M="<<M<<"\n";return 4;}
          }
        } last[q]=int(labels.size());}
        labels.push_back(high);if(!high.empty())highEvents++;
        C+=d-1;t=n;
      }
    }
    cout<<"ZERO_HIGH_DONOR_PASS X="<<X<<" B="<<B<<" total="<<total<<" highEvents="<<highEvents<<" qs=";
    for(const auto &e:counts)cout<<e.first<<":"<<e.second<<",";
    cout<<"\n";
  }
}
