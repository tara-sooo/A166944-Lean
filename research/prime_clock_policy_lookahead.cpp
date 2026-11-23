// Controlled clipped prime clock: pick a nonunit squarefree divisor of the tied event product.
// Two one-step greedy controls: fewest next active primes; longest next clock gap.
#include <algorithm>
#include <cmath>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
vector<int>spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int k=p*p;k<n;k+=p)if(spf[k]==k)spf[k]=p;}
vector<int>fac(int n){vector<int>f;while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
ll gap(ll t,int p,int r){ll x=(r-t)%(2LL*p);return x>0?x:x+2LL*p;}
struct Entry{ll n;int active;};
Entry next(ll t,ll C,ll K,int B){ll n=K+1;int ac=0;for(int p:fac((int)(C-1)))if(p<=B){ac++;n=min(n,t+gap(t,p,0));}for(int p:fac((int)(C+1)))if(p<=B){ac++;n=min(n,t+gap(t,p,p+2));}return {n,ac};}
struct Stats{ll good=0,bad=0,events=0,growth=0,ownerF=0,ownerR=0,selectedF=0,selectedR=0,sinks=0,maxR=0,choices=0,compound=0;int badWitness=0;};
int main(int argc,char**argv){if(argc<2)return 2;int MX=0;for(int i=1;i<argc;i++)MX=max(MX,atoi(argv[i]));sieve(8*MX+500);
for(int ai=1;ai<argc;ai++){int X=atoi(argv[ai]),B=ceil(sqrt(7.*X));Stats total[5];
 for(int M=X+1;M<2*X;M+=2){ll K=(7LL*M-1)/4;
  for(int policy=0;policy<5;policy++){ll t=M+2,C=2LL*M-2;vector<char>owned(B+1),selectedOwned(B+1);int ret=0;
   while(t<K){auto entry=next(t,C,K,B);ll n=entry.n;if(n>K)break;
    int raw=gcd((int)((n&1)?n-2:n),(int)((n&1)?C+1:C-1));vector<int>chosenps;
    for(int p:fac(raw))if(p<=B)chosenps.push_back(p);
    if(chosenps.empty())throw runtime_error("no factors");
    int full=1;for(int p:chosenps)full*=p;
    if(chosenps.size()>15)throw runtime_error("too many ties");
    int owner=0;for(int p:chosenps)if(p>=11){owner=p;break;}
    if(owner){if(owned[owner]){total[policy].ownerR++;ret++;}else{owned[owner]=1;total[policy].ownerF++;}}
    int d=policy==0?full:policy==1?chosenps.front():policy==2?chosenps.back():0;
    if(policy>=3){int best=1000000000;ll topgap=-1;for(int mask=1;mask<(1<<chosenps.size());mask++){
       int candidate=1;for(int j=0;j<int(chosenps.size());j++)if(mask&(1<<j))candidate*=chosenps[j];
       ll state=C+candidate-1;
       if(state>2*n)throw runtime_error("cone issue candidate");
       auto future=next(n,state,K,B);ll wait=future.n-n;
       if(policy==3){if(future.active<best||(future.active==best && candidate<d)){best=future.active;d=candidate;}}
       else {if(wait>topgap||(wait==topgap && (d==0||candidate<d))){topgap=wait;d=candidate;}}
      }
    }
    if(d<=1||full%d)throw runtime_error("selection invalid");
    int selectedOwner=0;for(int p:chosenps)if(p>=11&&d%p==0){selectedOwner=p;break;}
    if(selectedOwner){if(selectedOwned[selectedOwner])total[policy].selectedR++;else{selectedOwned[selectedOwner]=1;total[policy].selectedF++;}}
    if(chosenps.size()>1)total[policy].choices++;
    total[policy].compound+=d!=chosenps.front()&&d!=chosenps.back();
    C+=d-1;t=n;if(C>2*n)throw runtime_error("new state beyond cone");
    total[policy].events++;total[policy].growth+=d-1;
   }
   bool pair=(spf[(int)(C-1)]==C-1&&spf[(int)(C+1)]==C+1);
   total[policy].good+=pair;total[policy].bad+=!pair;total[policy].maxR=max(total[policy].maxR,(ll)ret);
   if(!pair&&!total[policy].badWitness)total[policy].badWitness=M;
  }
 }
 for(int i=0;i<5;i++){const Stats z=total[i];cout<<"LOOKAHEAD_PASS X="<<X<<" B="<<B<<" policy="<<(i==0?"PRODUCT":i==1?"MIN":i==2?"MAX":i==3?"MIN_ACTIVE":"MAX_WAIT")<<" good="<<z.good<<" bad="<<z.bad<<" badWitness="<<z.badWitness<<" meanEvents="<<double(z.events)/(X/2)<<" meanGrowth="<<double(z.growth)/(X/2)<<" meanR="<<double(z.ownerR)/(X/2)<<" R="<<z.ownerR<<" meanF="<<double(z.ownerF)/(X/2)<<" selectedF="<<z.selectedF<<" selectedR="<<z.selectedR<<" maxR="<<z.maxR<<" choices="<<z.choices<<" compoundSelections="<<z.compound<<"\n";}
}
}
