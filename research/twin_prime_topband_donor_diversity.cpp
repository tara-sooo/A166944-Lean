// Exact ORIGINAL squarefree parity-GCD wheel, with unique post-q-state return episode fibres.
// Build: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_topband_donor_diversity.cpp -o /tmp/top_diversity
// Run: /tmp/top_diversity 256 512 1024 2048 4096 8192 16384 32768 65536 131072 262144 524288 1048576
// Return labels are ALL q factors, including masked q and composite events; high donors are >=11.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <stdexcept>
#include <vector>
using namespace std;using ll=long long;
vector<int> spf;
void sieve(int n){spf.resize(n);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<n;p++)if(spf[p]==p)for(int j=p*p;j<n;j+=p)if(spf[j]==j)spf[j]=p;}
void factor(int n,vector<int>&fs){fs.clear();while(n>1){int p=spf.at(n);fs.push_back(p);do{n/=p;}while(n%p==0);}}
int gap(ll n,int p,int r){ll k=(r-n)%(2LL*p);return int(k>0?k:k+2*p);}
struct Event{int t;int C;vector<int>fac;};
void run(int X){int B=int(ceill(sqrtl(7.L*X)));ll total=0,firsts=0;int maxFirstTagOffset=0,maxReturnTagOffset=0;ll with[5]{};int minDistinct=100000,maxDistinct=0;int minDonor=100000,maxDonor=0;ll qMin[4]{};vector<int> fs;map<tuple<int,int,int,int>,int> episodeFibre;
for(int M=X+1;M<2*X;M+=2){ll t=M+2,C=2LL*M-2,K=(7LL*M-1)/4;vector<Event> events;vector<int> last(B+1,-1);
while(t<K){ll n=K+1;factor(int(C-1),fs);for(int p:fs)if(p<=B)n=min(n,t+gap(t,p,0));factor(int(C+1),fs);for(int p:fs)if(p<=B)n=min(n,t+gap(t,p,p+2));if(n>K)break;int a=(n&1)?int(n-2):int(n), b=(n&1)?int(C+1):int(C-1);factor(gcd(a,b),fs);int d=1;for(int p:fs)if(p<=B)d*=p;if(d<=1)throw runtime_error("bad event");C+=d-1;t=n;events.push_back({int(t),int(C),{}});auto &f=events.back().fac;for(int p:fs)if(p<=B)f.push_back(p);
int idx=int(events.size())-1;
for(int q:f)if(q>=11 && 2*q>=B){total++;if(last[q]==-1)firsts++;else {set<int> donor;int m=0;for(int j=last[q]+1;j<idx;j++){bool high=false;for(int r:events[j].fac)if(r>=11){donor.insert(r);high=true;}m+=high;}int distinct=int(donor.size());maxFirstTagOffset=max(maxFirstTagOffset,events[last[q]].t-M);maxReturnTagOffset=max(maxReturnTagOffset,events[idx].t-M);episodeFibre[{q,events[last[q]].t,events[last[q]].C,events[idx].t}]++;int cls=min(distinct,4);with[cls]++;if(distinct<minDistinct){minDistinct=distinct;}maxDistinct=max(maxDistinct,distinct);minDonor=min(minDonor,m);maxDonor=max(maxDonor,m);if(distinct==1){int r=*donor.begin();if(r<q)qMin[0]++;else if(r>q)qMin[1]++;else qMin[2]++;}if(distinct>=2){qMin[3]++;}}last[q]=idx;}
}
}
int maxEpisodeFibre=0;for(const auto &it:episodeFibre)maxEpisodeFibre=max(maxEpisodeFibre,it.second);
 if(X==2048&&(total!=356||firsts!=332||episodeFibre.size()!=1||maxEpisodeFibre!=24))throw runtime_error("regression X2048");
 if(X==16384&&(total!=2147||firsts!=2139||episodeFibre.size()!=1||maxEpisodeFibre!=8))throw runtime_error("regression X16384");
 if(X==65536&&(total!=8585||firsts!=8585))throw runtime_error("regression X65536");
 if(X==262144&&(total!=29749||firsts!=29749))throw runtime_error("regression X262144");
 if(X==524288&&(total!=44798||firsts!=44767||episodeFibre.size()!=1||maxEpisodeFibre!=31))throw runtime_error("regression X524288");
 if(X==1048576&&(total!=99276||firsts!=99271||episodeFibre.size()!=2||maxEpisodeFibre!=4))throw runtime_error("regression X1048576");
 if(minDonor==100000)minDonor=0;
 cout<<"DONOR_DIVERSITY_PASS X="<<X<<" B="<<B<<" top_incidence="<<total<<" first="<<firsts<<" returns="<<total-firsts<<" distinct_high_donors_0="<<with[0]<<" 1="<<with[1]<<" 2="<<with[2]<<" 3="<<with[3]<<" 4plus="<<with[4]<<" min_high_event_count="<<minDonor<<" max_high_event_count="<<maxDonor<<" one_donor_smaller="<<qMin[0]<<" one_donor_larger="<<qMin[1]<<" 2plus="<<qMin[3]<<" distinct_episode_classes="<<episodeFibre.size()<<" max_episode_fibre="<<maxEpisodeFibre<<" max_tag_offset="<<maxFirstTagOffset<<" max_return_offset="<<maxReturnTagOffset<<"\n";
}
int main(int argc,char**argv){if(argc<2)return 1;int mx=0;for(int i=1;i<argc;i++){int X=atoi(argv[i]);if(X<256||X>1048576||X%4)return 2;mx=max(mx,X);}sieve(8*mx+100);for(int i=1;i<argc;i++)run(atoi(argv[i]));}
