#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <vector>
using namespace std;
using I=int64_t;
struct Hit{int t,p;};
struct Wheel{int B;vector<int> spf;explicit Wheel(int X):B(int(ceil(sqrt(7.0*X)))),spf(7*X+4){for(int i=2;i<int(spf.size());++i)if(!spf[i]){spf[i]=i;if(I(i)*i<I(spf.size()))for(I j=I(i)*i;j<I(spf.size());j+=i)if(!spf[j])spf[j]=i;}} Hit hit(int t,int C,int K,const vector<int>* pool=nullptr)const{Hit best{K+1,0};for(int s:{-1,1}){int v=C+s;while(v>1){int p=spf[v];if(p>B)break;if(p>2&&(!pool||find(pool->begin(),pool->end(),p)!=pool->end())){int m=2*p,r=s==-1?0:p+2,u=t+1+(r-(t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(v%p==0)v/=p;}}return best;}};
struct Ev{int t,C,p;};
void run(int X){Wheel w(X);const int L=210,limit=4*L+10;I events=0,discoveries=0,shadowEvents=0,twoChecks=0,twoLarge=0,maxTwo=0,maxLarge=0,maxGain=0,maxSmallPair=0,six=0,nonTwin=0,less3=0;map<int,I> nlabels;
 for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4;vector<int> seen{3,5,7};vector<Ev> path,high;int firstT=t,firstC=C;while(true){Hit h=w.hit(t,C,K);if(!h.p){if(w.spf[C-1]!=C-1||w.spf[C+1]!=C+1){++nonTwin;if(seen.size()<6)++less3;}break;}path.push_back({h.t,C,h.p});if(h.p>7)high.push_back(path.back());t=h.t;C+=h.p-1;assert(C<=2*t);++events;if(find(seen.begin(),seen.end(),h.p)==seen.end()){++discoveries;seen.push_back(h.p);}}
 ++nlabels[seen.size()-3];
 // Reconstruct the prefix through the first three new high labels by adding
 // just the next discovery label to LOW+seen, with the original cutoff.
 vector<int> pool{3,5,7};t=firstT;C=firstC;size_t i=0;
 while(i<path.size()&&pool.size()<6){size_t j=i;while(j<path.size()&&find(pool.begin(),pool.end(),path[j].p)!=pool.end())++j;if(j==path.size())break;int q=path[j].p;pool.push_back(q);for(;i<=j;++i){Hit h=w.hit(t,C,K,&pool);assert(h.t==path[i].t&&h.p==path[i].p&&C==path[i].C);t=h.t;C+=h.p-1;++shadowEvents;}}
 // Check all contiguous high subwords over at most two distinct labels.
 // At each left endpoint, extend until a third label is encountered.
 for(size_t a=0;a<high.size();++a){int p=high[a].p,q=0;size_t b=a+1;while(b<high.size()){int u=high[b].p;if(u!=p){if(!q)q=u;else if(q!=u)break;}++b;}I n=b-a;++twoChecks;maxTwo=max(maxTwo,n);if(q&&min(p,q)>limit){++twoLarge;maxLarge=max(maxLarge,n);if(n>=4){assert(abs(p-q)<=4);for(size_t k=a+1;k<b;++k)assert(high[k].p!=high[k-1].p);}if(n>=6){assert(abs(p-q)==2);++six;}assert(n<=7);if(n==7)assert(high[a].p>high[a+1].p);}else maxSmallPair=max(maxSmallPair,n);}
 if(pool.size()<=5){int g=C-firstC;maxGain=max(maxGain,I(g));}
 }
 cout<<"X="<<X<<" B="<<w.B<<" events="<<events<<" discoveries="<<discoveries<<" replay="<<shadowEvents<<" twoChecks="<<twoChecks<<" largeChecks="<<twoLarge<<" maxTwo="<<maxTwo<<" maxLarge="<<maxLarge<<" maxSmallPair="<<maxSmallPair<<" six="<<six<<" nonTwin="<<nonTwin<<" nonTwinLT3="<<less3<<" distinctHist=";for(auto [k,v]:nlabels)cout<<k<<":"<<v<<",";cout<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
