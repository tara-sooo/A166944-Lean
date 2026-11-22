// Event-jump exhaustive or sampling audit of untruncated canonical squarefree wheel.
// Finite tests, NOT a general termination theorem.
#include <bits/stdc++.h>
using namespace std;using ll=long long;
struct Ret{ll T,G,events;};
ll next_pos(ll pos,int p,int residue){ll gap=(residue-pos)%(2LL*p);if(gap<=0)gap+=2LL*p;return pos+gap;}
Ret run(ll v,ll L,const vector<int>&ps){ll s=v+2,pos=s,C=(2*v-2)%L,G=0;ll ev=0;
while(true){ll next=LLONG_MAX;int active=0;for(int p:ps){if((C-1+p)%p==0){active++;next=min(next,next_pos(pos,p,0));}if((C+1)%p==0){active++;next=min(next,next_pos(pos,p,p+2));}}
if(!active)break;
ll d=1;for(int p:ps){if(next%2==0){if(next%p==0&&(C-1+p)%p==0)d*=p;}else{if((next-2)%p==0&&(C+1)%p==0)d*=p;}}
if(d<=1)throw runtime_error("invalid first event");
C=(C+d-1)%L;G+=d-1;pos=next;if(++ev>100000)throw runtime_error("no termination in event budget");}
if(G>2*(pos-s)+6)throw runtime_error("nonnegative deficit violation");
return {pos-s,G,ev};}
int main(int argc,char**argv){int cap=argc>1?atoi(argv[1]):19;long long N=argc>2?atoll(argv[2]):-1;ll L=1;vector<int>ps;for(int p=3;p<=cap;p+=2){bool prime=true;for(int d=3;d*d<=p;d+=2)if(p%d==0)prime=false;if(prime){ps.push_back(p);L*=p;}}if(N<0)N=L;mt19937_64 rng(20261123);ll maxT=0,maxG=0,maxEvents=0,Tgt0=0,sumT=0,sumG=0,violations=0;ll witnessT=0,witnessG=0;
for(ll i=0;i<N;i++){ll v=(N==L)?2*i+1:2*(rng()%L)+1;auto r=run(v,L,ps);if(r.T>maxT){maxT=r.T;witnessT=v;}if(r.G>maxG){maxG=r.G;witnessG=v;}maxEvents=max(maxEvents,r.events);sumT+=r.T;sumG+=r.G;if(r.T>cap*cap)violations++;if(r.G==0)Tgt0++;}
cout<<"PASS q="<<cap<<" L="<<L<<" sample="<<N<<" full="<<(N==L?1:0)<<" maxT="<<maxT<<" at_v="<<witnessT<<" maxG="<<maxG<<" at_v="<<witnessG<<" maxEvents="<<maxEvents<<" meanT="<<double(sumT)/N<<" meanG="<<double(sumG)/N<<" stepsOver_qSquared="<<violations<<" zero_growth="<<Tgt0<<"\n";
if(N==L){struct Check{int p;ll t,g;};Check checks[]={{3,5,4},{5,17,10},{7,48,28},{11,114,98},{13,157,148},{17,239,316},{19,388,568}};for(auto x:checks)if(x.p==cap&&(x.t!=maxT||x.g!=maxG))throw runtime_error("terminal regression failed");
if(cap==19&&(violations!=2 || witnessT!=8264687 || witnessG!=8264687))throw runtime_error("q19 counterexample regression failed");}}
