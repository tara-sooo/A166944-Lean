// Standalone integer certificate, no external dependencies.
// g++ -O3 -std=c++17 negative_min_mod2310_potential.cpp -o /tmp/min2310 && /tmp/min2310
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <deque>
#include <iostream>
#include <vector>
using namespace std;
constexpr int Q=210,N=Q*Q/2,M=N*121,A=17,B=8,LIM=1000,P=291;
int mod(int x,int q){int r=x%q;return r<0?r+q:r;}
int idx(int x,int n){return mod(x,Q)/2*Q+mod(n,Q);}
int wait(int x,int n,int p){int c=mod(x+1,p)==0?0:mod(x-1,p)==0?p+2:-1;if(c<0)return 100000;int w=mod(c-n,2*p);return w?w:2*p;}
struct Edge{int j,p,w,c;};
int main(){
 vector<int> ps;for(int p=3;p<=P;p+=2){bool v=true;for(int d=3;d*d<=p;d+=2)if(p%d==0){v=false;break;}if(v)ps.push_back(p);}
 vector<int>w0(N,100000),p0(N);for(int i=0;i<N;i++){int x=2*(i/Q),n=i%Q;for(int p:{3,5,7}){int w=wait(x,n,p);if(w<w0[i])w0[i]=w,p0[i]=p;}}
 auto raw=[&](int i,int cutoff,auto emit){int x=2*(i/Q),n=i%Q;if(p0[i])emit(idx(x-p0[i]+1,n+w0[i]),p0[i],w0[i]);for(int p:ps)if(p>7&&p<=cutoff)for(int w=1;w<=min(2*p,w0[i]-1);w++)emit(idx(x-p+1,n+w),p,w);};
 vector<int>F(N),inq(N,1);deque<int>q;for(int i=0;i<N;i++)q.push_back(i);int pops0=0;
 while(q.size()){int i=q.front();q.pop_front();inq[i]=0;assert(++pops0<2000000);raw(i,97,[&](int j,int p,int w){int c=6*w-13*(p-1);if(F[j]<F[i]+c){F[j]=F[i]+c;if(!inq[j])q.push_back(j),inq[j]=1;}});}
 assert(*min_element(F.begin(),F.end())==0&&*max_element(F.begin(),F.end())==80);long long baseChecks=0;for(int i=0;i<N;i++)raw(i,97,[&](int j,int p,int w){assert(F[j]-F[i]>=6*w-13*(p-1));baseChecks++;});assert(98-13>=80);
 vector<vector<Edge>>edges(N);long long ec=0;
 for(int i=0;i<N;i++)raw(i,P,[&](int j,int p,int w){int c=6*(B*w-A*(p-1))-B*(F[j]-F[i]);if(c>=-LIM){edges[i].push_back({j,p,w,c});ec++;}});
 vector<int>H(M),in(M);auto getwait=[&](int i,int u,int v){int n=i%Q;int nn=v;if((nn%2)!=(n%2))nn+=11;return wait(u,nn,11);};
 auto relax=[&](int I,auto emit){int i=I/121,u=(I%121)/11,v=I%11,ww=getwait(i,u,v);for(auto e:edges[i]){if(e.p==11?e.w!=ww:e.p<11?e.w>ww:e.w>=ww)continue;int J=e.j*121+mod(u-e.p+1,11)*11+mod(v+e.w,11);emit(J,e);}};
 for(int I=0;I<M;I++)relax(I,[&](int J,Edge e){if(e.c>H[J]){H[J]=e.c;if(!in[J])q.push_back(J),in[J]=1;}});
 long long pops=0;while(q.size()){int I=q.front();q.pop_front();in[I]=0;relax(I,[&](int J,Edge e){if(H[J]<H[I]+e.c){H[J]=H[I]+e.c;assert(H[J]<=LIM);if(!in[J]){in[J]=1;if(q.size()&&H[J]>H[q.front()])q.push_front(J);else q.push_back(J);}}});assert(++pops<20000000);}
 int mx=*max_element(H.begin(),H.end());assert(*min_element(H.begin(),H.end())==0&&mx==940);assert(6*(A-2*B)*(P+1)-6*A-80*B>=LIM);
 // Independent verifier: enumerate every finite raw transition again. Recompute
 // small-prime priority by literal ticks; check omitted edges using range only.
 auto literal=[&](int x,int n,int p){for(int w=1;w<=2*p;w++){int c=n+w;if(c%2==0?mod(x+1,p)==0&&mod(c,2*p)==0:mod(x-1,p)==0&&mod(c,2*p)==p+2)return w;}return 100000;};
 vector<array<int,121>> w11(N);for(int i=0;i<N;i++)for(int u=0;u<11;u++)for(int v=0;v<11;v++){int nn=v;if(nn%2!=i%Q%2)nn+=11;w11[i][u*11+v]=literal(u,nn,11);}
 long long retained=0,discarded=0,checked=0;
 for(int i=0;i<N;i++){int x=2*(i/Q),n=i%Q;int small=0,ws=100000;for(int p:{3,5,7}){int w=literal(x,n,p);if(w<ws)ws=w,small=p;}assert(small==p0[i]&&ws==w0[i]);
  auto verify=[&](int p,int w){int j=idx(x-p+1,n+w);int c=6*(B*w-A*(p-1))-B*(F[j]-F[i]);if(c< -LIM){assert(c<=-mx);discarded++;return;}retained++;for(int u=0;u<11;u++)for(int v=0;v<11;v++){int z=w11[i][u*11+v];if(p==11?w!=z:p<11?w>z:w>=z)continue;int I=i*121+u*11+v,J=j*121+mod(u-p+1,11)*11+mod(v+w,11);assert(6*(B*w-A*(p-1))<=B*(F[j]-F[i])+H[J]-H[I]);checked++;}};
  if(small)verify(small,ws);for(int p:ps)if(p>7)for(int w=1;w<=min(2*p,ws-1);w++)verify(p,w);
 }
 assert(retained==ec);cout<<"base_states="<<N<<" base_range=80 base_checks="<<baseChecks<<" lifted_states="<<M<<" lift_range="<<mx<<" total_range_bound="<<80*B+mx<<" retained_base_edges="<<retained<<" discarded_base_edges="<<discarded<<" verified_lift_edges="<<checked<<" queue_pops="<<pops<<" cutoff="<<P<<"\n";
}
