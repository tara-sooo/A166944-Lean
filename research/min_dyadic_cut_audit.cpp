#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <map>
#include <tuple>
#include <vector>
using namespace std;
using I=int64_t;
struct Hit{int t,p;};
struct Wheel{int B;vector<int> spf;explicit Wheel(int X):B(int(ceil(sqrt(7.0*X)))),spf(7*X+4){for(int i=2;i<int(spf.size());++i)if(!spf[i]){spf[i]=i;if(I(i)*i<I(spf.size()))for(I j=I(i)*i;j<I(spf.size());j+=i)if(!spf[j])spf[j]=i;}} Hit hit(int t,int C,int K)const{Hit best{K+1,0};for(int s:{-1,1}){int v=C+s;while(v>1){int p=spf[v];if(p>B)break;if(p>2){int m=2*p,r=s==-1?0:p+2,u=t+1+(r-(t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(v%p==0)v/=p;}}return best;}};
struct Rec{int C,id,t,p,active;};
struct Entry{I n=0,H=0,late=0;int b=0,C=0,t=0;vector<int> K;};
void run(int X){assert(X>=256&&(X&(X-1))==0);Wheel w(X);int B=w.B,N=X/2;vector<Rec> a;I R=0,E=0,events=0;for(int i=0;i<N;++i){int M=X+2*i+1,t=M+2,C=2*M-2,K=(7*M-1)/4,p0=0;while(true){Hit h=w.hit(t,C,K);a.push_back({C,i,t,p0,h.p!=0});if(!h.p)break;R+=min(w.spf[C-1],w.spf[C+1]);++events;t=h.t;C+=h.p-1;p0=h.p;assert(C<=2*t);}}sort(a.begin(),a.end(),[](Rec a,Rec b){return tie(a.C,a.id)<tie(b.C,b.id);});for(size_t i=0,j;i<a.size();i=j){I n=0;for(j=i;j<a.size()&&a[j].C==a[i].C;++j)n+=a[j].active;E+=n*n*min(w.spf[a[i].C-1],w.spf[a[i].C+1]);}I sum=0,farSum=0,nearOriginSum=0;cout<<"X="<<X<<" B="<<B<<" events="<<events<<" R="<<R<<" E="<<E<<"\n";
 for(int k=2;k<=N;k*=2){I H=0,F=0,FO=0,cross=0,distinct=0,proj=0,maxW=0,maxProj=0,entryEnergy=0,nonzero=0,maxAvg=0;bool coarse=k>B;vector<int> idEntry(coarse?N:0,-1);vector<Entry> entries;map<tuple<int,int,int,int>,int> em;map<tuple<int,int,int>,I> pm; vector<tuple<int,int,I,I>> rightMass;
  for(size_t i=0,j;i<a.size();i=j){int C=a[i].C,r=min(w.spf[C-1],w.spf[C+1]);for(j=i+1;j<a.size()&&a[j].C==C;++j){}for(size_t u=i,v;u<j;u=v){int b=a[u].id/k,mid=b*k+k/2,J=2*X+4*(mid-1);for(v=u+1;v<j&&a[v].id/k==b;++v){}I nl=0,nr=0,fl=0,fr=0,frNew=0;for(size_t x=u;x<v;++x){auto z=a[x];int C0=2*X+4*z.id;bool left=z.id<mid,far=left?J-C0>B:C0-J>B;if(coarse&&left&&far&&C>J&&idEntry[z.id]<0){assert(z.p>0);int D=C-z.p+1;assert(D<=J&&D>=J-z.p+2&&C<J+B&&((D-1)%z.p==0||(D+1)%z.p==0));auto key=make_tuple(b,z.p,D,z.t);auto [it,inserted]=em.emplace(key,int(entries.size()));if(inserted){entries.emplace_back();entries.back().b=b;entries.back().C=C;entries.back().t=z.t;}int id=it->second;idEntry[z.id]=id;++entries[id].n;entries[id].K.push_back((7*(X+2*z.id+1)-1)/4);++pm[{b,z.p,D}];++cross;}if(!z.active)continue;if(left){++nl;fl+=far;}else{++nr;fr+=far;frNew+=far&&C-C0<=B;}}
 H+=I(r)*nl*nr;F+=I(r)*fl*fr;FO+=I(r)*fl*frNew;if(coarse&&fr)rightMass.emplace_back(C,b,fr,fr-frNew);if(coarse&&fr){for(size_t x=u;x<v;++x){auto z=a[x];if(z.active&&z.id<mid&&J-(2*X+4*z.id)>B){int id=idEntry[z.id];assert(id>=0);entries[id].H+=I(r)*fr;entries[id].late+=I(r)*(fr-frNew);}}}}
 }
 sum+=H;farSum+=F;nearOriginSum+=FO;if(coarse){I check=0;I lateCheck=0, suffixChecks=0;for(auto &e:entries){sort(e.K.begin(),e.K.end());int C=e.C,t=e.t,K=e.K.back();I replay=0,replayLate=0;while(true){Hit h=w.hit(t,C,K);if(!h.p)break;I m=e.K.end()-lower_bound(e.K.begin(),e.K.end(),h.t);assert(m>0);auto it=lower_bound(rightMass.begin(),rightMass.end(),make_tuple(C,e.b,I(0),I(0)));if(it!=rightMass.end()&&get<0>(*it)==C&&get<1>(*it)==e.b){int r=min(w.spf[C-1],w.spf[C+1]);replay+=r*m*get<2>(*it);replayLate+=r*m*get<3>(*it);}++suffixChecks;t=h.t;C+=h.p-1;}assert(replay==e.H&&replayLate==e.late);lateCheck+=replayLate;check+=e.H;maxW=max(maxW,e.n);entryEnergy+=e.n*e.n;nonzero+=e.H>0;if(e.n)maxAvg=max(maxAvg,e.H/e.n);}assert(check==F&&lateCheck==F-FO);cout<<" suffixChecks="<<suffixChecks;for(auto e:pm)maxProj=max(maxProj,e.second);distinct=entries.size();proj=pm.size();assert(proj<=I(N/k)*2*B);}
 cout<<" k="<<k<<" H="<<H<<" far="<<F<<" nearOrigin="<<FO<<" cross="<<cross<<" keys="<<distinct<<" projected="<<proj<<" maxW="<<maxW<<" maxProj="<<maxProj<<" entryE="<<entryEnergy<<" nonzero="<<nonzero<<" maxAvg="<<maxAvg<<"\n";
 }
 assert(E==R+2*sum);assert(nearOriginSum<=I(B/4+1)*R);cout<<" sumH="<<sum<<" sumFar="<<farSum<<" nearOriginTotal="<<nearOriginSum<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
