#define main stopped_ghost_main
#include "min_stopped_ghost_audit.cpp"
#undef main
#include <iomanip>
#include <map>
#include <tuple>
struct Entry {int source[2]={0,0};};
void kernel(const vector<Layer>& layers,int b,int P,I N,int eta){
 int m=2*P;long double q=eta/10.0L;
 vector<vector<long double>> k(m,vector<long double>(b));k[m-1][b-1]=1;
 for(int j=m-2;j>=0;--j)for(int r=0;r<b;++r)k[j][r]=(1-q)*k[j+1][r]+(r+1<b?q*k[j+1][r+1]:0);
 vector<long double> tail(b+1);tail[b]=1;
 for(int j=0;j<m;++j)for(int r=0;r<b;++r)tail[r]=(1-q)*tail[r]+q*tail[r+1];
 long double init=tail[0];vector<I> mass(b+1);mass[0]=N;
 long double actual=init,ghost=init,posGhost=init,critical=0,outer=0,old=0,global=init;
 long double width=sqrtl(3.0L*m*logl(max(2,P)));I critActive=0,allActive=0;
 for(int j=0;j<m;++j){const auto &z=layers[j];vector<I> next=mass;I maxex=0,globalRisk=0;long double maxWeight=0;for(int r=0;r<b;++r){I f=0,g=0,a=0;if(r<(int)z.active.size()){f=z.inc[r];g=z.risk[r];a=z.active[r];}assert(a<=mass[r]&&f<=g&&g<=a);long double e=(long double)g-q*mass[r],pos=max(0.0L,e);actual+=k[j][r]*((long double)f-q*mass[r])/N;ghost+=k[j][r]*e/N;posGhost+=k[j][r]*pos/N;maxex=max(maxex,10*g-eta*mass[r]);allActive+=a;globalRisk+=g;if(r<j)maxWeight=max(maxWeight,k[j][r]);
 if(fabsl((b-r-1)-q*(m-j-1))<=width){critical+=k[j][r]*pos/N;critActive+=a;}else outer+=k[j][r]*pos/N;
 next[r]-=f;next[r+1]+=f;}mass.swap(next);global+=maxWeight*globalRisk/N;old+=maxex/(10.0L*N);}
 assert(fabsl(actual-(long double)mass[b]/N)<1e-10L);assert(ghost+1e-10L>=actual);assert(posGhost+1e-10L>=ghost);assert(posGhost<=init+old+1e-10L);
 cout<<setprecision(9)<<" eta="<<eta<<" old="<<double(old)<<" tail="<<double(init)<<" signed="<<double(ghost)<<" positive="<<double(posGhost)<<" global="<<double(global)<<" critical="<<double(critical)<<" outer="<<double(outer)<<" critActive="<<critActive<<" active="<<allActive<<" killed="<<mass[b];
}
// Uncapped number of DISTINCT previously seen admissible ghost labels.
int incidences(const Wheel&w,State s,int K,int y,const vector<int>&prev,vector<int>&mark,int stamp){int result=0;for(;;){Hit low{K+1,0};vector<Hit> candidates;for(int sign:{-1,1}){int z=s.c+sign;while(z>1){int p=w.spf[z];if(p>w.B)break;if(p>2){int m=2*p,r=sign==-1?0:p+2,u=s.t+1+(r-(s.t+1)%m+m)%m;if(u<=K){if(p<=y){if(u<low.t||(u==low.t&&p<low.p))low={u,p};}else if(prev[p]>=0)candidates.push_back({u,p});}}while(z%p==0)z/=p;}}for(Hit h:candidates)if(h.t<low.t||(h.t==low.t&&h.p<low.p)){if(mark[h.p]!=stamp){mark[h.p]=stamp;++result;}}if(!low.p)break;s={low.t,s.c+low.p-1};}return result;}
long double marginal(const vector<I>& sums,int P,I N){int m=2*P,b=P;long double q=.4L;vector<long double> k(b),next(b);k[b-1]=1;long double ans=0;for(int j=m-1;j>=0;--j){long double mx=0;for(int r=max(0,j-P);r<min(j,b);++r)mx=max(mx,k[r]);ans+=mx*sums[j]/N;for(int r=0;r<b;++r)next[r]=(1-q)*k[r]+(r+1<b?q*k[r+1]:0);k.swap(next);}return ans;}
void run(int X){Wheel w(X);int B=w.B,y=7,L=210;double logB=log(B);for(int p=11;p<=B;++p)if(w.spf[p]==p){if(I(L)*p>max(210.0,pow(logB,1.0/6)))break;L*=p;y=p;}int P=0;for(int p=y+1;p<=B;++p)if(w.spf[p]==p)++P;int Q=int(ceil(B/pow(logB,2.0/3))),a=int(ceil(pow(logB,1.0/3))),J=3*L+int(ceil(pow(logB,1.0/6))),R=max(31,int(ceil(pow(logB,1.0/4)))),m=2*P,b=(P+1)/2;I N=X/2;
 vector<Layer> badLayers(m),allLayers(m);vector<int> prev(B+1,-1),cnt(B+1),used;vector<Event> v;map<tuple<int,int,int,int,int,int>,Entry> seen;bool witness=false;I mixed=0;vector<I> sums(m);vector<int> mark(B+1);int stamp=0;
 for(int M=X+1;M<2*X;M+=2){State s{M+2,2*M-2};int K=(7*M-1)/4,cost=0,allCost=0;used.clear();v.clear();for(int j=0;j<m;++j){Ghost g=scan(w,s,K,y,L,Q,a,J,R,v,prev,cnt);Hit h=g.actual.h;if(!h.p)break;int p=h.p,C=g.actual.C;bool inc=bad(p,C,v,prev,cnt,Q,a,J,R),repeat=prev[p]>=0;int nInc=incidences(w,s,K,y,prev,mark,++stamp);assert((nInc>0)==g.allRisk);sums[j]+=nInc;
 if(cost<b)badLayers[j].add(cost,g.risk,inc);
 if(allCost<P)allLayers[j].add(allCost,g.allRisk,repeat);
 if(X<=65536){auto &e=seen[{j,allCost,s.t,s.c,h.t,p}];if(!e.source[repeat]){if(e.source[!repeat]){++mixed;if(!witness){cout<<"witness X="<<X<<" j="<<j<<" r="<<allCost<<" t="<<s.t<<" C="<<s.c<<" next="<<h.t<<","<<p<<" fresh_M="<<(repeat?e.source[0]:M)<<" repeat_M="<<(repeat?M:e.source[1])<<"\n";witness=true;}}e.source[repeat]=M;}}
 cost+=inc;allCost+=repeat;if(!cnt[p]++)used.push_back(p);prev[p]=j;v.push_back({p,C,(C-1)%p==0?-1:1});s={h.t,C+p-1};}for(int p:used){cnt[p]=0;prev[p]=-1;}}
 cout<<"X="<<X<<" P="<<P<<" marginal="<<double(marginal(sums,P,N))<<" mixedStates="<<(X<=65536?mixed:-1)<<" ALL";kernel(allLayers,P,P,N,4);cout<<" RES";kernel(badLayers,b,P,N,2);cout<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
