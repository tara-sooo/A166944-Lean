#define main full_budget_main
#include "min_full_horizon_budget_audit.cpp"
#undef main
#include <map>
#include <tuple>
#include <set>
struct V{int C,t,p,next;};
struct Rec{int C,t,M,prev,p,q,d1,dt;};
struct Count{I all=0,far=0;};
Count pairs(vector<int> a,int B){sort(a.begin(),a.end());I near=0;size_t l=0;for(size_t i=0;i<a.size();++i){while(a[i]-a[l]>B)++l;near+=i-l;}I n=I(a.size())*(a.size()-1)/2;return {2*n,2*(n-near)};}
void add(Count &a,Count b,int s=1){a.all+=s*b.all;a.far+=s*b.far;}
void run(int X){Wheel w(X);int B=w.B,Q=int(ceil(B/pow(log(B),1.0/3)));vector<Rec> a;vector<V> v;set<int> observed;I R=0,rareR=0,triples=0,events=0,maxLag=0;vector<int> mass(7*X/2+2);
 for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4;v.clear();while(true){Hit h=w.hit(t,C,K);if(!h.p)break;int r=min(w.spf[C-1],w.spf[C+1]);R+=r;++events;++mass[C/2];v.push_back({C,t,h.p,h.t});C+=h.p-1;t=h.t;}
  for(size_t i=1;i+1<v.size();++i){auto x=v[i-1],y=v[i],z=v[i+1];a.push_back({y.C,y.t,M,x.p,y.p,z.p,y.next-y.t,z.next-y.t});if(x.p>=Q&&z.p==x.p){int p=x.p,q=y.p,s0=(x.C-1)%p==0?-1:1,s2=(z.C-1)%p==0?-1:1;assert(q>=p&&q!=p);assert((q-2-s0+s2)%(p)==0);assert(((p-1)+(q-1)+s2-s0)%(2*p)==0);++triples;observed.insert(x.C);observed.insert(y.C);observed.insert(z.C);}}
 }
 for(int C:observed)rareR+=I(min(w.spf[C-1],w.spf[C+1]))*mass[C/2];
 // Enumerate a superset of all three horizons in an actual p,q,p with p>=Q.
 set<int> possible;I keys=0;for(int p=max(5,Q);p<=B;++p)if(w.spf[p]==p)for(int k=1;k<=B/p+1;k+=2)for(int c:{2,4}){int q=k*p+c;if(q>B||q==p||w.spf[q]!=q)continue;for(int s0:{-1,1})for(int s1:{-1,1})for(int s2:{-1,1}){if(c!=2+s0-s2)continue;I start=2*I(X),end=7*I(X)-(p-1)-(q-1);I C=start+((-s0-start)%(2*p)+2*p)%(2*p); // correct even residue: use one of two representatives modulo p
 if(C%2) C+=p; // may exceed first even solution by 2p; normalize
 if(C-2*p>=start) C-=2*p;
 for(;C<end;C+=2*p){if((C+p-1+s1)%q)continue;++keys;possible.insert(int(C));possible.insert(int(C+p-1));possible.insert(int(C+p+q-2));}
 }}
 for(int C:observed){assert(possible.count(C));}I possibleR=0;for(int C:possible){int r=min(w.spf[C-1],w.spf[C+1]);if(r<=B)possibleR+=I(r)*mass[C/2];}assert(rareR<=possibleR);
 sort(a.begin(),a.end(),[](const Rec&a,const Rec&b){return tie(a.C,a.p,a.q,a.dt,a.d1,a.t,a.M)<tie(b.C,b.p,b.q,b.dt,b.d1,b.t,b.M);});Count ret,retSamePrev,retLarge;I weightedFar=0;for(size_t i=0,j;i<a.size();i=j){for(j=i+1;j<a.size()&&tie(a[j].C,a[j].p,a[j].q,a[j].dt)==tie(a[i].C,a[i].p,a[i].q,a[i].dt);++j){}if(j-i<2)continue;vector<int> ids;map<int,vector<int>> byWait,byPrev;map<pair<int,int>,vector<int>> byBoth;map<int,vector<int>> bigPrev;map<pair<int,int>,vector<int>> bigBoth;int lo=a[i].t,hi=lo;for(size_t k=i;k<j;++k){auto b=a[k];lo=min(lo,b.t);hi=max(hi,b.t);ids.push_back(b.M);byWait[b.d1].push_back(b.M);byPrev[b.prev].push_back(b.M);byBoth[{b.prev,b.d1}].push_back(b.M);if(b.prev>=Q&&b.q>=Q){bigPrev[b.prev].push_back(b.M);bigBoth[{b.prev,b.d1}].push_back(b.M);}}
 maxLag=max(maxLag,I(hi-lo));Count rr=pairs(ids,B);for(auto &e:byWait)add(rr,pairs(e.second,B),-1);add(ret,rr);weightedFar+=rr.far*(I(min(w.spf[a[i].C-1],w.spf[a[i].C+1]))+min(w.spf[a[i].C+a[i].p-2],w.spf[a[i].C+a[i].p]));for(auto &e:byPrev)add(retSamePrev,pairs(e.second,B));for(auto &e:byBoth)add(retSamePrev,pairs(e.second,B),-1);for(auto &e:bigPrev){Count n=pairs(e.second,B);if(n.all){assert(hi-lo<2LL*Q*Q);if(e.first!=a[i].q){for(auto &b:bigBoth)if(b.first.first==e.first)add(n,pairs(b.second,B),-1);assert(n.all==0);continue;}add(retLarge,n);}}for(auto &e:bigBoth)if(e.first.first==a[i].q)add(retLarge,pairs(e.second,B),-1);

 }
 assert(ret.all>=retSamePrev.all&&retSamePrev.all>=retLarge.all&&ret.far>=retSamePrev.far&&retSamePrev.far>=retLarge.far);cout<<"X="<<X<<" B="<<B<<" Q="<<Q<<" events="<<events<<" R="<<R<<" triples="<<triples<<" obs="<<observed.size()<<" possible="<<possible.size()<<" keys="<<keys<<" rareR="<<rareR<<" possibleR="<<possibleR<<" maxLag="<<maxLag<<" reversal="<<ret.all<<" far="<<ret.far<<" weightedFar="<<weightedFar<<" samePrev="<<retSamePrev.all<<" samePrevFar="<<retSamePrev.far<<" large="<<retLarge.all<<" largeFar="<<retLarge.far<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
