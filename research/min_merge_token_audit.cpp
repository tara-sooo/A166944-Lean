#define main full_budget_main
#include "min_full_horizon_budget_audit.cpp"
#undef main
#include <tuple>
struct Rec{int C,t,id,pc,pt,p;};
enum Type{REP,SAME,BIG,MIXED,ROOT};
void run(int X){Wheel w(X);int B=w.B,N=X/2,Q=int(ceil(B/pow(log(B),2.0/3))),y=int(ceil(pow(log(B),2)));vector<Rec>a;vector<int>typ(N),crossed(N);I total=0,R=0;
 for(int id=0;id<N;++id){int M=X+2*id+1,t=M+2,C=2*M-2,K=(7*M-1)/4,pc=-1,pt=-1;for(;;){Hit h=w.hit(t,C,K);a.push_back({C,t,id,pc,pt,h.p});if(!h.p)break;R+=min(w.spf[C-1],w.spf[C+1]);++total;pc=C;pt=t;C+=h.p-1;t=h.t;assert(C<=2*t);}}
 sort(a.begin(),a.end(),[](const Rec&a,const Rec&b){return tie(a.C,a.t,a.pc,a.pt,a.id)<tie(b.C,b.t,b.pc,b.pt,b.id);});I birth[5]={},cost[5]={},entry[5]={},after[5]={},repHigh=0,rareVertices=0,rareUnits=0,unique=0,activeVertices=0,ends=0;int J=3*X-4,maxLarge=0;
 auto demote=[&](int id,int k){assert(typ[id]==REP);typ[id]=k;++birth[k];};
 for(size_t i=0,j;i<a.size();i=j){for(j=i+1;j<a.size()&&a[j].C==a[i].C&&a[j].t==a[i].t;++j){}++unique;int C=a[i].C;vector<pair<int,int>> reps;
  for(size_t l=i,u;l<j;l=u){for(u=l+1;u<j&&a[u].pc==a[l].pc&&a[u].pt==a[l].pt;++u){}int id=-1;for(size_t x=l;x<u;++x)if(typ[a[x].id]==REP){assert(id<0);id=a[x].id;}assert(id==a[u-1].id);reps.push_back({a[l].pc<0?0:C-a[l].pc+1,id});}
  sort(reps.begin(),reps.end());vector<int> big,small;int root=-1;
  for(size_t l=0,u;l<reps.size();l=u){for(u=l+1;u<reps.size()&&reps[u].first==reps[l].first;++u){}for(size_t x=l;x+1<u;++x)demote(reps[x].second,SAME);auto [p,id]=reps[u-1];if(!p)root=id;else if(p>=Q)big.push_back(id);else small.push_back(id);}
  maxLarge=max(maxLarge,int(big.size()));if(big.size()>=2){++rareVertices;rareUnits+=big.size()-1;}if(!big.empty()){sort(big.begin(),big.end());for(size_t x=0;x+1<big.size();++x)demote(big[x],BIG);small.push_back(big.back());}sort(small.begin(),small.end());for(size_t x=0;x+1<small.size();++x)demote(small[x],MIXED);int rep=small.empty()?-1:small.back();if(root>=0){if(rep>=0)demote(min(rep,root),ROOT);rep=max(rep,root);}assert(rep>=0);int maxid=-1,r=min(w.spf[C-1],w.spf[C+1]);bool active=false,repActive=false;
  for(size_t x=i;x<j;++x){auto z=a[x];maxid=max(maxid,z.id);int k=typ[z.id];assert((k==REP)==(z.id==rep));if(z.id<N/2&&J-(2*X+4*z.id)>B&&C>J&&!crossed[z.id]){assert(z.pc>=0&&z.pc<=J&&C<J+B);crossed[z.id]=1;++entry[k];}if(z.p){assert(r<=z.p);cost[k]+=r;if(crossed[z.id])after[k]+=r;active=true;if(k==REP){repActive=true;if(z.p>=y)repHigh+=r;}}else ++ends;}
  assert(rep==maxid);assert(active==repActive);activeVertices+=active;
 }
 I s=0,d=0;for(int k=0;k<5;++k){s+=cost[k];d+=birth[k];}assert(s==R&&birth[BIG]==rareUnits&&ends==N&&d<=N&&cost[BIG]<=8*I(X)*birth[BIG]);cout<<"X="<<X<<" B="<<B<<" Q="<<Q<<" y="<<y<<" events="<<total<<" unique="<<unique<<" active="<<activeVertices<<" R="<<R<<" rareV="<<rareVertices<<" rareUnits="<<rareUnits<<" maxLarge="<<maxLarge<<" repHigh="<<repHigh<<" births=";for(auto v:birth)cout<<v<<",";cout<<" cost=";for(auto v:cost)cout<<v<<",";cout<<" entry=";for(auto v:entry)cout<<v<<",";cout<<" after=";for(auto v:after)cout<<v<<",";cout<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
