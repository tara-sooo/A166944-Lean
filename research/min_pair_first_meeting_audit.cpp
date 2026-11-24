#define main full_budget_main
#include "min_full_horizon_budget_audit.cpp"
#undef main
#include <tuple>
#include <iomanip>
#include <map>
struct Rec {int C,t,M,pc,pt,p,nt;bool active;};
struct Bands {vector<int> lim;vector<I> v;Bands(int X,int B){lim.push_back(B);while(lim.back()<X)lim.push_back(2*lim.back());v.resize(lim.size());}void add(vector<int>& a,I w=1){if(a.size()<2)return;sort(a.begin(),a.end());I before=0;for(size_t k=0;k<lim.size();++k){size_t l=0;I s=0;for(size_t i=0;i<a.size();++i){while(a[i]-a[l]>lim[k])++l;s+=i-l;}v[k]+=w*(s-before);before=s;}assert(before==I(a.size())*I(a.size()-1)/2);}};
void run(int X){Wheel w(X);int B=w.B,Q=int(ceil(B/pow(log(B),2.0/3)));Bands E(X,B),same(X,B),F(X,B),sameLabel(X,B),bigDiff(X,B),sameNext(X,B),mergeNext(X,B),parallel(X,B),mergeCount(X,B);vector<Rec>a;I R=0,total=0,mixed=0,reset=0,bigMixed=0;int maxGain=0,maxSpan=0;
 for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4,pt=-1,pc=-1;while(true){Hit h=w.hit(t,C,K);a.push_back({C,t,M,pc,pt,h.p,h.t,h.p!=0});if(!h.p)break;int r=min(w.spf[C-1],w.spf[C+1]);assert(r<=B&&h.t-t<=2*r);R+=r;++total;pc=C;pt=t;C+=h.p-1;t=h.t;assert(C<=2*t);}maxGain=max(maxGain,C-(2*M-2));}
 sort(a.begin(),a.end(),[](const Rec&x,const Rec&y){return tie(x.C,x.t,x.pc,x.pt,x.M)<tie(y.C,y.t,y.pc,y.pt,y.M);});vector<int> ids;auto add=[&](Bands&dst,size_t l,size_t r,I weight,bool active){ids.clear();for(size_t i=l;i<r;++i)if(!active||a[i].active)ids.push_back(a[i].M);dst.add(ids,weight);};I energy=0;
 for(size_t i=0,j;i<a.size();i=j){for(j=i+1;j<a.size()&&a[j].C==a[i].C;++j){}int C=a[i].C,r=min(w.spf[C-1],w.spf[C+1]);I n=0;int mn=2*X,mx=0;for(size_t k=i;k<j;++k)if(a[k].active){++n;mn=min(mn,a[k].M);mx=max(mx,a[k].M);}if(n){assert(r<=B);energy+=r*n*n;maxSpan=max(maxSpan,mx-mn);add(E,i,j,r,true);
 if(n>1){map<int,vector<int>> byp;map<pair<int,int>,vector<int>> byclock,bygap;for(size_t k=i;k<j;++k)if(a[k].active){byp[a[k].p].push_back(a[k].M);byclock[{a[k].p,a[k].nt}].push_back(a[k].M);bygap[{a[k].p,a[k].nt-a[k].t}].push_back(a[k].M);}for(auto &e:byp)sameNext.add(e.second,r);for(auto &e:byclock){mergeNext.add(e.second,r);mergeCount.add(e.second);}for(auto &e:bygap)parallel.add(e.second,r);}
}for(size_t k=i,l;k<j;k=l){for(l=k+1;l<j&&a[l].t==a[k].t;++l){}if(l-k<2)continue;add(same,k,l,r,true);add(mergeCount,k,l,-1,true);add(F,k,l,1,false);int labels=0,largeLabels=0;
 for(size_t x=k,y;x<l;x=y){for(y=x+1;y<l&&a[y].pc==a[x].pc;++y){}if(a[x].pc>=0){++labels;int p=C-a[x].pc+1;assert(w.spf[p]==p);largeLabels+=p>=Q;add(sameLabel,x,y,1,false);}for(size_t u=x,v;u<y;u=v){for(v=u+1;v<y&&a[v].pt==a[u].pt;++v){}add(F,u,v,-1,false);add(sameLabel,u,v,-1,false);}}
 if(labels>=2){++mixed;int t=a[k].t,delta=2*t-C-(t%2?6:0);if(delta==0)++reset;if(largeLabels>=2){++bigMixed;vector<int> big;for(size_t x=k;x<l;++x)if(a[x].pc>=0&&C-a[x].pc+1>=Q)big.push_back(a[x].M);bigDiff.add(big);for(size_t x=k,y;x<l;x=y){for(y=x+1;y<l&&a[y].pc==a[x].pc;++y){}if(a[x].pc>=0&&C-a[x].pc+1>=Q)add(bigDiff,x,y,-1,false);}assert(delta==0||abs(delta)>=2LL*Q*Q);}}
 }}
 assert(energy==R+2*accumulate(E.v.begin(),E.v.end(),I(0)));for(size_t k=0;k<E.v.size();++k)assert(E.v[k]>=same.v[k]&&F.v[k]>=sameLabel.v[k]&&sameLabel.v[k]>=0&&bigDiff.v[k]>=0&&mergeCount.v[k]==sameLabel.v[k]&&sameNext.v[k]>=mergeNext.v[k]+parallel.v[k]-same.v[k]);
 cout<<"X="<<X<<" B="<<B<<" Q="<<Q<<" events="<<total<<" R="<<R<<" maxGain="<<maxGain<<" maxSpan="<<maxSpan<<" mixed="<<mixed<<" reset="<<reset<<" bigMixed="<<bigMixed<<" E="<<energy<<"\n";for(size_t k=0;k<E.v.size();++k)cout<<"  d="<<(k?E.lim[k-1]:0)<<".."<<E.lim[k]<<" E="<<2*E.v[k]<<" G="<<2*(E.v[k]-same.v[k])<<" F="<<2*F.v[k]<<" sameLabel="<<2*sameLabel.v[k]<<" bigDiff="<<2*bigDiff.v[k]<<" Gdiff="<<2*(E.v[k]-sameNext.v[k])<<" Gmerge="<<2*(mergeNext.v[k]-same.v[k])<<" Gparallel="<<2*(parallel.v[k]-same.v[k])<<" Gchange="<<2*(sameNext.v[k]+same.v[k]-mergeNext.v[k]-parallel.v[k])<<" E_norm="<<setprecision(7)<<double(2*E.v[k])/(I(X)*X*B)<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
