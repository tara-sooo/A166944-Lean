// A166944 Cap B: finite arithmetic verifier for overlap of repeated prime debts.
// Covers (A) one paired-reuse request per distinct prime, arbitrary key count,
// and (B) one key with two adjacent requests plus two other single-request keys.
// GNU C++17. This does not prove Cap B and is not a Lean kernel certificate.
#include <bits/stdc++.h>
using namespace std;
constexpr int WORDS=6;
struct Mask { array<unsigned long long, WORDS> x{}; void set(int q){x[q/64]|=1ULL<<(q%64);} };
struct Placement { int x,y,z; Mask starts,occupied; };
static inline bool clashes(const Placement& p, const Mask &starts, const Mask &occ){
 for(int i=0;i<WORDS;i++)if((p.starts.x[i]&occ.x[i]) || (p.occupied.x[i]&starts.x[i])) return true;
 return false;
}
static inline Mask unions(const Mask &a,const Mask &b){Mask c;for(int i=0;i<WORDS;i++)c.x[i]=a.x[i]|b.x[i];return c;}
vector<Placement> make_places(int p,int W,int windows){
 vector<Placement> out;
 const int q=(p+4)/6, count=2*windows+1;
 int inv3=0;for(int i=1;i<p;i++)if((3*i)%p==1){inv3=i;break;}
 set<vector<int>> offset_patterns;
 for(int sign:{-1,1}){
  int t=((sign*inv3)%p+p)%p;
  vector<int> allowed;
  for(int d=1;d<=W;d++)if((d%p)==0 || (d%p)==t)allowed.push_back(d);
  vector<int> ds{0};
  function<void(int)> rec=[&](int i){
   if((int)ds.size()==count){
    bool good=true;for(int j=0;j+2<count;j++)if(ds[j+2]-ds[j]<p)good=false;
    if(good)offset_patterns.insert(ds);
    return;
   }
   for(int j=i;j<(int)allowed.size();j++){
    int d=allowed[j];if(d-ds.back()<q)continue;
    ds.push_back(d);rec(j+1);ds.pop_back();
   }
  };
  rec(0);
 }
 for(const auto& pat:offset_patterns){
  for(int o=0;o<=W-pat.back();o++){
   Placement v{};v.x=o;v.y=o+pat[1];v.z=o+pat.back();
   for(int d:pat){int h=o+d;
    v.starts.set(h);
    for(int u=h;u<h+q;u++)if(u<WORDS*64)v.occupied.set(u);
   }
   out.push_back(v);
  }
 }
 return out;
}
struct Solver {
 vector<int> ps;
 vector<int> mults;
 vector<vector<Placement>> place;
 long long nodes=0, cap;
 bool overflow=false;
 bool recur(unsigned taken,Mask starts,Mask occ){
  ++nodes;
  if(nodes>cap){overflow=true;return false;}
  if(taken == ((1u<<ps.size())-1))return true;
  int best=-1; int bestcount=INT_MAX;
  for(int i=0;i<(int)ps.size();i++)if(!(taken&(1u<<i))){
   int n=0;
   for(auto &x:place[i])if(!clashes(x,starts,occ))n++;
   if(n==0)return false;
   if(n<bestcount){best=i;bestcount=n;}
  }
  for(auto &x:place[best]){
   if(clashes(x,starts,occ))continue;
   if(recur(taken|(1u<<best),unions(starts,x.starts),unions(occ,x.occupied)))return true;
   if(overflow)return false;
  }
  return false;
 }
 int solve(long long budget){
  cap=budget;
  int k=ps.size();int D=0;for(int i=0;i<k;i++)D+=2*mults[i]*(ps[i]+30);
  int W=(D-1)/6;
  vector<vector<Placement>> raw;for(int i=0;i<k;i++) raw.push_back(make_places(ps[i],W,mults[i]));
  int inert[]={0,2,3,5,7,10,12,17,18,23,25,28,30,32,33};
  bool allowed[35]{};for(int a:inert)allowed[a]=true;
  for(int shift:inert){
   Mask good;for(int y=0;y<=W;y++)if(allowed[(shift+y)%35])good.set(y);
   place.clear();place.resize(k);
   for(int i=0;i<k;i++)for(const auto &v:raw[i]){
     bool ok=true;for(int w=0;w<WORDS;w++)if(v.starts.x[w]&~good.x[w])ok=false;
     if(ok)place[i].push_back(v);
   }
   if(any_of(place.begin(),place.end(),[](auto &v){return v.empty();}))continue;
   for(int root=0;root<k;root++){
    for(auto &p:place[root]){
     if(p.x!=0)continue;
     if(recur(1u<<root,p.starts,p.occupied))return 1;
     if(overflow)return 2;
    }
   }
  }
  return 0;
 }
};
// At every positive-debt event p>=61, pre-horizon C is 0 mod 6,
// coprime-to-210 on C-1 and C+1, and +/-1 modulo p. Thus its C/6
// has one of 15 inert residues mod 35, and for one p the positions lie
// in two classes mod p. The gaps between prime events fund their growth.
// Necessary counting bounds reduce potential violations to finite tuples.
static vector<int> primes_through(int n){
 vector<bool> prime(n+1,true);prime[0]=prime[1]=false;
 for(int p=2;p*p<=n;p++)if(prime[p])for(int q=p*p;q<=n;q+=p)prime[q]=false;
 vector<int> out;for(int p=61;p<=n;p++)if(prime[p])out.push_back(p);
 return out;
}
int main(){
 const auto primes=primes_through(323);
 const int expected[]={0,0,0,303,1215,1347,540,43};
 long long totalSingle=0, totalDouble=0;
 auto beg=chrono::steady_clock::now();
 for(int k=3;k<=7;k++){
  int checked=0,good=0,timed=0;long long maxnodes=0;
  vector<int> rest;
  function<void(int,int)> dfs=[&](int start,int S){
   if((int)rest.size()==k-1){
    if(S>=63*k-1)return;
    for(int j=start;j<(int)primes.size();j++){
     int P=primes[j];
     if(6*P>=2*(S+P)+60*k)continue;
     Solver solver;solver.ps=rest;solver.ps.push_back(P);
     solver.mults.assign(k,1);
     int res=solver.solve(200000);
     checked++;maxnodes=max(maxnodes,solver.nodes);
     if(res==1) good++;
     if(res==2) timed++;
    }
    return;
   }
   for(int j=start;j<(int)primes.size();j++){
    if(S+primes[j]>=63*k-1)break;
    rest.push_back(primes[j]);dfs(j+1,S+primes[j]);rest.pop_back();
   }
  };
  dfs(0,0);
  cout<<"single k="<<k<<" candidates="<<checked<<" possible="<<good
      <<" unfinished="<<timed<<" maxnodes="<<maxnodes<<"\n";
  if(checked!=expected[k]||good||timed)return 1;
  totalSingle+=checked;
 }
 int good=0,timed=0;long long maxnodes=0;
 for(int p:primes)for(int q:primes)if(q!=p)for(int r:primes)if(r>q&&r!=p){
  const int D=4*p+2*q+2*r+240;
  const int P=max({p,q,r});
  const int increments=5*(p-1)+3*(q-1)+3*(r-1)-(P-1);
  if(increments>=D || max({12*p,6*q,6*r})>=D)continue;
  totalDouble++;
  Solver solver;solver.ps={p,q,r};solver.mults={2,1,1};
  int res=solver.solve(200000);maxnodes=max(maxnodes,solver.nodes);
  if(res==1) good++;
  if(res==2) timed++;
 }
 cout<<"repeat(2,1,1) candidates="<<totalDouble<<" possible="<<good
     <<" unfinished="<<timed<<" maxnodes="<<maxnodes<<"\n";
 if(totalDouble!=2184||good||timed)return 1;
 cout<<"PASS: all "<<totalSingle+totalDouble<<" arithmetic candidates excluded\n";
 cout<<"Seconds: "<<chrono::duration<double>(chrono::steady_clock::now()-beg).count()<<"\n";
}