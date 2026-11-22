// A166944 squarefree-prime stage: EXACT first divergence versus old last hit.
// g++ -O3 -std=c++17 research/squarefree_first_split_timing_audit.cpp -o timing_audit
// ./timing_audit 1024 ; ./timing_audit 4096 ; ./timing_audit 16384
// No global mean bound, Cap B or twin-prime proof.
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
vector<int> spf;
vector<int> factor(int n){
  vector<int>o;
  while(n>1){
    int p=spf[n];o.push_back(p);
    while(n%p==0)n/=p;
  }
  return o;
}
ll nextp(ll pos,int p,int residue){
  ll d=(residue-pos)%(2LL*p);
  if(d<=0)d+=2LL*p;
  return pos+d;
}
struct Event {ll n,C;int e;};
struct Path {int growth;ll last;vector<Event>events;};

Path old_run(int m,int P){
  ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2,last=pos;
  vector<Event> ev;
  while(pos<K){
    ll n=K+1;
    for(int p:factor(int(C-1)))
      if(p<=P)n=min(n,nextp(pos,p,0));
    for(int p:factor(int(C+1)))
      if(p<=P)n=min(n,nextp(pos,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
    for(int p:factor(raw))if(p<=P)e*=p;
    if(e<=1)throw runtime_error("nonunit first-hit missing");
    ev.push_back({n,C,e});
    pos=n;last=n;C+=e-1;
  }
  return {int(C-(2LL*m-2)),last,move(ev)};
}
pair<int,int> new_growth(int m,int P){
  int watched_p_hits=0;
  ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;
  while(pos<K){
    ll n=K+1;
    for(int p:factor(int(C-1)))
      if(p<=P)n=min(n,nextp(pos,p,0));
    for(int p:factor(int(C+1)))
      if(p<=P)n=min(n,nextp(pos,p,p+2));
    if(n>K)break;
    int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),e=1;
    for(int p:factor(raw))if(p<=P)e*=p;
    if(e<=1)throw runtime_error("nonunit first-hit missing");
    if(e%P==0)++watched_p_hits;
    pos=n;C+=e-1;
  }
  return {int(C-(2LL*m-2)),watched_p_hits};
}
struct Split{bool found;ll n;int post_deficit;bool post_freeze;};
Split first_split(int m,int p,const Path& old){
  ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;
  auto seek=[&](ll hi,int eold)->Split{
    ll n=K+1;
    if((C-1)%p==0)n=min(n,nextp(pos,p,0));
    if((C+1)%p==0)n=min(n,nextp(pos,p,p+2));
    if(n<=hi){
      int e=(n==hi)?eold:1;
      int x=int(2*n-(C+1LL*p*e-1));
      if(x<0)throw runtime_error("negative deficit");
      return {true,n,x,n>old.last};
    }
    return {false,0,0,false};
  };
  for(auto ev:old.events){
    auto r=seek(ev.n,ev.e);
    if(r.found)return r;
    pos=ev.n;C=ev.C+ev.e-1;
  }
  return seek(K,1);
}
int main(int argc,char**argv){
  int X=argc>1?atoi(argv[1]):4096;
  if(X!=1024&&X!=4096&&X!=16384)return 2;
  int B=int(ceil(sqrt(7.0*X))),limit=7*X+10000;
  spf.resize(limit);
  iota(spf.begin(),spf.end(),0);
  for(int p=2;1LL*p*p<limit;++p)if(spf[p]==p)
    for(int j=p*p;j<limit;j+=p)
      if(spf[j]==j)spf[j]=p;
  vector<int>primes;
  for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);
  // 0 split at or before old last;
  // 1 post-freeze X in {0,6};
  // 2 post-freeze X in {2p,2p+6};
  // 3 post-freeze OTHER X (typically >=4p, with p=3 special).
  array<ll,4>positive{},negative{},npos{},nneg{};
  ll low2_count=0,low2_cost=0,oneshot_count=0,oneshot_cost=0;
  for(size_t j=0;j<primes.size();++j){
    int p=primes[j],oldP=j?primes[j-1]:1;
    for(int m=X+1;m<2*X;m+=2){
      Path old=old_run(m,oldP);
      auto new_path=new_growth(m,p);
      int delta=new_path.first-old.growth;
      if(!delta)continue;
      Split z=first_split(m,p,old);
      if(!z.found)throw runtime_error("new wheel grew without initial p divergence");
      int group=0;
      if(z.post_freeze){
        if(z.post_deficit==0||z.post_deficit==6)group=1;
        else if(z.post_deficit==2*p||z.post_deficit==2*p+6)group=2;
        else group=3;
      }
      if(delta>0){positive[group]+=delta;++npos[group];}
      else{negative[group]-=delta;++nneg[group];}
      if(p>=11&&group==1&&old.growth<=2*p){
        ++low2_count;low2_cost+=delta;
        if(new_path.second==1){
          ++oneshot_count;oneshot_cost+=delta;
        }
      }
      if(group>0&&delta<0)
        throw runtime_error("post-freeze negative insertion contradicts exact theorem");
    }
  }
  const struct{int x;array<ll,4>p,n;} expected[]={
    {1024, {6726,12268,16452,4980},{486,0,0,0}},
    {4096,{57960,99878,162170,125670},{46536,0,0,0}},
    {16384,{369372,761250,1556242,752574},{524112,0,0,0}}
  };
  for(const auto& row:expected)if(X==row.x)
    if(positive!=row.p || negative!=row.n)
      throw runtime_error("finite signed partition regression mismatch");
  if(X==4096 && (low2_count!=883 || low2_cost!=85116
      || oneshot_count!=865 || oneshot_cost!=82806))
    throw runtime_error("4k moderate-postfreeze cost regression mismatch");
  if(X==16384 && (low2_count!=3960 || low2_cost!=690942
      || oneshot_count!=3791 || oneshot_cost!=655098))
    throw runtime_error("16k moderate-postfreeze cost regression mismatch");
  cout<<"PASS X="<<X<<" B="<<B<<" (category: positive,negative,count_pos,count_neg)\n";
  for(int i=0;i<4;++i)
    cout<<i<<": "<<positive[i]<<" "<<negative[i]
        <<" "<<npos[i]<<" "<<nneg[i]<<"\n";
  ll net=accumulate(positive.begin(),positive.end(),0LL)
         -accumulate(negative.begin(),negative.end(),0LL);
  cout<<"net="<<net<<"; post-freeze negative cost exactly zero\n";
  cout<<"postfreeze X0/6 p>=11 oldgrowth<=2p count="<<low2_count
      <<" positive_cost="<<low2_cost
      <<" one_shot_count="<<oneshot_count
      <<" one_shot_cost="<<oneshot_cost<<"\n";
  cout<<"Full dyadic insertion mean theorem remains OPEN\n";
}
