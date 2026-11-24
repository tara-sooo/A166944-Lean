#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
#include <set>
using namespace std;
using I=int64_t;
struct Hit {int t,p; bool operator==(const Hit& h) const {return t==h.t&&p==h.p;}};
struct State {int t,c;};
struct Wheel {
 int B; vector<int> spf;
 Wheel(int X): B(int(ceil(sqrt(7.0*X)))),spf(7*X+64) {
  for(int i=2;i<(int)spf.size();++i) if(!spf[i]) {spf[i]=i;if(I(i)*i<(I)spf.size()) for(I j=I(i)*i;j<(I)spf.size();j+=i) if(!spf[j])spf[j]=i;}
 }
 Hit hit(State s,int K,int omit=0) const {
  Hit best{K+1,0};
  for(int sign : {-1,1}){int z=s.c+sign;assert(z>0&&z<(int)spf.size());while(z>1){int p=spf[z];if(p> B) break;if(p>2&&p!=omit){int m=2*p,r=(sign==-1?0:p+2);int u=s.t+1+(r-(s.t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(z%p==0) z/=p;}}
  return best;
 }
 Hit literal(State s,int K,int omit=0) const {
  for(int n=s.t+1;n<=K;++n){int z=n%2?gcd(n-2,s.c+1):gcd(n,s.c-1);while(z>1){int p=spf[z];if(p>B)break;if(p>2&&p!=omit)return {n,p};while(z%p==0)z/=p;}}return {K+1,0};
 }
 bool twin(int c) const{return spf[c-1]==c-1&&spf[c+1]==c+1;}
 Hit shadow_return(State s,int K,int p) const {
  for(;;){Hit q=hit(s,K,p);int r=-1;if((s.c-1)%p==0)r=0;else if((s.c+1)%p==0)r=p+2;
   if(r>=0){int m=2*p;int u=s.t+1+(r-(s.t+1)%m+m)%m;if(u<=K&&(u<q.t||(u==q.t&&p<q.p)))return {u,p};}
   if(!q.p)return {K+1,0};
   s={q.t,s.c+q.p-1};
  }
 }
};
struct Stats {
 vector<I> hist{0}; I H=0,F=0,Z=0;
 void add(int n){if(n>=(int)hist.size())hist.resize(n+1);++hist[n];H+=n;++F;Z+=I(n)*n;}
 void out(const char* label){vector<I> D(hist.size()+1);for(int k=(int)hist.size()-1;k>=1;--k)D[k]=D[k+1]+hist[k];double mx=0;int at=0;for(int k=1;k<(int)hist.size();++k){double v=2*k<(int)D.size()?double(D[2*k])/D[k]:0;if(v>mx){mx=v;at=k;}}cout<<label<<" H="<<H<<" F="<<F<<" Z="<<Z<<" maxN="<<hist.size()-1<<" maxRatio="<<mx<<" at="<<at<<" tails=";for(int k=1;k<(int)hist.size();k*=2)cout<<k<<":"<<D[k]<<",";cout<<"\n";}
};
void audit(int X){Wheel w(X);int B=w.B,y=2,L=2,P=0;for(int p=3;p<=B;p+=2)if(w.spf[p]==p&&I(L)*p<=sqrt(B)){L*=p;y=p;}for(int p=y+1;p<=B;++p)if(w.spf[p]==p)++P;
 int P7=0;for(int p=11;p<=B;++p)if(w.spf[p]==p)++P7;
 int Q=int(ceil(B/pow(log(B),1.0/3))), cap=int(ceil(pow(log(B),1.0/6)));
 Stats a,b,c,d,e; vector<int> cnt(B+1),sample(B+1),used,high;
 vector<pair<int,int>> prefix;vector<int> prev(B+1,-1);vector<int> prefixUsed;
 I Dfull=0,small=0,excess=0,one=0,multi=0,zero=0,maxGrowth=0;set<pair<int,int>> oneStates; I twins=0,checks=0,shadowchecks=0,recharge=0,oddDeficit=0;
 for(int M=X+1;M<2*X;M+=2){State s{M+2,2*M-2};int K=(7*M-1)/4;used.clear();high.clear();prefix.clear();prefixUsed.clear();vector<pair<int,State>> trace;bool verify=X<=1024 || M<X+129;
  for(;;){Hit h=w.hit(s,K);if(X<=1024){assert(h==w.literal(s,K));++checks;}if(!h.p)break;int p=h.p;if(!cnt[p]++)used.push_back(p);if(p>y)high.push_back(p);if(p>7 && (int)prefix.size()<2*P7)prefix.push_back({p,s.c});s={h.t,s.c+p-1};if(verify)trace.push_back({p,s});}
  twins+=w.twin(s.c);
  for(int j=0;j<(int)prefix.size();++j){auto [p,C]=prefix[j];maxGrowth=max(maxGrowth,I(C-(2*M-2)));assert(I(C-(2*M-2))<=I(2)*P7*(B+210));
   if(prev[p]<0){prefixUsed.push_back(p);}else{++Dfull;if(p<Q){++small;}else{int d=j-prev[p];if(d==1){++zero;assert(p<840);}else if(d==2){++one;oneStates.insert({prefix[prev[p]].second,p});}else ++multi;}}prev[p]=j;
  }
  for(int p:prefixUsed){if(p<Q){int n=0;for(auto [q,C]:prefix){(void)C;if(q==p)++n;}excess+=max(0,n-1-cap);}prev[p]=-1;}

  for(int p:used){int n=cnt[p];if(p>y)a.add(n);if(p>7)b.add(n);if(p>19)c.add(n);if(4*P<p)d.add(n);cnt[p]=0;}
  for(int j=0;j<(int)high.size()&&j<4*P;j+=2)++sample[high[j]];
  for(int p:used)if(sample[p]){e.add(sample[p]);oddDeficit+=sample[p]-1;sample[p]=0;}
  if(verify){for(size_t j=0;j<trace.size();++j){int p=trace[j].first;State z=trace[j].second;Hit expected{K+1,0};for(size_t k=j+1;k<trace.size();++k)if(trace[k].first==p){expected={trace[k].second.t,p};int E=trace[k].second.c-(p-1)-z.c;if(p>=5){assert(E>=p-1);if(E<=2*p)assert(E==p-1||E==p+1||E==p+3);++recharge;}break;}Hit actual=w.shadow_return(z,K,p);assert(expected==actual);++shadowchecks;}}
 }
 assert(Dfull==small+zero+one+multi);
 cout<<"2P fixed LOW7 Q="<<Q<<" cap="<<cap<<" P7="<<P7<<" fullD="<<Dfull<<" small="<<small<<" excess="<<excess<<" large_zero="<<zero<<" large_one="<<one<<" large_multi="<<multi<<" unique_one_states="<<oneStates.size()<<" maxGrowth="<<maxGrowth<<"\n";
 cout<<"X="<<X<<" B="<<B<<" y="<<y<<" L="<<L<<" P="<<P<<" twins="<<twins<<" literal="<<checks<<" shadow="<<shadowchecks<<" recharge="<<recharge<<" Dodd="<<oddDeficit<<"\n";a.out("growing");b.out("p>7");c.out("p>19");d.out("p>4P");e.out("odd sample");cout.flush();
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)audit(stoi(argv[i]));}
