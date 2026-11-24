#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using I=int64_t; using U=uint64_t;
struct Hit { int t,p; bool operator==(Hit b)const{return t==b.t&&p==b.p;} };
struct Wheel {
 int B; vector<int> spf;
 explicit Wheel(int X):B(int(ceil(sqrt(7.0*X)))),spf(7*X+212){for(int i=2;i<int(spf.size());++i)if(!spf[i]){spf[i]=i;if(I(i)*i<I(spf.size()))for(I j=I(i)*i;j<I(spf.size());j+=i)if(!spf[j])spf[j]=i;}}
 Hit hit(int t,int C,int K)const{Hit best{K+1,0};for(int sign:{-1,1}){int z=C+sign;while(z>1){int p=spf[z];if(p>B)break;if(p>2){int m=2*p,r=sign==-1?0:p+2,u=t+1+(r-(t+1)%m+m)%m;if(u<best.t||(u==best.t&&u<=K&&p<best.p))best={u,p};}while(z%p==0)z/=p;}}return best;}
 Hit literal(int t,int C,int K)const{for(int n=t+1;n<=K;++n){int z=n%2?gcd(n-2,C+1):gcd(n,C-1);while(z>1){int p=spf[z];if(p>B)break;if(p>2)return {n,p};while(z%p==0)z/=p;}}return {K+1,0};}
 bool twin(int C)const{return spf[C-1]==C-1&&spf[C+1]==C+1;}
 bool bigfactor(int z,int Q,int omit)const{while(z>1){int p=spf[z];if(p>B)break;if(p>=Q&&p!=omit)return true;while(z%p==0)z/=p;}return false;}
};
// Count key multiplicities over ORIGINAL sources, with all prefix ranks pooled.
struct Energy {I keys=0,total=0,maxw=0,energy=0;};
Energy count(vector<U>& a){sort(a.begin(),a.end());Energy e;for(size_t i=0,j;i<a.size();i=j){for(j=i+1;j<a.size()&&a[j]==a[i];++j){}I w=j-i;++e.keys;e.total+=w;e.maxw=max(e.maxw,w);e.energy+=w*w;}return e;}
void run(int X){assert(X>=256&&X%4==0);Wheel w(X);int B=w.B,y=7,L=210,Q=int(ceil(B/pow(log(B),2.0/3))),a=int(ceil(pow(log(B),1.0/3))),P=0,Ps=0;for(int p=11;p<=B;++p)if(w.spf[p]==p){++P;Ps+=p<Q;}int m=2*P;I N=X/2;vector<U> large,small,risk;vector<int> counts(B+1),used;I H=0,Hs=0,Hl=0,A=0,Uadj=0,smallToLarge=0,firstLarge=0,checks=0,twins=0,ends=0,maxLen=0;const U stride=U(7)*X+212;
 for(int M=X+1;M<2*X;M+=2){int t=M+2,C=2*M-2,K=(7*M-1)/4,j=0,qprev=0,Cprev=0;used.clear();for(;;){Hit h=w.hit(t,C,K);if(X<=1024){assert(h==w.literal(t,C,K));++checks;}if(!h.p){++ends;twins+=w.twin(C);break;}int p=h.p;t=h.t;int Cbefore=C;C+=p-1;assert(C<=2*t);if(p<=y)continue;++j;++H;if(!counts[p]++)used.push_back(p);if(p<Q){++Hs;small.push_back(U(p)*stride+C);}else{++Hl;large.push_back(U(p)*stride+C);if(!qprev)++firstLarge;else if(qprev<Q)++smallToLarge;else{++Uadj;int E=Cbefore-Cprev;assert(0<=E&&E<L&&E%2==0);assert(Cprev%qprev==0||(Cprev+2)%qprev==0);if(p==qprev)assert(p-1<L);else risk.push_back(U(qprev)*stride+Cprev);}}
 qprev=p;Cprev=C;if(j==m)break;}
 maxLen=max(maxLen,I(j));for(int p:used){if(p<Q)A+=max(0,counts[p]-1-a);counts[p]=0;}}
 assert(H==Hs+Hl&&Hl==Uadj+smallToLarge+firstLarge);assert(smallToLarge<=Hs&&firstLarge<=N);assert(Hs<=A+N*Ps*(a+1));
 Energy el=count(large),es=count(small),er=count(risk);assert(el.total==Hl&&es.total==Hs);assert(er.total<=Uadj);assert((long double)er.total*er.total<= (long double)er.keys*el.energy);
 // Exact relaxed arithmetic key set: q>=Q, C even and q|C or q|C+2;
 // some DIFFERENT p>=Q divides C+e+-1 for even 0<=e<L.
 I S=0,Sall=0;for(int q=max(Q,11);q<=B;++q)if(w.spf[q]==q){for(int off:{0,-2}){I start=2*I(X);I z=start+((off-start)%(2*q)+2*q)%(2*q);for(I C=z;C<7*I(X);C+=2*q){++Sall;bool ok=false;for(int e=0;e<L&&!ok;e+=2)ok=w.bigfactor(int(C)+e-1,Q,q)||w.bigfactor(int(C)+e+1,Q,q);S+=ok;}}}
 assert(er.keys<=S);I same=Uadj-er.total; if(Q>L+1)assert(same==0); long double bound=sqrtl((long double)S*el.energy)+same;
 cout<<"X="<<X<<" B="<<B<<" P="<<P<<" Q="<<Q<<" a="<<a<<" H="<<H<<" Hs="<<Hs<<" Hl="<<Hl<<" A="<<A<<" U="<<Uadj<<" same="<<same<<" S="<<S<<" Sall="<<Sall<<" keys="<<el.keys<<" maxw="<<el.maxw<<" E="<<el.energy<<" smallE="<<es.energy<<" riskKeys="<<er.keys<<" maxRiskW="<<er.maxw<<" riskE="<<er.energy<<" CS_over_XP="<<double(bound/(I(X)*P))<<" E_loglog2_over_X2="<<double((long double)el.energy*pow(log(log(B)),2)/(I(X)*X))<<" A_over_XP="<<double((long double)A/(I(X)*P))<<" maxLen="<<maxLen<<" ends="<<ends<<" twins="<<twins<<" checks="<<checks<<"\n";
}
int main(int argc,char**argv){for(int i=1;i<argc;++i)run(stoi(argv[i]));}
