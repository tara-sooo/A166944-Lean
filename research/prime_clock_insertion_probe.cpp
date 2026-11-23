// Compare EXACT potential tau on S and S union {q}, full residue state graph.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_insertion_probe.cpp -o /tmp/insertion
#include <bits/stdc++.h>
using namespace std;
struct Graph{int P,T,N;vector<int>nx,budget;vector<short>g;long long sinks=0;
 Graph(vector<int> ps){P=1;for(int p:ps)P*=p;T=2*P;N=T*P;nx.assign(N,-1);g.assign(N,0);budget.assign(N,0);
 for(int t=0;t<T;t++)for(int h=0;h<P;h++){int best=100000,prod=1,C=2*h;
 for(int p:ps){int r=-1;if((C-1)%p==0)r=0;else if((C+1)%p==0)r=p+2;else continue;
 int z=(r-t)%(2*p);if(z<=0)z+=2*p;
 if(z<best){best=z;prod=p;}else if(z==best)prod*=p;}
 int s=t*P+h;
 if(prod==1){sinks++;continue;}
 nx[s]=((t+best)%T)*P+((h+(prod-1)/2)%P);g[s]=best;
 }
 vector<unsigned char> status(N,0);vector<int> st;st.reserve(200);
 for(int a=0;a<N;a++)if(!status[a]){int u=a;st.clear();while(u>=0&&!status[u]){status[u]=1;st.push_back(u);u=nx[u];}
 if(u>=0&&status[u]==1)throw runtime_error("CYCLE");
 while(!st.empty()){int x=st.back();st.pop_back();budget[x]=g[x]+(nx[x]<0?0:budget[nx[x]]);status[x]=2;}}
 }
 int query(int t,int h)const{return budget[(t%T)*P+(h%P)];}
};
void probe(vector<int> small,int q){vector<int> full=small;full.push_back(q);Graph g(small),f(full);int maxin=INT_MIN,minin=INT_MAX,maxt=0,maxSmall=0,maxFull=0,nAbove2=0,nAbove4=0,nPos=0;
 int wT=0,wH=0;
 for(int t=0;t<f.T;t++)for(int h=0;h<f.P;h++){
 int big=f.query(t,h),base=g.query(t,h),delta=big-base;
 if(delta>maxin){maxin=delta;wT=t;wH=h;maxt=big;}
 minin=min(minin,delta);maxSmall=max(maxSmall,base);maxFull=max(maxFull,big);
 nAbove2+=(delta>2*q);nAbove4+=(delta>4*q);nPos+=(delta>0);
 }
 cout<<"INSERTION_PROBE S=";for(int p:small)cout<<p<<",";
 cout<<" q="<<q<<" states="<<f.N<<" oldMax="<<maxSmall<<" newMax="<<maxFull<<" maxDelta="<<maxin
 <<" minDelta="<<minin<<" gt2q="<<nAbove2<<" gt4q="<<nAbove4<<" increasing="<<nPos
 <<" witness=(t="<<wT<<",C="<<2*wH<<") witnessTau="<<maxt<<"\n";
}
int main(){probe({3,5},7);probe({3,7},11);probe({5,7},11);probe({3,5,7},11);}
