// Exact finite-state prime-clock graph for a specified SMALL squarefree prime alphabet.
// Reproduce: g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_automaton_exhaustive.cpp -o /tmp/clock
// Example: /tmp/clock 3 5 7 11
// The state space has exactly 2*P*P elements, P=product of the input primes.
// Source: independent clock graph, not a proof for arbitrarily many primes.
#include <algorithm>
#include <climits>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 vector<int>ps;int P=1;
 for(int i=1;i<argc;i++){int p=atoi(argv[i]);if(p<3||p%2==0||P>5000/p)return 2;ps.push_back(p);P*=p;}
 if(ps.empty()||2LL*P*P>50000000)return 2;
 int T=2*P,N=T*P;
 vector<int>nxt(N,-1),etime(N),ecount(N),egrow(N);
 vector<unsigned short>gapv(N,0),growv(N,0);
 long long sinks=0;
 for(int t=0;t<T;t++)for(int h=0;h<P;h++){
  int C=2*h,best=INT_MAX,d=1;
  for(int p:ps){int r;
   if((C-1)%p==0)r=0;
   else if((C+1)%p==0)r=p+2;
   else continue;
   int g=((r-t)%(2*p)+(2*p))%(2*p);
   if(!g)g=2*p;
   if(g<best){best=g;d=p;}else if(g==best)d*=p;
  }
  int s=t*P+h;
  if(d==1){sinks++;continue;}
  nxt[s]=((t+best)%T)*P+((h+(d-1)/2)%P);
  gapv[s]=best;growv[s]=d-1;
 }
 vector<unsigned char>mark(N);
 int maxevents=0,maxtime=0,maxgrowth=0,cycle=0;
 vector<int>path;path.reserve(1000);
 for(int x=0;x<N;x++)if(!mark[x]){
  path.clear();int y=x;
  while(y!=-1&&mark[y]==0){mark[y]=1;path.push_back(y);y=nxt[y];}
  if(y!=-1&&mark[y]==1){cycle=1;cerr<<"CYCLE state="<<y<<"\n";break;}
  for(auto it=path.rbegin();it!=path.rend();it++){
   int s=*it,r=nxt[s];
   if(r<0){ecount[s]=0;etime[s]=0;egrow[s]=0;}
   else{ecount[s]=1+ecount[r];etime[s]=gapv[s]+etime[r];egrow[s]=growv[s]+egrow[r];}
   mark[s]=2;
   maxevents=max(maxevents,ecount[s]);
   maxtime=max(maxtime,etime[s]);
   maxgrowth=max(maxgrowth,egrow[s]);
  }
 }
 cout<<"CLOCK_FINITE_PASS P="<<P<<" states="<<N<<" sinks="<<sinks
 <<" cycle="<<cycle<<" maxevents="<<maxevents<<" maxtime="<<maxtime
 <<" maxgrowth="<<maxgrowth<<" sumprimes="<<accumulate(ps.begin(),ps.end(),0)<<"\n";
 return cycle?3:0;
}
