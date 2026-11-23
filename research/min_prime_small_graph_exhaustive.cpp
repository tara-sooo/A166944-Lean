// Exact MIN prime-clock full CRT graph for SMALL finite alphabets.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_small_graph_exhaustive.cpp -o /tmp/mingraph
// /tmp/mingraph 3 5 7 11
#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 vector<int>ps;int P=1;
 for(int i=1;i<argc;i++){
  int p=atoi(argv[i]);if(p<3||p%2==0||P>4000/p)return 2;
  ps.push_back(p);P*=p;
 }
 if(ps.empty())return 2;
 int N=2*P*P;
 vector<int>nxt(N,-1),time(N,0),events(N,0);
 vector<uint8_t>gap(N),status(N);
 long long sinks=0;int cycles=0,maxtime=0,maxevents=0;
 for(int t=0;t<2*P;t++)for(int h=0;h<P;h++){
  int C=2*h,g=INT_MAX,choice=0;
  for(int p:ps){
   int r=(C-1)%p==0?0:((C+1)%p==0?p+2:-1);
   if(r<0)continue;
   int dt=((r-t)%(2*p)+2*p)%(2*p);if(dt==0)dt=2*p;
   if(dt<g||(dt==g&&p<choice)){g=dt;choice=p;}
  }
  int v=t*P+h;
  if(!choice){sinks++;continue;}
  nxt[v]=((t+g)%(2*P))*P+(h+(choice-1)/2)%P;
  gap[v]=g;
 }
 vector<int>stack;stack.reserve(128);
 for(int v=0;v<N;v++){
  if(status[v])continue;
  stack.clear();int z=v;
  while(z>=0&&status[z]==0){status[z]=1;stack.push_back(z);z=nxt[z];}
  if(z>=0&&status[z]==1){cycles++;break;}
  while(!stack.empty()){
   int u=stack.back();stack.pop_back();int w=nxt[u];
   time[u]=gap[u]+(w>=0?time[w]:0);
   events[u]=w>=0?1+events[w]:0;
   status[u]=2;
   maxtime=max(maxtime,time[u]);maxevents=max(maxevents,events[u]);
  }
 }
 cout<<"MIN_GRAPH_FULL P="<<P<<" states="<<N<<" sinks="<<sinks
     <<" cycles="<<cycles<<" maxTime="<<maxtime<<" maxEvents="<<maxevents<<"\n";
 return cycles?3:0;
}
