// Heuristic (NOT exhaustive) CRT-residue search for long prime-clock paths.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_adversarial_search.cpp -o /tmp/clock_search
// /tmp/clock_search 31 50000
// /tmp/clock_search 251 45000
// RNG seed is fixed. Any printed maxima are achieved finite lower bounds on WORST-CASE time.
// A missing cycle in this search is NOT a theorem about general prime alphabets.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
using ll=long long;
static mt19937_64 rng(20261123);
struct State {ll t;vector<int> c;};
int main(int argc,char** argv){
 int B=argc>1?atoi(argv[1]):47;
 int repeats=argc>2?atoi(argv[2]):50000;
 vector<int> ps;
 for(int p=3;p<=B;p+=2){bool prime=true;for(int d=3;d*d<=p;d+=2)if(p%d==0)prime=false;if(prime)ps.push_back(p);}
 int k=ps.size(),sum=accumulate(ps.begin(),ps.end(),0);
 vector<int> timeMod(k);
 auto assess=[&](State const& s)->pair<int,int>{
  vector<int> cm=s.c;
  for(int j=0;j<k;j++)timeMod[j]=int(s.t%(2LL*ps[j]));
  int tm=0,events=0;
  for(int count=0;count<30000;count++){
   int g=1000000000;vector<int> tied;
   for(int j=0;j<k;j++){
    int p=ps[j],r;
    if(cm[j]==1)r=0;
    else if(cm[j]==p-1)r=p+2;
    else continue;
    int z=(r-timeMod[j]+2*p)%(2*p);
    if(z==0)z=2*p;
    if(z<g){g=z;tied.clear();tied.push_back(j);}else if(z==g)tied.push_back(j);
   }
   if(g>2*B)break;
   tm+=g;events++;
   for(int j=0;j<k;j++){
    int r=1;for(int a:tied)r=int((1LL*r*ps[a])%ps[j]);
    cm[j]=(cm[j]+r-1+ps[j])%ps[j];
    timeMod[j]=(timeMod[j]+g)%(2*ps[j]);
   }
   if(tm>10000000)break;
  }
  return {tm,events};
 };
 State cur{0,vector<int>(k)};
 auto init=[&](){cur.t=(ll)(rng()&((1LL<<52)-1));for(int j=0;j<k;j++)cur.c[j]=rng()%ps[j];};
 init();int current=assess(cur).first;int global=0,maxevents=0;int updates=0;
 for(int i=0;i<repeats;i++){
  State candidate=cur;
  int a=rng()%100;
  if(a<57){int j=rng()%k;candidate.c[j]=rng()%ps[j];}
  else if(a<80){int j=rng()%k;candidate.c[j]=(candidate.c[j]+(rng()%2?1:ps[j]-1))%ps[j];}
  else if(a<95){candidate.t+=ll((int)(rng()%(4*B+1))-2*B);if(candidate.t<0)candidate.t=-candidate.t;}
  else {candidate.t=rng()&((1LL<<52)-1);}
  auto [tm,ne]=assess(candidate);
  double temperature=20.0+100.0*(1.0-double(i)/repeats);
  if(tm>=current || double(rng()%1000000)/1000000.0<exp(double(tm-current)/temperature)){
   cur=move(candidate);current=tm;
  }
  if(tm>global){global=tm;maxevents=ne;updates++;}
  if(i%5000==4999){init();current=assess(cur).first;}
 }
 cout<<"ADVERSARIAL B="<<B<<" primes="<<k<<" iterations="<<repeats
 <<" sumPrimes="<<sum<<" maxTime="<<global<<" maxEvents="<<maxevents
 <<" ratio="<<double(global)/sum<<" improvements="<<updates<<'\n';
}
