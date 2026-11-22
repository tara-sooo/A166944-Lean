#include <bits/stdc++.h>
using namespace std;
static constexpr int P=3*5*7*11, T=2*P,N=T*P;
static const int ps[]={3,5,7,11};
int nextgap(int t,int p,int r){int a=(r-t)%(2*p);if(a<=0)a+=2*p;return a;}
int main(){
 vector<int> nxt(N,-1), d(N,0),depth(N,-1),rootGrowth(N,-1);int sinks=0;
 for(int t=0;t<T;t++)for(int c2=0;c2<P;c2++){
  int c=2*c2, idx=t*P+c2,gap=10000000,mult=1;
  for(int p:ps){int rem;
    if((c-1)%p==0) rem=0;
    else if((c+1)%p==0)rem=p+2;
    else continue;
    int v=nextgap(t,p,rem);
    if(v<gap){gap=v;mult=p;}else if(v==gap)mult*=p;
  }
  if(gap==10000000){sinks++;continue;}
  nxt[idx]=((t+gap)%T)*P + ( (c+mult-1)%T )/2;
  d[idx]=mult;
  if(idx%(N/997+1)==0){
    int directGap=-1,directD=1,tt=t+4*T,cc=c+4*T;
    for(int step=1;step<=2*ps[sizeof(ps)/sizeof(ps[0])-1];step++){
      int n=tt+step,raw=int(gcd((n&1)?n-2:n,(n&1)?cc+1:cc-1)),prod=1;
      for(int prime:ps)if(raw%prime==0)prod*=prime;
      if(prod>1){directGap=step;directD=prod;break;}
    }
    if(directGap!=gap||directD!=mult)throw runtime_error("independent literal low-step mismatch");
  }
 }
 vector<int> indeg(N,0);for(int a:nxt)if(a>=0)indeg[a]++;
 vector<int> q;q.reserve(N);for(int i=0;i<N;i++)if(!indeg[i])q.push_back(i);
 for(size_t i=0;i<q.size();i++){int x=nxt[q[i]];if(x>=0&&--indeg[x]==0)q.push_back(x);}
 if(q.size()!=N)throw runtime_error("cycle");
 int maxDepth=0, maxGrowth=0;
 for(int i=N-1;i>=0;i--){int s=q[i];depth[s]=nxt[s]<0?0:1+depth[nxt[s]];rootGrowth[s]=nxt[s]<0?0:d[s]-1+rootGrowth[nxt[s]];maxDepth=max(maxDepth,depth[s]);maxGrowth=max(maxGrowth,rootGrowth[s]);}
 vector<uint8_t> seen(maxGrowth+1,0);seen[0]=1;
 vector<int> witness(maxGrowth+1,-1);
 for(int s=0;s<N;s++){
    int e=0,t=s;
    while(nxt[t]>=0){e+=d[t]-1;t=nxt[t];if(e>maxGrowth)throw runtime_error("bad growth bound"); if(!seen[e]){seen[e]=1;witness[e]=s;}}
 }
 vector<int> spf(maxGrowth+8);iota(spf.begin(),spf.end(),0);
 for(int i=2;1LL*i*i<(int)spf.size();i++)if(spf[i]==i)for(int j=i*i;j<(int)spf.size();j+=i)if(spf[j]==j)spf[j]=i;
 set<int> exceptional;int maxFactor=0,maxE=0,nonzero=0;map<int,int> maxCauses;
 for(int e=0;e<(int)seen.size();e++)if(seen[e]){
    nonzero++;maxE=max(maxE,e);
    for(int x:{e-3,e-1,e+1}){
      int a=abs(x);if(a<2)continue;
      while(a>1){int p=spf[a];while(a%p==0)a/=p; if(p>11){exceptional.insert(p);maxFactor=max(maxFactor,p);maxCauses[p]=e;}}
    }
 }
 int canonicalMaxZ=0,canonicalMaxE=0,canonicalMaxGrowth=0,canonicalPlateaus=0;
 for(int M=1;M<T;M+=2){
   int t=M+2,C=2*M-2,E=0;
   while(true){
     canonicalPlateaus++;canonicalMaxZ=max(canonicalMaxZ,2*t-C);
     int gap=INT_MAX,dNow=1;
     for(int p:ps){int residue;
       if((C-1)%p==0)residue=0;
       else if((C+1)%p==0)residue=p+2;
       else continue;
       int v=nextgap(t,p,residue);
       if(v<gap){gap=v;dNow=p;}else if(v==gap)dNow*=p;
     }
     if(gap==INT_MAX)break;
     t+=gap;C+=dNow-1;E++;
     if(E>maxDepth)throw runtime_error("canonical > arbitrary-state longest path");
   }
   canonicalMaxE=max(canonicalMaxE,E);
   canonicalMaxGrowth=max(canonicalMaxGrowth,C-(2*M-2));
 }
 cout<<"CANONICAL_LOW P="<<P<<" residues="<<P<<" plateaus="<<canonicalPlateaus
     <<" maxZ="<<canonicalMaxZ<<" maxEvents="<<canonicalMaxE<<" maxGrowth="<<canonicalMaxGrowth<<"\n";
 if(P==1155 && (canonicalPlateaus!=4940 || canonicalMaxZ!=146 || canonicalMaxE!=18))
   throw runtime_error("canonical 11-wheel checkpoint mismatch");
 if(maxDepth!=22 || maxGrowth!=1156 || sinks!=311850 || nonzero!=138 || exceptional.size()!=58 || maxFactor!=1153)
   throw runtime_error("exhaustive all-state refractory regression mismatch");
 cout<<"P="<<P<<" states="<<N<<" sinks="<<sinks<<" maxDepth="<<maxDepth<<" maxGrowth="<<maxGrowth<<" attainablePrefixGrowths="<<nonzero<<" maxPrefix="<<maxE<<" distinctHighRepeatPrimes="<<exceptional.size()<<" maxRepeatPrime="<<maxFactor<<"\n";
 cout<<"REPEAT_PRIMES";for(int p:exceptional)cout<<" "<<p<<":"<<maxCauses[p];cout<<"\n";
 cout<<"ATTAINABLE_PREFIXES";for(int e=0;e<(int)seen.size();e++)if(seen[e])cout<<" "<<e;cout<<"\n";
}
