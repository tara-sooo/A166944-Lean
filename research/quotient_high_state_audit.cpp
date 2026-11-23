// Original parity-specific clipped GCD, full time-sweep of cohort first mergers.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror first_merger_genealogy_audit.cpp -o first_merger_genealogy_audit
// ./first_merger_genealogy_audit 256 512 1024 4096 16384 65536
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>
using namespace std;
using ll=long long;
struct Action{int n,typ,id,c0,c1,weight;}; // typ 0 expiration, 1 move, 2 birth
struct High{int n;ll cumulative;};
static vector<int> spf;
static void sieve(int z){spf.resize(z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<z;++p)if(spf[p]==p)for(int j=p*p;j<z;j+=p)if(spf[j]==j)spf[j]=p;}
static void fac(int n,vector<int>&v){v.clear();while(n>1){int p=spf.at(n);v.push_back(p);do{n/=p;}while(n%p==0);}}
static int clk(ll t,int q,int r){int a=int((r-t)%(2LL*q));if(a<=0)a+=2*q;return a;}
static ll literal(int M,int B){ll c=2LL*M-2,c0=c,K=(7LL*M-1)/4;vector<int>v;for(ll n=M+3;n<=K;n++){int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(raw,v);int d=1;for(int p:v)if(p<=B)d*=p;c+=d-1;}return c-c0;}
static ll jump(int M,int B){ll c=2LL*M-2,c0=c,t=M+2,K=(7LL*M-1)/4;vector<int>v;while(t<K){ll n=K+1;fac(int(c-1),v);for(int p:v)if(p<=B)n=min(n,t+clk(t,p,0));fac(int(c+1),v);for(int p:v)if(p<=B)n=min(n,t+clk(t,p,p+2));if(n>K)break;int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(raw,v);int d=1;for(int p:v)if(p<=B)d*=p;c+=d-1;t=n;}return c-c0;}
struct Stats{ll newPairs=0,credit=0,firstCredit=0,zeroFuturePairs=0,oneFuturePair=0,futureHighCount=0;};
static void run(int X){
 const int B=int(ceill(sqrtl(7.L*X))), N=X/2;
 vector<Action>actions;actions.reserve(size_t(X)*14);
 vector<vector<High>>high(N);
 vector<ll>totalQ(N,0);
 vector<int>location(N,-1);
 vector<int>f;
 ll totalHigh=0,totalHits=0,totalGrowth=0;
 for(int id=0;id<N;++id){
   const int M=X+1+2*id,s=M+2,K=(7LL*M-1)/4;
   actions.push_back({s,2,id,0,2*M-2,0});actions.push_back({K+1,0,id,0,0,0});
   ll c=2LL*M-2,t=s,qsum=0;
   while(t<K){
     ll n=K+1;
     fac(int(c-1),f);for(int p:f)if(p<=B)n=min(n,t+clk(t,p,0));
     fac(int(c+1),f);for(int p:f)if(p<=B)n=min(n,t+clk(t,p,p+2));
     if(n>K)break;
     int raw=int(gcd((n&1)?n-2:n,(n&1)?c+1:c-1));fac(raw,f);int d=1,w=0;
     for(int p:f)if(p<=B){d*=p;if(p>=13){w+=p;totalHits++;}}
     if(d<=1)throw runtime_error("invalid nonunit event");
     actions.push_back({int(n),1,id,int(c),int(c)+d-1,w});
     if(w){high[id].push_back({int(n),qsum+=w});totalHigh++;}
     c+=d-1;t=n;
   }
   totalQ[id]=qsum;totalGrowth+=c-(2LL*M-2);
 }
 sort(actions.begin(),actions.end(),[](const Action&a,const Action&b){if(a.n!=b.n)return a.n<b.n;if(a.typ!=b.typ)return a.typ<b.typ;return a.id<b.id;});
 unordered_map<int,vector<int>>groups;groups.reserve(N*2);
 auto remaining=[&](int id,int n)->ll{
   const auto& v=high[id];auto it=upper_bound(v.begin(),v.end(),n,[](int k,const High&z){return k<z.n;});
   const ll used=(it==v.begin()?0:(it-1)->cumulative);
   return totalQ[id]-used;
 };
 Stats born,low,highMerge,multiMerge;ll joinedEnergy=0,events=0,newPairs=0,mergedQCredit=0;
 ll maxCohort=0,maxMergedCohort=0;ll birthCollisions=0,foldCollisions=0;ll boundaryDeaths=0;ll uniqueHighNodes=0,uniqueQWeight=0,uniqueHighMass=0,quotientArea=0,sourceArea=0,maxSupport=0,peakAlive=0;int prevTime=X+2;
 auto mergegroups=[&](vector<vector<int>>&&parts,int t,int typ){
   // typ 0 birth, 1 update where A_n has only primes below 13, 2 has high prime, 3 mixed high factors
   if(parts.empty())throw runtime_error("no parts");
   ll mass=0,cross=0;for(auto&part:parts){if(part.empty())throw runtime_error("empty part");cross+=mass*ll(part.size());mass+=part.size();}
   vector<int>out;out.reserve(mass);
   if(parts.size()>1){
     vector<pair<int,int>> all;all.reserve(mass);
     for(int k=0;k<int(parts.size());++k)for(int id:parts[k])all.push_back({id,k});
     sort(all.begin(),all.end());
     vector<int>higher(parts.size(),0);
     ll others=0,credit=0,firstCredit=0,zeroFuturePairs=0,oneFuturePair=0,futureHighCount=0;int remain=0;
     for(int v=int(all.size())-1;v>=0;--v){
       auto[id,k]=all[v];ll later=remain-higher[k];
       if(later<0)throw runtime_error("negative later");
       others+=later;credit+=later*remaining(id,t);
       if(later){
         const auto& v=high[id];
         const auto it=upper_bound(v.begin(),v.end(),t,[](int k,const High&z){return k<z.n;});
         const ll events=ll(v.end()-it);
         futureHighCount+=later*events;
         if(events==0)zeroFuturePairs+=later;
         else {
           const ll prev=it==v.begin()?0:(it-1)->cumulative;
           firstCredit+=later*(it->cumulative-prev);
           if(events==1)oneFuturePair+=later;
           if(it->n-t>133+2LL*int(ceill(sqrtl(7.L*X))))throw runtime_error("first shared high lag exceeds universal bound");
         }
       }
       higher[k]++;remain++;
     }
     if(others!=cross)throw runtime_error("cross pair formula mismatch");
     newPairs+=cross;mergedQCredit+=credit;
     Stats*bucket=typ==0?&born:(typ==1?&low:(typ==2?&highMerge:&multiMerge));
     bucket->newPairs+=cross;bucket->credit+=credit;bucket->firstCredit+=firstCredit;bucket->zeroFuturePairs+=zeroFuturePairs;bucket->oneFuturePair+=oneFuturePair;bucket->futureHighCount+=futureHighCount;
     if(typ==0)birthCollisions++;else foldCollisions++;
     maxMergedCohort=max(maxMergedCohort,mass);
   }
   for(auto&part:parts)out.insert(out.end(),part.begin(),part.end());
   maxCohort=max(maxCohort,mass);
   return out;
 };
 ll times=0,activeMass=0;
 for(size_t i=0;i<actions.size();){
   const int n=actions[i].n;size_t j=i+1;while(j<actions.size()&&actions[j].n==n)j++;
   quotientArea+=ll(n-prevTime)*groups.size();
   sourceArea+=ll(n-prevTime)*activeMass;
   prevTime=n;
   size_t a=i;
   // expire before step n: K+1
   while(a<j&&actions[a].typ==0){int id=actions[a].id,c=location[id];
     if(c<0)throw runtime_error("expire unknown source");
     auto it=groups.find(c);if(it==groups.end())throw runtime_error("expire missing state");
     auto& vec=it->second;auto k=find(vec.begin(),vec.end(),id);if(k==vec.end())throw runtime_error("expire missing id");
     vec.erase(k);if(vec.empty())groups.erase(it);location[id]=-1;boundaryDeaths++;activeMass--;a++;
   }
   // compute each distinct pre-state update while all simultaneous movers still in pre groups
   unordered_map<int,pair<int,int>>pre;pre.reserve((j-a)*2+1);
   unordered_map<int,int>moverCounts;moverCounts.reserve((j-a)*2+1);
   while(a<j&&actions[a].typ==1){const Action&z=actions[a];
     if(location[z.id]!=z.c0)throw runtime_error("event prestate differs from source state");
     auto it=pre.find(z.c0);
     if(it==pre.end()){pre.emplace(z.c0,make_pair(z.c1,z.weight));}
     else if(it->second.first!=z.c1||it->second.second!=z.weight)throw runtime_error("same prestate different transition");
     moverCounts[z.c0]++;a++;
   }
   for(const auto& [c,params]:pre){
     const int w=params.second;
     auto it=groups.find(c);if(it==groups.end())throw runtime_error("update missing group");
     if(int(it->second.size())!=moverCounts.at(c))throw runtime_error("not all cohort members updated together");
     if(w>0){ll m=it->second.size();joinedEnergy+=ll(w)*m*(m-1);uniqueHighNodes++;uniqueQWeight+=w;uniqueHighMass+=m;}
     events+=it->second.size();
   }
   // collect destination parts in batch; this prevents artificial sequential merges
   unordered_map<int,vector<vector<int>>>pending;pending.reserve(pre.size()*2+1);
   for(const auto& [c,params]:pre){int target=params.first;auto it=groups.find(c);
     vector<int>group=move(it->second);groups.erase(it);
     for(int id:group)location[id]=target;
     pending[target].push_back(move(group));
   }
   for(auto&entry:pending){
     const int target=entry.first;auto& parts=entry.second;
     auto at=groups.find(target);if(at!=groups.end()){parts.push_back(move(at->second));groups.erase(at);}
     int eventWeight=0;int factorCount=0;
     for(const auto& z:pre)if(z.second.first==target&&z.second.second>0){eventWeight+=z.second.second;factorCount++;}
     const int typ=eventWeight==0?1:(factorCount>1?3:2);
     groups.emplace(target,mergegroups(move(parts),n,typ));
   }
   // births at s(M), AFTER update n, since this source starts at the post-step n plateau
   while(a<j&&actions[a].typ==2){const auto&z=actions[a];
     if(location[z.id]>=0)throw runtime_error("birth source already active");
     location[z.id]=z.c1;activeMass++;
     auto it=groups.find(z.c1);
     if(it==groups.end())groups.emplace(z.c1,vector<int>{z.id});
     else{vector<vector<int>> parts;parts.push_back(move(it->second));parts.push_back({z.id});it->second=mergegroups(move(parts),n,0);}
     a++;
   }
   if(a!=j)throw runtime_error("bad event ordering");
   maxSupport=max(maxSupport,ll(groups.size()));peakAlive=max(peakAlive,activeMass);times++;i=j;
 }
 if(!groups.empty())throw runtime_error("sweep ended with active sources");
 for(int id=0;id<N;id++)if(location[id]!=-1)throw runtime_error("source did not expire");
 if(2*mergedQCredit!=joinedEnergy)throw runtime_error("FIRST-MERGER CREDIT FAILED TO RECONCILE J_JOIN-A");
 if(4*newPairs>totalGrowth)throw runtime_error("first-merge pair count exceeds total original growth / 4");
 ll knownHigh=0;
 switch(X){case 4096:knownHigh=7675;break;case 16384:knownHigh=45343;break;case 65536:knownHigh=224221;break;case 262144:knownHigh=1198498;break;case 1048576:knownHigh=5516751;break;default:break;}
 if(knownHigh&&totalHigh!=knownHigh)throw runtime_error("original high-event count regression");
 cout<<"GENEALOGY_PASS X="<<X<<" B="<<B<<" sources="<<N<<" events="<<events
     <<" highEvents="<<totalHigh<<" qHitFactors="<<totalHits
     <<" totalOriginalGrowth="<<totalGrowth<<" mergedPairsToGrowthBudget="<<double(4*newPairs)/totalGrowth<<" firstMergePairs="<<newPairs
     <<" birthPairs="<<born.newPairs<<" lowFoldPairs="<<low.newPairs<<" highFoldPairs="<<highMerge.newPairs<<" multiFoldPairs="<<multiMerge.newPairs
     <<" birthCredit="<<born.credit<<" lowFoldCredit="<<low.credit<<" highFoldCredit="<<highMerge.credit<<" multiFoldCredit="<<multiMerge.credit
     <<" futureWeightPairCredit="<<mergedQCredit<<" joinedOffDiag="<<joinedEnergy
     <<" firstFutureQCredit="<<(born.firstCredit+low.firstCredit+highMerge.firstCredit+multiMerge.firstCredit)
     <<" zeroFuturePairs="<<(born.zeroFuturePairs+low.zeroFuturePairs+highMerge.zeroFuturePairs+multiMerge.zeroFuturePairs)
     <<" exactlyOneFutureHighPairs="<<(born.oneFuturePair+low.oneFuturePair+highMerge.oneFuturePair+multiMerge.oneFuturePair)
     <<" sharedFutureHighEventCount="<<(born.futureHighCount+low.futureHighCount+highMerge.futureHighCount+multiMerge.futureHighCount)
     <<" avgFutureQperNewPair="<<double(mergedQCredit)/newPairs
     <<" birthMergeTimes="<<birthCollisions<<" foldMergeTimes="<<foldCollisions
     <<" uniqueHighNodes="<<uniqueHighNodes<<" uniqueQWeight="<<uniqueQWeight<<" weightedQoverUniqueQ="<<double(mergedQCredit*0+accumulate(totalQ.begin(),totalQ.end(),0LL))/uniqueQWeight<<" quotientArea="<<quotientArea<<" sourceArea="<<sourceArea<<" areaRatio="<<double(sourceArea)/quotientArea<<" maxSupport="<<maxSupport<<" peakAlive="<<peakAlive<<" maxCohort="<<maxCohort<<" maxMergedCohort="<<maxMergedCohort<<" sweptTimes="<<times<<" expirations="<<boundaryDeaths
     <<"\n";
}
int main(int argc,char**argv){if(argc<2)return 2;vector<int>xs;int maxX=0;for(int k=1;k<argc;k++){int x=atoi(argv[k]);if(x<128||x%4||x>1100000)return 2;xs.push_back(x);maxX=max(maxX,x);}sieve(8*maxX+1000);for(int M=7;M<=119;M+=2)if(literal(M,41)!=jump(M,41))throw runtime_error("original GCD literal mismatch");for(int X:xs)run(X);}
