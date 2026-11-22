// Original parity-GCD, exact squarefree capped trajectory; event-jump and independent step checks.
#include <bits/stdc++.h>
using namespace std; using ll=long long;
vector<int> spf, primes;
vector<int> fac(int n){vector<int> ans;while(n>1){int p=spf.at(n);ans.push_back(p);while(n%p==0)n/=p;}return ans;}
ll next_hit(ll pos,int p,ll r){ll d=(r-pos)%(2LL*p);if(d<=0)d+=2LL*p;return pos+d;}
vector<pair<int,int>> ev(int m,int P){ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;vector<pair<int,int>> e;while(pos<K){ll n=K+1;for(int p:fac(int(C-1)))if(p<=P)n=min(n,next_hit(pos,p,0));for(int p:fac(int(C+1)))if(p<=P)n=min(n,next_hit(pos,p,p+2));if(n>K)break;int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;for(int p:fac(raw))if(p<=P)d*=p;if(d<=1)throw runtime_error("bad event clock");e.push_back({int(n-(m+2)),d-1});C+=d-1;pos=n;}return e;}
int main(int argc,char**argv){int X=argc>1?atoi(argv[1]):1024;int requested=argc>2?atoi(argv[2]):31;int B=int(ceil(sqrt(7.0*X)));int U=2*X+(3*B+7)/2+5;int Z=7*U+100;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);auto it=find(primes.begin(),primes.end(),requested);if(it==primes.end())return 2;int q=requested,prev=(it==primes.begin()?1:*(it-1));int maxT=int((7LL*(U-1)-1)/4)-(U+1);vector<ll> tsigned(maxT+1),tmass(maxT+1),tcount(maxT+1);ll totalSigned=0,totalAbsFinal=0,totalMassTime=0,globalD=0,firstActive=LLONG_MAX,lastActive=0,oddEarly=0,countV=0,totalOld=0,totalNew=0;ll npos=0,nneg=0,growthEnergy=0,truncCorr=0;vector<ll> fFinal,fTrunc;const int truncT=2*q;ll S_q=0;for(int p:primes)if(p>q&&p>=11)S_q+=p;
for(int v=X+1;v<U;v+=2){auto a=ev(v,q),b=ev(v,prev);ll W=0;int J=0;for(auto p:primes)if(p>q&&p>=11){J++;int r=v%p;if(r==0||r==1||r==3||r==5)W+=p;}ll A=W-4LL*J;if(llabs(A)>13LL*B)throw runtime_error("incidence bound mismatch");int ia=0,ib=0;ll delta=0,absTime=0,earlyH=0;while(ia<(int)a.size()||ib<(int)b.size()){int t=min(ia<(int)a.size()?a[ia].first:INT_MAX,ib<(int)b.size()?b[ib].first:INT_MAX);ll da=(ia<(int)a.size()&&a[ia].first==t)?a[ia++].second:0;ll db=(ib<(int)b.size()&&b[ib].first==t)?b[ib++].second:0;ll diff=da-db;if(!diff)continue;if(t< (q-7+1)/2)oddEarly++;firstActive=min(firstActive,ll(t));lastActive=max(lastActive,ll(t));totalMassTime+=llabs(diff);absTime+=llabs(diff);delta+=diff;if(t<=truncT)earlyH+=diff;tsigned[t]+=diff*A;tmass[t]+=llabs(diff);tcount[t]++;if(diff>0){npos+=diff;}else nneg-=diff;}fFinal.push_back(delta);fTrunc.push_back(earlyH);truncCorr+=earlyH*A;totalSigned+=delta;totalAbsFinal+=llabs(delta);globalD+=delta*A;ll gOld=accumulate(b.begin(),b.end(),0LL,[](ll s, auto z){return s+z.second;});ll gNew=accumulate(a.begin(),a.end(),0LL,[](ll s, auto z){return s+z.second;});totalOld+=gOld;totalNew+=gNew;growthEnergy+=gOld*gOld+gNew*gNew;countV++;
}
ll absCorrSlice=0,maxslice=0,atmax=0,times=0;array<ll,6> csum{}, cmass{},cnum{};for(int t=1;t<=maxT;t++)if(tcount[t]){times++;absCorrSlice+=llabs(tsigned[t]);if(llabs(tsigned[t])>maxslice){maxslice=llabs(tsigned[t]);atmax=t;}int k=t<q/2?0:t<q?1:t<2*q?2:t<4*q?3:t<8*q?4:5;csum[k]+=tsigned[t];cmass[k]+=tmass[t];cnum[k]+=tcount[t];}
if(accumulate(tsigned.begin(),tsigned.end(),0LL)!=globalD)throw runtime_error("time stage D mismatch");
if(oddEarly)throw runtime_error("q causal lightcone fail");
if(npos-nneg!=totalNew-totalOld)throw runtime_error("mass mismatch");
ll finalBV=llabs(fFinal.back()),truncBV=llabs(fTrunc.back());for(size_t i=1;i<fFinal.size();i++){finalBV+=llabs(fFinal[i]-fFinal[i-1]);truncBV+=llabs(fTrunc[i]-fTrunc[i-1]);}
if(X==1024 && q==59 && (globalD!=0 || totalMassTime!=264 || totalAbsFinal!=0 || firstActive!=30 || lastActive!=139)) throw runtime_error("q59 regression changed");
if(X==4096 && q==149 && (globalD!=-1920 || totalMassTime!=1056 || totalAbsFinal!=120 || firstActive!=71 || lastActive!=281 || finalBV!=120)) throw runtime_error("q149 regression changed");
if(X==4096 && q==97 && (globalD!=-150630 || totalMassTime!=16148 || totalAbsFinal!=12108 || finalBV!=5364)) throw runtime_error("q97 regression changed");
if(llabs(globalD)>4*S_q*finalBV || llabs(truncCorr)>4*S_q*truncBV)throw runtime_error("short-interval Abel bound mismatch");
for(int T:{1, max(1,q/2),q,2*q,4*q,8*q})if(T<=maxT){ll tail=accumulate(tmass.begin()+T,tmass.end(),0LL);if(tail*T>3*growthEnergy)throw runtime_error("time tail energy bound mismatch");}
cout<<"PASS X="<<X<<" q="<<q<<" prev="<<prev<<" B="<<B<<" V="<<countV<<" firstActiveT="<<firstActive<<" last="<<lastActive<<" activeTimes="<<times<<"\n";
cout<<"D="<<globalD<<" sum_t_abs_D_t="<<absCorrSlice<<" L1time="<<totalMassTime<<" L1final="<<totalAbsFinal<<" time_to_final_L1="<<(double)totalMassTime/max(1LL,totalAbsFinal)<<"\n";
cout<<"M2="<<growthEnergy<<" earlyCorr_at_2q="<<truncCorr<<" BVbound_final="<<4*S_q*finalBV<<" BVbound_at_2q="<<4*S_q*truncBV<<"\n";
cout<<"BV_final="<<finalBV<<" BV_trunc_at_2q="<<truncBV<<" truncated_H_L1="<<accumulate(fTrunc.begin(),fTrunc.end(),0LL,[](ll a,ll b){return a+llabs(b);})<<"\n";
cout<<"newGrowth="<<totalNew<<" oldGrowth="<<totalOld<<" timeL1_vs_newplusold="<<(double)totalMassTime/max(1LL,totalNew+totalOld)<<" maxAbsD_t="<<maxslice<<" at_t="<<atmax<<"\n";
for(int i=0;i<6;i++)cout<<"band="<<i<<" corrSigned="<<csum[i]<<" timeMass="<<cmass[i]<<" activeOccurrences="<<cnum[i]<<"\n";
}
