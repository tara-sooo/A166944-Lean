// A166944 cross-prime past-increment / future four-residue diagnostic.
// Exact arithmetic/GCD finite calculation, not Lean kernel validation.
// The three listed X scales are regression-checked; larger X can be probed.
// Hypothesis E=O(X*B^2/log B) is OPEN.
// g++ -std=c++17 -O3 -Wall -Wextra /mnt/data/cross_prime_increments_audit.cpp -o /mnt/data/cross_prime_increments_audit
// /mnt/data/cross_prime_increments_audit 4096
#include <bits/stdc++.h>
using namespace std;
using ll=long long;
vector<int> spf, primes;
vector<int> factors(int n){vector<int> f;while(n>1){int p=spf.at(n);f.push_back(p);do{n/=p;}while(n%p==0);}return f;}
ll next_hit(ll pos,int p,ll r){ll a=(r-pos)%(2*p);if(a<=0)a+=2*p;return pos+a;}
int growth_events(int m,int cap){ll pos=m+2,K=(7LL*m-1)/4,C=2LL*m-2;while(pos<K){ll t=K+1;for(int p:factors(int(C-1)))if(p<=cap)t=min(t,next_hit(pos,p,0));for(int p:factors(int(C+1)))if(p<=cap)t=min(t,next_hit(pos,p,p+2));if(t>K)break;int raw=int(gcd((t&1)?t-2:t,(t&1)?C+1:C-1)),d=1;for(int p:factors(raw))if(p<=cap)d*=p;if(d==1)throw runtime_error("bad clock");C+=d-1;pos=t;}return int(C-(2LL*m-2));}
int growth_steps(int m,int cap){ll C=2LL*m-2,K=(7LL*m-1)/4;for(int n=m+3;n<=K;n++){int raw=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1)),d=1;for(int p:factors(raw))if(p<=cap)d*=p;C+=d-1;}return int(C-(2LL*m-2));}
int main(int argc,char**argv){int X=argc>1?stoi(argv[1]):4096;if(X<256||X>262144||X%2)return 2;int B=int(ceil(sqrt(7.0*X)));int U=2*X+(3*B+7)/2+5;int Z=7*U+100;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;for(int p=3;p<=B;p+=2)if(spf[p]==p)primes.push_back(p);int J=primes.size();int vcount=(U-X)/2;int m11=find(primes.begin(),primes.end(),11)-primes.begin();
for(int m=7;m<=111;m+=2)for(int c:{1,3,5,7,11,13})if(growth_events(m,c)!=growth_steps(m,c))throw runtime_error("independent gcd mismatch");
vector<ll> dq(J), absdq(J), base(J), Wq(J), plusdq(J), minusdq(J), maxabs(J), H2q(J), A2q(J);ll direct=0, ref=0, signed_dq=0, abs_dq=0, totalvariation=0, positivevariation=0, negativevariation=0, lastgrowth=0, bad_w=0;
vector<ll> per_bin(6), per_bin_abs(6), per_bin_energy(6),per_bin_var(6);
for(int v=X+1;v<U;v+=2){vector<int> h(J);for(int i=0;i<J;i++)h[i]=growth_events(v,primes[i]);vector<int> selected(J,0), futureJ(J,0);vector<ll> futureW(J,0);ll W=0;int N=0;for(int i=J-1;i>=0;i--){futureW[i]=W;futureJ[i]=N;if(primes[i]>=11){int r=v%primes[i];if(r==0||r==1||r==3||r==5){selected[i]=1;W+=primes[i];}N++;}}
if(W>13LL*B)bad_w++;
ll directlocal=0,localref=0;for(int i=m11;i<J;i++){directlocal+=1LL*primes[i]*selected[i]*(i? h[i-1]:0);localref+=4LL*(i? h[i-1]:0);}
direct+=directlocal;ref+=localref;int prev=0;ll lhs=0,rhs=0;for(int i=0;i<J;i++){int delta=h[i]-prev;prev=h[i];int q=primes[i];ll discrepancy=futureW[i]-4LL*futureJ[i];ll term=delta*discrepancy;H2q[i]+=1LL*delta*delta;A2q[i]+=discrepancy*discrepancy;ll b=4LL*futureJ[i]*delta;dq[i]+=term;absdq[i]+=llabs(term);base[i]+=b;Wq[i]+=futureW[i];if(delta>0){plusdq[i]+=delta;positivevariation+=delta;}else{minusdq[i]-=delta;negativevariation-=delta;}maxabs[i]=max(maxabs[i],llabs(term));signed_dq+=term;totalvariation+=abs(delta);lhs+=term;rhs+=b;
int bin= q<11?0: q<=B/8?1:q<=B/4?2:q<=B/2?3:q<=3*B/4?4:5;per_bin[bin]+=term;per_bin_abs[bin]+=llabs(term);per_bin_energy[bin]+=b;per_bin_var[bin]+=abs(delta);
}if(lhs+rhs!=directlocal || directlocal==LLONG_MIN)throw runtime_error("identity mismatch");lastgrowth+=h.back();}
for(ll x:dq)abs_dq+=llabs(x);
ll frombase=accumulate(base.begin(),base.end(),0LL);if(frombase+signed_dq!=direct||ref!=frombase)throw runtime_error("global mismatch");
if(growth_events(619,11)!=24 || growth_events(619,13)!=12)throw runtime_error("negative-stage witness changed");
struct Case {int x;ll E, baseline, D, absD, H2, A2;};
const Case cases[]={{4096,36344568LL,37822496LL,-1477928LL,3834200LL,128169316LL,546493909LL},{16384,485635362LL,481859104LL,3776258LL,49171738LL,3330039128LL,13668623643LL},{65536,5672417264LL,5769264200LL,-96846936LL,486681372LL,25725426668LL,374377649407LL}};
ll checkH2=accumulate(H2q.begin(),H2q.end(),0LL),checkA2=accumulate(A2q.begin(),A2q.end(),0LL);
for(const auto &c: cases)if(X==c.x && (direct!=c.E || frombase!=c.baseline || signed_dq!=c.D || abs_dq!=c.absD || checkH2!=c.H2 || checkA2!=c.A2))throw runtime_error("regression mismatch");
cout<<setprecision(10)<<"PASS X="<<X<<" B="<<B<<" U="<<U<<" #p="<<J<<" v="<<vcount<<"\n";
cout<<"E="<<direct<<" baseline="<<frombase<<" D_total="<<signed_dq<<" sum_abs_Dq="<<abs_dq<<" total_var_Dq_contributions="<<accumulate(absdq.begin(),absdq.end(),0LL)<<"\n";
cout<<"D_over_E="<<double(signed_dq)/direct<<" sum_absDq_over_E="<<double(abs_dq)/direct<<" max_weight_violations="<<bad_w<<"\n";
ll H2=accumulate(H2q.begin(),H2q.end(),0LL),A2=accumulate(A2q.begin(),A2q.end(),0LL);long double bystage=0;for(int i=0;i<J;i++)bystage+=sqrt((long double)H2q[i]*(long double)A2q[i]);cout<<"L2_energy_delta="<<H2<<" L2_weight_center="<<A2<<" direct_global_Cauchy="<<double(sqrt((long double)H2*A2))<<" stagewise_Cauchy="<<double(bystage)<<" stagewise_Cauchy_over_absD="<<double(bystage/llabs(signed_dq))<<"\n";
cout<<"total_prefix_variation="<<totalvariation<<" plus="<<positivevariation<<" minus="<<negativevariation<<" terminal_growth_V="<<lastgrowth<<" tv_to_terminal="<<double(totalvariation)/lastgrowth<<"\n";
cout<<"sum_per_q:\n";for(int i=0;i<J;i++)if(llabs(dq[i])*20>abs_dq||i<4||i>J-3)cout<<"q="<<primes[i]<<" Dq="<<dq[i]<<" baseline_q="<<base[i]<<" plus="<<plusdq[i]<<" minus="<<minusdq[i]<<"\n";
cout<<"bins 0:(3,5,7); 1:(11,B/8];2:(B/8,B/4];3:(B/4,B/2];4:(B/2,3B/4];5:(3B/4,B]\n";
for(int k=0;k<6;k++)cout<<k<<" Dsum="<<per_bin[k]<<" absTerms="<<per_bin_abs[k]<<" base="<<per_bin_energy[k]<<" variation="<<per_bin_var[k]<<"\n";
}
