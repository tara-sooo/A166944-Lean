// Exact parity-specific squarefree clipped GCD: second-order effect of swapping two prime insertions.
// g++ -std=c++17 -O3 -Wall -Wextra -Werror band_swap_curvature_audit.cpp -o /tmp/band_swap_curvature_audit
// /tmp/band_swap_curvature_audit 4096 32 [half=0|1]
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
using ll=long long;
static vector<int> spf;
struct Ev { int n,e; };
vector<int> factor(int a){vector<int> f;while(a>1){int p=spf.at(a);f.push_back(p);do{a/=p;}while(a%p==0);}return f;}
ll next_hit(ll pos,ll p,ll residue){ll d=(residue-pos)%(2*p);if(d<=0)d+=2*p;return pos+d;}
int run(int M,const vector<unsigned char>& mask,vector<Ev>* events=nullptr){ll pos=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
  while(pos<K){ll n=K+1;for(int p:factor(int(C-1)))if(p<(int)mask.size()&&mask[p])n=min(n,next_hit(pos,p,0));for(int p:factor(int(C+1)))if(p<(int)mask.size()&&mask[p])n=min(n,next_hit(pos,p,p+2));if(n>K)break;ll g=gcd((n&1)?n-2:n,(n&1)?C+1:C-1);int d=1;for(int p:factor(int(g)))if(p<(int)mask.size()&&mask[p])d*=p;if(d<=1)throw runtime_error("event clock inconsistency");if(events)events->push_back({int(n),d});C+=d-1;pos=n;}
  return int(C-(2LL*M-2));}
int literal(int M,const vector<unsigned char>& mask){ll C=2LL*M-2,K=(7LL*M-1)/4;for(ll n=M+3;n<=K;n++){ll g=gcd((n&1)?n-2:n,(n&1)?C+1:C-1);int d=1;for(int p:factor(int(g)))if(p<(int)mask.size()&&mask[p])d*=p;C+=d-1;}return int(C-(2LL*M-2));}
ll oldKick(int M,int p,const vector<Ev>& events){ll pos=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
 auto clock=[&](){ll n=K+1;if((C-1)%p==0)n=min(n,next_hit(pos,p,0));if((C+1)%p==0)n=min(n,next_hit(pos,p,p+2));return n;};
 for(auto e:events){if(clock()<=e.n)return (p-1LL)*((clock()==e.n)?e.e:1);pos=e.n;C+=e.e-1;}
 return clock()<=K?(p-1LL):0LL;
}
int main(int argc,char**argv){int X=argc>1?atoi(argv[1]):4096;int lo=argc>2?atoi(argv[2]):32;int half=argc>3?atoi(argv[3]):0;
 if(X<256||X>65536||X%2||lo<2|| (lo&(lo-1)))return 2;
 int B=int(ceil(sqrt(7.*X))),Z=8*X+10000;spf.resize(Z);iota(spf.begin(),spf.end(),0);for(int p=2;1LL*p*p<Z;p++)if(spf[p]==p)for(int j=p*p;j<Z;j+=p)if(spf[j]==j)spf[j]=p;
 vector<int> band;vector<unsigned char>mask(B+1,0);for(int p=3;p<=B;p+=2)if(spf[p]==p){if(p<lo)mask[p]=1;else if(p<2*lo)band.push_back(p);}
 if(half){vector<int>remaining;for(size_t k=0;k<band.size();k++){if(k%2==0)mask[band[k]]=1;else remaining.push_back(band[k]);}band.swap(remaining);}
 if(band.size()<2)throw runtime_error("band has too few primes");
 if(X>=4096){vector<unsigned char> w(B+1);for(int p=3;p<32;p+=2)if(spf[p]==p)w[p]=1;int gs=literal(4727,w);w[37]=1;int gp_=literal(4727,w);w[37]=0;w[41]=1;int gq_=literal(4727,w);w[37]=1;int gpq_=literal(4727,w);if(gs!=58||gp_!=100||gq_!=58||gpq_!=166)throw runtime_error("literal M4727 cascade witness changed");}
 if(X>=16384){vector<unsigned char> w(B+1);for(int p=3;p<128;p+=2)if(spf[p]==p)w[p]=1;int gs=literal(19583,w);w[157]=1;int gp_=literal(19583,w);w[157]=0;w[173]=1;int gq_=literal(19583,w);w[157]=1;int gpq_=literal(19583,w);if(gs!=244||gp_!=454||gq_!=244||gpq_!=2446)throw runtime_error("literal M19583 cascade witness changed");}
 for(int M=7;M<=119;M+=2)if(run(M,mask)!=literal(M,mask))throw runtime_error("literal base comparison failed");
 ll swapMinBound=0,swapExactBound=0;
 ll failFirstKick=0,maxKickRatioNum=0,maxKickRatioDen=1;int failM=0,failP=0,failQ=0;ll failCurv=0,failKick=0;
 ll nPairs=0,nonnull=0,orderSensitive=0,negativeSensitive=0,curvL1=0,swapL1=0,curvL2=0,negativeMarginalSamples=0,totalSourcePairs=0,curvBaseNone=0,curvBaseOne=0,curvBaseBoth=0,oneActiveTotal=0;
 int witnessOneM=0,witnessOneP=0,witnessOneQ=0;
 ll oneL1=0,bothL1=0,oneL2=0,bothL2=0,oneSwapL1=0,bothSwapL1=0;ll maxCurv=0,maxSwap=0;int maxCurvM=0,maxCurvP=0,maxCurvQ=0;
 vector<int> g0(X/2),gp(X/2),gq(X/2);vector<vector<Ev>> baseEv(X/2);
 for(int j=0;j<X/2;j++)g0[j]=run(X+1+2*j,mask,&baseEv[j]);
 vector<vector<ll>> kicks(band.size(),vector<ll>(X/2));
 vector<vector<unsigned char>> activeInBase(band.size(),vector<unsigned char>(X/2));
 for(size_t k=0;k<band.size();k++)for(int j=0;j<X/2;j++){kicks[k][j]=oldKick(X+1+2*j,band[k],baseEv[j]);activeInBase[k][j]=(kicks[k][j]!=0);}
 for(size_t ii=0;ii<band.size();ii++){int p=band[ii];mask[p]=1;for(int j=0;j<X/2;j++){vector<Ev> ev;gp[j]=run(X+1+2*j,mask,&ev);ll actual=0;for(auto e:ev)if(e.e%p==0){actual=(p-1LL)*(e.e/p);break;}if(actual!=kicks[ii][j])throw runtime_error("first-p kick disagrees with full enlarged path");}mask[p]=0;
   for(size_t jj=ii+1;jj<band.size();jj++){int q=band[jj];mask[q]=1;for(int j=0;j<X/2;j++)gq[j]=run(X+1+2*j,mask);mask[q]=0;
     mask[p]=mask[q]=1;
     ll pcurv=0,pswap=0,nonzero=0,nsens=0;
     for(int j=0;j<X/2;j++){int M=X+1+2*j;ll a=gp[j]-g0[j],c=gq[j]-g0[j],h=run(M,mask)-gp[j]-gq[j]+g0[j];
       ll d1=max(0LL,a)+max(0LL,c+h),d2=max(0LL,c)+max(0LL,a+h),dif=d1-d2;
       if(llabs(dif)>llabs(h)||llabs(dif)>llabs(a-c))throw runtime_error("sharp 2nd difference swap lemma contradicted");
       swapMinBound+=min(llabs(h),llabs(a-c));swapExactBound+=llabs(h);
       if(!activeInBase[ii][j]&&!activeInBase[jj][j]&&h)throw runtime_error("nonzero curvature with no old prime opportunity");
       pcurv+=llabs(h);pswap+=llabs(dif);curvL1+=llabs(h);swapL1+=llabs(dif);curvL2+=h*h;
       ll fk=kicks[ii][j]+kicks[jj][j];if(llabs(h)>fk){failFirstKick++;if(!failM){failM=M;failP=p;failQ=q;failCurv=h;failKick=fk;}}
       if(fk && llabs(h)*maxKickRatioDen>maxKickRatioNum*fk){maxKickRatioNum=llabs(h);maxKickRatioDen=fk;}
       if(h) {nonzero++;nonnull++;int ac=int(activeInBase[ii][j])+int(activeInBase[jj][j]);if(ac==0)curvBaseNone++;else if(ac==1){curvBaseOne++;oneL1+=llabs(h);oneL2+=h*h;oneSwapL1+=llabs(dif);if(!witnessOneM){witnessOneM=M;witnessOneP=p;witnessOneQ=q;}}else {curvBaseBoth++;bothL1+=llabs(h);bothL2+=h*h;bothSwapL1+=llabs(dif);}}
       if(int(activeInBase[ii][j])+int(activeInBase[jj][j])==1)oneActiveTotal++;
       if(dif){nsens++;orderSensitive++;}
       if((a<0||c<0||a+h<0||c+h<0))negativeMarginalSamples++;
       if(dif && a>=0&&c>=0&&a+h>=0&&c+h>=0)throw runtime_error("order effect without signed stage");
       if(dif && (a<0||c<0||a+h<0||c+h<0))negativeSensitive++;
       if(llabs(h)>maxCurv){maxCurv=llabs(h);maxCurvM=M;maxCurvP=p;maxCurvQ=q;}
       maxSwap=max(maxSwap,llabs(dif));
       totalSourcePairs++;
     }
     mask[p]=mask[q]=0;
     cout<<"PAIR p="<<p<<" q="<<q<<" curvature_l1="<<pcurv<<" swap_l1="<<pswap<<" nonzeroCurv="<<nonzero<<" sensitive="<<nsens<<"\n";
     nPairs++;
   }
 }
 if(X==4096&&lo==32&&half==0&&(nPairs!=21||curvL1!=40506||swapL1!=2574||nonnull!=459||orderSensitive!=64||curvBaseOne!=346||curvBaseBoth!=113||failFirstKick!=297))throw runtime_error("4096 band curvature regression failed");
 if(X==8192&&lo==64&&half==0&&(nPairs!=78||curvL1!=189150||swapL1!=35148||nonnull!=864||orderSensitive!=130||curvBaseOne!=699))throw runtime_error("8192 band curvature regression failed");
 if(X==16384&&lo==128&&half==0&&(nPairs!=253||curvL1!=1310442||swapL1!=203982||nonnull!=3073||orderSensitive!=908||curvBaseOne!=1542||curvBaseBoth!=1531||failFirstKick!=1743))throw runtime_error("16384 band curvature regression failed");
 if(X==16384&&lo==128&&half==1&&(nPairs!=55||curvL1!=676722||swapL1!=251238||nonnull!=774||orderSensitive!=368||failFirstKick!=491))throw runtime_error("halfband curvature regression failed");
 cout<<setprecision(12)<<"PASS X="<<X<<" B="<<B<<" band=["<<lo<<","<<2*lo<<") primeCount="<<band.size()<<" pairs="<<nPairs<<" sourcePairs="<<totalSourcePairs<<" curvature_l1="<<curvL1<<" swap_l1="<<swapL1<<" swap_min_bound="<<swapMinBound<<" swap_over_min_bound="<<double(swapL1)/swapMinBound<<" swap_over_curvature="<<double(swapL1)/curvL1<<" nonzeroCurv="<<nonnull<<" orderSensitive="<<orderSensitive<<" sensitive_given_curvature="<<double(orderSensitive)/nonnull<<" negativeMarginal="<<negativeMarginalSamples<<" maxCurv="<<maxCurv<<" witness="<<maxCurvM<<","<<maxCurvP<<","<<maxCurvQ<<" maxSwap="<<maxSwap<<" curvature_l2="<<curvL2<<" base_none="<<curvBaseNone<<" base_one="<<curvBaseOne<<" base_both="<<curvBaseBoth<<" one_L1="<<oneL1<<" both_L1="<<bothL1<<" one_L2="<<oneL2<<" both_L2="<<bothL2<<" one_swap_L1="<<oneSwapL1<<" both_swap_L1="<<bothSwapL1<<" one_active_total="<<oneActiveTotal<<" triggered_witness="<<witnessOneM<<","<<witnessOneP<<","<<witnessOneQ<<" half="<<half<<" fail_Kick_Dominance="<<failFirstKick<<" firstFail="<<failM<<","<<failP<<","<<failQ<<","<<failCurv<<","<<failKick<<" maxCurvPerKick="<<double(maxKickRatioNum)/maxKickRatioDen<<"\n";
}
