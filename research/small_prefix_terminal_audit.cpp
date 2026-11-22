// Finite-state terminal growth for clipped squarefree gcd, all canonical residues.
// C++17 -O3. No Lean verification; every tested canonical residue enumerated.
#include <bits/stdc++.h>
using namespace std;using ll=long long;
struct Info{int growth;int steps;};
Info terminal(int v,int L){int n=v+3,C=int((2LL*v-2)%L),g=0,s=0;while(gcd(L,C-1)>1||gcd(L,C+1)>1){int d=gcd(L,gcd((n&1)?n-2:n,(n&1)?C+1:C-1));C=(C+d-1)%L;g+=d-1;++n;++s;if(s>2000)throw runtime_error("not absorbed by cap");}return {g,s};}
int main(){int L=1,P=1;for(int q:{3,5,7,11,13,17}){L*=q;ll sumabs=0,sum=0,minus=0,zero=0,plus=0,maxsteps=0,maxgrowth=0,minDelta=0,maxDelta=0;int worstV=0;
for(int v=1;v<2*L;v+=2){auto a=terminal(v,L),b=terminal(v,P);int d=a.growth-b.growth;sum+=d;sumabs+=abs(d);maxsteps=max<ll>(maxsteps,a.steps);if(a.growth>maxgrowth){maxgrowth=a.growth;worstV=v;}minDelta=min<ll>(minDelta,d);maxDelta=max<ll>(maxDelta,d);if(d>0)plus++;else if(d<0)minus++;else zero++;}
cout<<"q="<<q<<" L="<<L<<" residues="<<L<<" T="<<maxsteps<<" Gmax="<<maxgrowth<<" worstV="<<worstV<<" A_q=sum|delta|="<<sumabs<<" signed_sum="<<sum<<" pos/zero/neg="<<plus<<"/"<<zero<<"/"<<minus<<" minmax_delta="<<minDelta<<"/"<<maxDelta<<"\n";const struct {int q,T,gmax;long long Aq,sumsigned;int neg;} expected[]={{3,5,4,6,6,0},{5,17,10,36,36,0},{7,48,28,360,360,0},{11,114,98,5820,5820,0},{13,157,148,81000,74196,145},{17,239,316,1548744,1463856,1283}};
for(auto e:expected)if(e.q==q && (maxsteps!=e.T || maxgrowth!=e.gmax ||sumabs!=e.Aq||sum!=e.sumsigned||minus!=e.neg))throw runtime_error("fixed-prefix regression mismatch");
P=L;}
}
