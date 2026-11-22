// A166944 squarefree sqrt-wheel exact first-hit scan.
// Uses ONLY distinct primes <= floor(sqrt(2K(M)+1)); capped parity gcd.
// Build: g++ -std=c++17 -O3 research/squarefree_sqrt_wheel_scan.cpp -o sqrt_scan
// Run: ./sqrt_scan 10000000
// Finite tests, not a proof of the global twin-prime conjecture.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using i64 = long long;
vector<int> spf;

vector<int> prime_factors(int n) {
    vector<int> f;
    while (n>1) {
        int p=spf[n] ? spf[n] : n;
        f.push_back(p);
        do { n/=p; } while (n%p==0);
    }
    return f;
}
i64 next_residue(i64 pos, int p, i64 r) {
    i64 v=(r-pos)%(2LL*p);
    if(v<=0)v+=2LL*p;
    return pos+v;
}
int floor_isqrt(i64 n) {
    int r=int(sqrt(double(n)));
    while (1LL*(r+1)*(r+1)<=n)++r;
    while (1LL*r*r>n)--r;
    return r;
}
int main(int argc,char**argv) {
    int top=argc>1?atoi(argv[1]):1000000;
    if (top<7 || top>10000000) return 2;
    int bound=int((7LL*top+7)/2+5);
    spf.assign(bound+1,0);
    for(int p=2;1LL*p*p<=bound;p++)
        if(!spf[p])
            for(i64 k=1LL*p*p;k<=bound;k+=p)
                if(!spf[k])spf[k]=p;
    i64 starts=0,bad=0,late=0,lastLate=0,lastBad=0;
    i64 quarter=0,lastQuarter=0,maxG=0,maxGM=0;
    vector<int> badms;
    auto t0=chrono::steady_clock::now();
    for(int M=7;M<=top;M+=2) {
        ++starts;
        i64 s=M+2,K=(7LL*M-1)/4,pos=s,C=2LL*M-2,last=s;
        int B=floor_isqrt(2*K+1);
        while(pos<K) {
            i64 nx=K+1;
            for(int p:prime_factors(int(C-1)))
                if(p<=B)nx=min(nx,next_residue(pos,p,0));
            for(int p:prime_factors(int(C+1)))
                if(p<=B)nx=min(nx,next_residue(pos,p,p+2));
            if(nx>K)break;
            int g=int(gcd((nx&1)?nx-2:nx,(nx&1)?C+1:C-1));
            int e=1;
            for(int p:prime_factors(g))if(p<=B)e*=p;
            if(e<=1){cerr<<"first-hit factorization error at M="<<M<<"\n";return 3;}
            C+=e-1;last=pos=nx;
        }
        i64 G=C-(2LL*M-2);
        if(4*G>=M){++quarter;lastQuarter=M;}
        if(G>maxG){maxG=G;maxGM=M;}
        if(2*(last-s)>M){++late;lastLate=M;}
        bool good=(C-1>1&&!spf[C-1])&&(C+1>1&&!spf[C+1]);
        if(!good){++bad;lastBad=M;badms.push_back(M);}
    }
    cout<<"STARTS "<<starts<<" BAD "<<bad<<" LAST_BAD "<<lastBad
        <<" LATE "<<late<<" LAST_LATE "<<lastLate
        <<" QUARTER_VIOLATIONS "<<quarter<<" LAST_QUARTER "<<lastQuarter
        <<" MAX_G "<<maxG<<" AT "<<maxGM<<"\nBAD_MS";
    for(int m:badms)cout<<" "<<m;
    cout<<"\nTIME "<<chrono::duration<double>(
        chrono::steady_clock::now()-t0).count()<<"s\n";
    if(top==10000000) {
        if(starts!=4999997 || badms!=vector<int>{11,23,25,39,41,43,45}
            || late!=15 || lastLate!=171
            || quarter!=94 || lastQuarter!=1131
            || maxG!=52316 || maxGM!=8760663) {
            cerr<<"10M finite regression failed\n";return 4;
        }
        cout<<"PASS 10M squarefree sqrt-wheel finite regression\n";
    }
    cout<<"Global squarefree GOOD and twin-prime infinitude still OPEN\n";
}
