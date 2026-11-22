// Signed prime insertion costs for the squarefree sqrt-wheel.
// Build: g++ -std=c++17 -O3 research/squarefree_prime_stage_audit.cpp -o stage_scan
// Run: ./stage_scan 1024     # or 4096, 16384
// The strong per-prime mean upper bound is NOT proved by these finite scans.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using i64=long long;
vector<int> spf;
vector<int> factors(int n) {
    vector<int> v;
    while(n>1) {
        int p=spf[n]?spf[n]:n;
        v.push_back(p);
        do {n/=p;} while(n%p==0);
    }
    return v;
}
i64 nxt(i64 pos,int p,i64 residue) {
    i64 d=(residue-pos)%(2LL*p);
    if(d<=0)d+=2LL*p;
    return pos+d;
}
int grow(int M,int P) {
    i64 pos=M+2,K=(7LL*M-1)/4,C=2LL*M-2;
    while(pos<K) {
        i64 n=K+1;
        for(int p:factors(int(C-1)))if(p<=P)n=min(n,nxt(pos,p,0));
        for(int p:factors(int(C+1)))if(p<=P)n=min(n,nxt(pos,p,p+2));
        if(n>K)break;
        int g=int(gcd((n&1)?n-2:n,(n&1)?C+1:C-1));
        int e=1;
        for(int p:factors(g))if(p<=P)e*=p;
        if(e<=1){cerr<<"wrong first hit\n";exit(2);}
        C+=e-1;pos=n;
    }
    return int(C-(2LL*M-2));
}
int main(int argc,char**argv) {
    int X=argc>1?atoi(argv[1]):1024;
    if(X<256||X>16384||X%2)return 2;
    int B=int(ceil(sqrt(7.0*X)));
    int limit=7*X+100;
    spf.assign(limit,0);
    for(int p=2;1LL*p*p<limit;p++)
        if(!spf[p])
            for(int x=p*p;x<limit;x+=p)
                if(!spf[x])spf[x]=p;
    vector<int> primes;
    for(int p=3;p<=B;p+=2)if(!spf[p])primes.push_back(p);
    vector<int> old(X/2,0);
    i64 total=0;
    double maxSigned=-1e100,maxPositive=-1e100;
    double maxSignedRatio=-1e100,maxPositiveRatio=-1e100;
    int pSigned=0,pPositive=0,pSR=0,pPR=0;
    for(int p:primes) {
        i64 signedTotal=0,positiveTotal=0;
        for(int i=0;i<X/2;i++) {
            int M=X+1+2*i;
            int newh=grow(M,p);
            int diff=newh-old[i];
            old[i]=newh;
            signedTotal+=diff;
            positiveTotal+=max(diff,0);
        }
        double signedMean=double(signedTotal)/(X/2);
        double positiveMean=double(positiveTotal)/(X/2);
        if(signedMean>maxSigned){maxSigned=signedMean;pSigned=p;}
        if(positiveMean>maxPositive){maxPositive=positiveMean;pPositive=p;}
        if(signedMean/p>maxSignedRatio){maxSignedRatio=signedMean/p;pSR=p;}
        if(positiveMean/p>maxPositiveRatio){
            maxPositiveRatio=positiveMean/p;pPR=p;
        }
        total+=signedTotal;
    }
    if(total!=accumulate(old.begin(),old.end(),0LL))
        return 3;
    if(X==1024 && (B!=85||primes.size()!=22||total!=39940))return 4;
    if(X==4096 && (B!=170||primes.size()!=38||total!=399142))return 4;
    if(X==16384 && (B!=339||primes.size()!=67||total!=2915326))return 4;
    cout<<setprecision(9)<<"X="<<X<<" B="<<B
        <<" primes="<<primes.size()
        <<" total_growth="<<total
        <<" mean_growth="<<double(total)/(X/2)
        <<" max_signed_mean="<<maxSigned<<" at_p="<<pSigned
        <<" max_positive_mean="<<maxPositive<<" at_p="<<pPositive
        <<" max_signed_mean_over_p="<<maxSignedRatio<<" at_p="<<pSR
        <<" max_positive_mean_over_p="<<maxPositiveRatio<<" at_p="<<pPR
        <<"\nPASS finite squarefree prime-stage comparison\n"
        <<"Unbounded-X per-prime mean upper bound OPEN\n";
}
