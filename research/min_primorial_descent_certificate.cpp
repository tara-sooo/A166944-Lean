// Independent rolling-row integer certificate for the offset MIN.
// Build: g++ -O3 -std=c++17 min_primorial_descent_certificate.cpp -o descent_certificate
// Run: ./descent_certificate
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
struct Certificate { int B, I; vector<int> rowmax; };
Certificate compute(const vector<int>& ps, int a, int b) {
    int Q=2; for(int p:ps) Q*=p;
    int width=(ps.back()-1)/2+1, rows=Q/2+1;
    vector<vector<int>> F(width,vector<int>(Q,0));
    vector<vector<int>> waits(2*ps.size(),vector<int>(Q));
    for(size_t j=0;j<ps.size();++j)for(int side=0;side<2;++side){
        int p=ps[j],s=side?p+2:0;
        for(int v=0;v<Q;++v){int w=(s-v)%(2*p); if(w<=0)w+=2*p;waits[2*j+side][v]=w;}
    }
    vector<int> rowmax(rows,0);int B=0,I=0;
    for(int i=rows-2;i>=0;--i){
        int u=2*i; auto& out=F[i%width];fill(out.begin(),out.end(),0);
        vector<int> eligible;
        for(size_t j=0;j<ps.size();++j){
            int p=ps[j];if((u+p-1)%p==0)eligible.push_back(2*j);
            if((u+1)%p==0)eligible.push_back(2*j+1);
        }
        if(!eligible.empty())for(int v=0;v<Q;++v){
            int w=100000, p=0;
            for(int c:eligible)if(waits[c][v]<w){w=waits[c][v];p=ps[c/2];}
            assert(u+p-1<=Q);
            int j=i+(p-1)/2;
            assert(j%width!=i%width);
            out[v]=max(0,2*b*w-(a+b)*(p-1)+F[j%width][(v+w)%Q]);
        }
        rowmax[i]=*max_element(out.begin(),out.end());B=max(B,rowmax[i]);
        // For u=12k mod Q, k mod Q/6 is unique, as Q/6 is odd.
        if(u%6==0){int m=Q/6,k=((u/6)*int64_t((m+1)/2))%m;assert(12*k%Q==u);I=max(I,out[(6*k+3)%Q]);}
    }
    cout<<"a="<<a<<" b="<<b<<" Q="<<Q<<" states="<<int64_t(rows)*Q<<" B="<<B<<" I="<<I<<'\n';
    return {B,I,move(rowmax)};
}
int main(){
    const vector<int> small={3,5,7,11};
    auto c=compute(small,11,3);assert(c.B==14&&c.I==6);
    // For p=13,w<=25 the reward is <=-18, so B=14 suffices.
    // At w=26 the source has no eligible small prime. Check the maximum
    // restricted-prefix reward at the resulting offset u+12 (all times).
    int M=0;const int Q=2310;
    for(int u=0;u<Q;u+=2){bool rough=true;for(int p:small)if((u+p-1)%p==0||(u+1)%p==0)rough=false;
        if(rough)M=max(M,c.rowmax[((u+12)%Q)/2]);}
    cout<<"p=13,w=26 rough-source successor bound "<<M<<'\n';
    assert(M==12);assert(6*26-14*12+M<=0);assert(14-2*17+c.B<=0);
    // Main certificate: all larger labels (>=17) have reward <= -28.
    auto d=compute({3,5,7,11,13},18,5);assert(d.B==28&&d.I==12);assert(23-3*17+d.B==0);
    cout<<"all certificate checks passed\n";
}
