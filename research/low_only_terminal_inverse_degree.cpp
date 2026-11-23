// All 2310*1155 odd-low wheel start states: C->C_inf preimage degree at fixed t.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
static constexpr int L=2310,P=L/2;
int gap(int t,int q,int r){int a=(r-t)%(2*q);if(a<=0)a+=2*q;return a;}
int main(){
 int maxDegree=0,maxT=0,maxY=0,maxElapsed=0,maxEvents=0,maxGrowth=0;
 long long one=0,two=0,three=0,four=0,more=0,sumCollidingPairs=0;
 vector<int> hist(P);
 for(int t0=0;t0<L;++t0){
  fill(hist.begin(),hist.end(),0);
  for(int k=0;k<P;k++){
    int t=5*L+t0,C=2*k+10*L,C0=C,count=0;
    while(true){int best=INT32_MAX,d=1;
      for(int q:{3,5,7,11}){
        int r=-1;
        if((C-1)%q==0)r=0;
        else if((C+1)%q==0)r=q+2;
        if(r<0)continue;
        int delta=gap(t,q,r);
        if(delta<best){best=delta;d=q;}else if(delta==best)d*=q;
      }
      if(best==INT32_MAX)break;
      t+=best;C+=d-1;
      if(++count>22)throw runtime_error("too many low events");
    }
    int idx=(C%L)/2;hist[idx]++;
    maxElapsed=max(maxElapsed,t-(5*L+t0));maxEvents=max(maxEvents,count);maxGrowth=max(maxGrowth,C-C0);
  }
  for(int y=0;y<P;y++){
    int m=hist[y];if(m>maxDegree){maxDegree=m;maxT=t0;maxY=2*y;}
    if(m==1)one++;else if(m==2)two++;else if(m==3)three++;else if(m==4)four++;else if(m>4)more++;
    sumCollidingPairs+=1LL*m*(m-1)/2;
  }
 }
 cout<<"LOW_TERMINAL_INVERSE_PASS states="<<L*P<<" maxInverseDegree="<<maxDegree<<" atTimeResidue="<<maxT<<" targetResidue="<<maxY
     <<" maxElapsed="<<maxElapsed<<" maxEvents="<<maxEvents<<" maxGrowth="<<maxGrowth
     <<" one="<<one<<" two="<<two<<" three="<<three<<" four="<<four<<" more="<<more
     <<" collidingPrestatePairs="<<sumCollidingPairs<<"\n";
 if(maxElapsed!=133||maxEvents!=22||maxGrowth!=1156||maxDegree!=39)throw runtime_error("exhaustive low wheel inverse certificate mismatch");
}
