// A166944 Cap B: full-period 30-wheel / four exceptional prime audit.
// C++17, self-contained. NOT an unconditional proof of Cap B.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr int MOD=30;
constexpr array<int,3> SUP={3,5,15};
constexpr array<int,4> EXC={61,67,71,73};
constexpr int PERIOD=30*61*67*71*73;
struct Edge {int j=-1, gap=0, e=0;};
int key(int s,int c){return (c/2)*30+s;}
int full_gcd(int r,int c){return gcd(r%2==0?r:r-2,r%2==0?c-1:c+1);}
struct Audit {
 array<Edge,450> edges{};
 array<int,450> color{},cnt{},travel{},growth{},potential{};
 int edge_count=0, max_count=0,max_travel=0,max_growth=0,max_potential=0;
 void visit(int i){
  if(color[i]==2)return;
  if(color[i]==1)throw runtime_error("cycle in forced mod-30 first-hit graph");
  color[i]=1;
  Edge a=edges[i];
  if(a.j>=0){
   visit(a.j);
   cnt[i]=1+cnt[a.j];
   travel[i]=a.gap+travel[a.j];
   growth[i]=a.e-1+growth[a.j];
   potential[i]=max(0,a.gap-2*(a.e-1)+potential[a.j]);
  }
  max_count=max(max_count,cnt[i]);max_travel=max(max_travel,travel[i]);
  max_growth=max(max_growth,growth[i]);max_potential=max(max_potential,potential[i]);
  color[i]=2;
 }
 Audit(){
  for(int c=0;c<30;c+=2)for(int s=0;s<30;s++){
   int i=key(s,c);
   for(int g=1;g<=10;g++){
    int r=s+g,e=gcd(full_gcd(r,c),30);
    if(e>1){
     if(find(SUP.begin(),SUP.end(),e)==SUP.end()) throw runtime_error("invalid clipped gcd");
     edges[i]={key(r%30,(c+e-1)%30),g,e};
     ++edge_count;break;
    }
   }
  }
  for(int i=0;i<450;i++)visit(i);
  int canonical_max=0;
  for(int m=1;m<30;m+=6) canonical_max=max(canonical_max,potential[key((m+2)%30,(2*m-2)%30)]);
  if(edge_count!=360 || max_count!=5 || max_travel!=19 || max_growth!=16 || max_potential!=4 || canonical_max!=3)
    throw runtime_error("unexpected mod-30 certificate statistics");
  for(int i=0;i<450;i++)if(edges[i].j>=0){
   auto a=edges[i];
   if(a.gap+potential[a.j]>2*(a.e-1)+potential[i])throw runtime_error("potential inequality failed");
  }
  cout<<"PASS: 450 states, 360 first-clipped-hit edges, max supported steps "<<max_count
      <<", travel "<<max_travel<<", growth "<<max_growth
      <<", coefficient-two potential max "<<max_potential<<", canonical start max "<<canonical_max<<"\n";
 }
};
// Because every allowed increment e is odd and divides the even PERIOD,
// the even horizon C mod PERIOD cannot wrap under C -> C+(e-1):
// if e | C-1 or C+1, the distance to the next multiple is >=e-1.
// So one full period gives a bound for arbitrary starting horizons.
int wheel_four(){
 constexpr int N=PERIOD/2+1;
 vector<uint8_t> dp(N,0);
 int max_exc=0,first_at=-1;
 for(int u=0;u<N;u++){
  int C=2*u,score=dp[u];
  if(score>max_exc){max_exc=score;first_at=C;}
  auto attempt=[&](int e,int add){
   if((C-1)%e!=0 && (C+1)%e!=0)return;
   int j=u+(e-1)/2;
   if(j>=N)return;
   if(score+add>=250)throw runtime_error("uint8 overflow");
   dp[j]=max(dp[j],static_cast<uint8_t>(score+add));
  };
  for(int e:SUP)attempt(e,0);
  for(int e:EXC)attempt(e,1);
 }
 if(max_exc!=12 || first_at!=443748)throw runtime_error("unexpected four-alphabet maximum");
 cout<<"PASS: full even horizon period P="<<PERIOD
     <<", four prime alphabet {61,67,71,73}, maximum exceptional events "<<max_exc
     <<" (first attained at C="<<first_at<<")\n";
 return max_exc;
}
// One 12-exception word is impossible already by the fourth genuine first hit.
// This does not certify that every 12-exception C-only word is impossible.
void rejected_word(){
 const array<int,19> Cs={442892,442964,442968,443038,443110,443112,443182,
  443254,443324,443326,443340,443406,443410,443470,443472,
  443538,443608,443674,443678};
 const array<int,19> es={73,5,71,73,3,71,73,71,3,15,67,5,61,3,67,71,67,5,71};
 const int C0=Cs[0];
 vector<int> candidates;
 for(int s=C0/2;s<C0;s++)candidates.push_back(s);
 const array<int,4> expected={4183,303,9,0};
 for(int k=0;k<4;k++){
  int C=Cs[k],e=es[k];vector<int> next;
  for(int s:candidates){
   int earliest=-1,actual_e=1;
   for(int g=1;g<=2*e && s+g<=C;g++){
    int r=s+g,v=full_gcd(r,C);
    if(v>1){earliest=r;actual_e=v;break;}
   }
   if(actual_e==e)next.push_back(earliest);
  }
  if(int(next.size())!=expected[k])throw runtime_error("first hit word count mismatch");
  sort(next.begin(),next.end());next.erase(unique(next.begin(),next.end()),next.end());
  cout<<"12-exception C-only candidate, true first-hit step "<<k+1
      <<": input="<<candidates.size()<<", matching="<<expected[k]
      <<", unique next indices="<<next.size()<<"\n";
  candidates.swap(next);
 }
 if(!candidates.empty())throw runtime_error("false candidate survived");
 cout<<"PASS: that specific 12-exception horizon word is not a genuine first-hit path\n";
}
int main(){
 try{Audit base;int n=wheel_four();rejected_word();
  // At most n exceptional p events, each with gap <=2p<=146.
  // There are at most n+1 supported-only strings, each with travel <=19.
  int T=2*73*n+19*(n+1);
  if(T!=1999)throw runtime_error("travel bound mismatch");
  cout<<"PAPER conditional: 12 exceptional steps imply total travel <= "<<T
      <<" for any authentic path with this increment alphabet\n";
  cout<<"Cap B for unrestricted increments is still open.\n";
 }catch(const exception&ex){cerr<<"FAIL: "<<ex.what()<<"\n";return 1;}
}