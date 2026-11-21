// Finite necessary-condition test for A166944 Cap B, 2026-11-21.
// C++17, standard library only. NOT a proof of unrestricted Cap B.
// Any genuine event with increment e divides C-1 or C+1.
// A supported event e|30 has e in {3,5,15} and raises C by e-1.
// Between two exceptional hits, enumerate ALL possible supported C changes.
// For three fixed distinct exceptional primes, keep the full C mod 30*p*q*r.
// This graph overapproximates genuine first-gcd event sequences.
#include <algorithm>
#include <array>
#include <deque>
#include <iostream>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <vector>
using namespace std;

constexpr array<int, 3> supported = {3, 5, 15};
constexpr array<int, 15> U = {0,10,8,6,4,2,0,16,14,0,10,8,6,4,2};
bool eligible(int c, int e) {
  return (c+1)%e==0 || (c-1+e)%e==0;
}
struct Support {
  array<vector<int>,30> totals;
  int max_growth=0, max_steps=0, edges=0;
  Support() {
    for(int c=0;c<30;c+=2) {
      for(int e:supported) if(eligible(c,e)) {
        ++edges;
        if(e-1+U[((c+e-1)%30)/2]>U[c/2])
          throw runtime_error("support potential inequality failed");
      }
      auto walk=[&](auto&& self,int residue,int growth,int depth)->void{
        totals[c].push_back(growth);
        max_growth=max(max_growth,growth);
        max_steps=max(max_steps,depth);
        if(depth>8) throw runtime_error("unexpected long supported path");
        for(int e:supported) if(eligible(residue,e))
          self(self,(residue+e-1)%30,growth+e-1,depth+1);
      };
      walk(walk,c,0,0);
      auto &v=totals[c];
      sort(v.begin(),v.end());
      v.erase(unique(v.begin(),v.end()),v.end());
      for(int h:v) if(h>U[c/2]) throw runtime_error("supported growth exceeded U");
    }
    if(edges!=18 || max_growth!=16 || max_steps!=6)
      throw runtime_error("unexpected support wheel result");
  }
};

struct Stats {int states,edges,maxlen;bool cycle;};
Stats triple(array<int,3> p,const Support& wheel) {
  const int L=15*p[0]*p[1]*p[2]; // C/2 modulo (30*p*q*r)/2
  vector<vector<int>> id(3,vector<int>(L,-1));
  vector<pair<int,int>> vertex;
  for(int k=0;k<3;++k)
    for(int sign:{-1,1}) {
      int q=p[k], inv2=(q+1)/2;
      int root=((sign*inv2)%q+q)%q;
      for(int m=root;m<L;m+=q) {
        id[k][m]=int(vertex.size());
        vertex.emplace_back(m,k);
      }
    }
  const int V=int(vertex.size());
  vector<vector<int>> adj(V);
  vector<int> indeg(V,0),length(V,1);
  int edge_count=0;
  for(int i=0;i<V;++i) {
    auto [m,k]=vertex[i];
    const int e=p[k], after_c=(2LL*m+e-1)%30;
    for(int H:wheel.totals[after_c]) {
      int mnext=(m+(e-1+H)/2)%L;
      for(int j=0;j<3;++j) if(j!=k) {
        int dest=id[j][mnext];
        if(dest<0) continue;
        adj[i].push_back(dest);
        ++indeg[dest];
        ++edge_count;
      }
    }
  }
  deque<int> queue;
  for(int i=0;i<V;++i) if(indeg[i]==0) queue.push_back(i);
  int processed=0, maximum=0;
  while(!queue.empty()) {
    int u=queue.front();queue.pop_front();
    ++processed;
    maximum=max(maximum,length[u]);
    for(int v:adj[u]) {
      length[v]=max(length[v],length[u]+1);
      if(--indeg[v]==0) queue.push_back(v);
    }
  }
  return {V,edge_count,maximum,processed!=V};
}
int main() {
  try {
    const Support wheel;
    cout<<"PASS: 15 even C residues, "<<wheel.edges
        <<" supported edges, maximal growth "<<wheel.max_growth
        <<", maximal supported events "<<wheel.max_steps<<"\n";
    vector<int> primes;
    for(int p=61;p<=109;p+=2) {
      bool prime=true;
      for(int d=3;d*d<=p;d+=2) if(p%d==0) {prime=false;break;}
      if(prime) primes.push_back(p);
    }
    if(primes.size()!=12) throw runtime_error("unexpected prime set");
    int checked=0, cycles=0, overall=0;
    array<int,3> worst={0,0,0};
    for(int i=0;i<int(primes.size());++i)
      for(int j=i+1;j<int(primes.size());++j)
        for(int k=j+1;k<int(primes.size());++k) {
          auto p=array<int,3>{primes[i],primes[j],primes[k]};
          auto x=triple(p,wheel);
          ++checked;
          if(x.cycle) ++cycles;
          if(x.maxlen>overall) {overall=x.maxlen;worst=p;}
        }
    cout<<"triples="<<checked<<", cycles="<<cycles
        <<", maximum exceptional events="<<overall
        <<", extremal primes="<<worst[0]<<","<<worst[1]<<","<<worst[2]<<"\n";
    if(checked!=220 || cycles!=0 || overall!=11 ||
       worst!=array<int,3>{67,71,73})
      throw runtime_error("unexpected three-exception graph certificate");
    cout<<"PASS: all 220 necessary-condition graphs exclude 12 exceptional events\n";
    cout<<"Cap B without the restricted exceptional-alphabet hypothesis remains OPEN.\n";
  } catch(const exception& ex) {
    cerr<<"FAIL: "<<ex.what()<<"\n";
    return 1;
  }
}
