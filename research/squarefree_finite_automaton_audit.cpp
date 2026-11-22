// Exact finite modular-transition audit for A166944 squarefree clipped gcd.
// Build: g++ -std=c++17 -O3 -Wall -Wextra squarefree_finite_automaton_audit.cpp -o finite_audit
// ./finite_audit [cutoff_prime=11] [mode=all|canonical]
// "all" traverses all 2*L^2 states and detects any nonabsorbing directed cycles;
// "canonical" explores the L initial odd canonical residues and detects loops.
// Finite integer computation, not Lean-checked proof and not a uniform theorem in L.
#include <bits/stdc++.h>
using namespace std;using ll=long long;
int main(int argc,char**argv){int cap=argc>1?atoi(argv[1]):11;string mode=argc>2?argv[2]:"all";
 vector<int> primes;ll L=1;for(int p=3;p<=cap;p+=2){bool pr=true;for(int d=3;d*d<=p;d+=2)if(p%d==0)pr=false;if(pr){L*=p;primes.push_back(p);}}if(L<=1||L>15015||(mode=="all"&&L>1155)){cerr<<"cap too large\n";return 2;}
 auto calc=[&](int n,int C){int d=std::gcd(int(L),std::gcd(n%2==0?n:n-2,n%2==0?C-1:C+1));return d;};
 auto absorber=[&](int C){return std::gcd(int(L),int((ll)(C+1)*(C-1)))==1;};
 if(mode=="canonical"){
   ll maxsteps=0,maxgrowth=0,maxidx=-1;int cy=0;ll total=0;for(int v=1;v<2*L;v+=2){int C=(2*v-2)%(int)L;int n=v+3;ll g=0,steps=0;unordered_map<ll,ll> visited;while(!absorber(C)){
    ll key=(n%(2*L))*L+C;
    if(visited.find(key)!=visited.end()){cy++;break;}
    visited[key]=steps;int d=calc(n,C);C=(C+d-1)%(int)L;g+=d-1;n++;steps++;
    if(steps>100000){cy++;break;}
   }if(steps>maxsteps){maxsteps=steps;maxidx=v;}maxgrowth=max(maxgrowth,g);total+=g;}
   cout<<"CANONICAL cap="<<cap<<" L="<<L<<" seeds="<<L<<" absorbed="<<L-cy<<" cycles="<<cy<<" maxsteps="<<maxsteps<<" maxstep_v="<<maxidx<<" maxgrowth="<<maxgrowth<<" totalgrowth="<<total<<"\n";
   return cy?3:0;
 }
 ll N=2*L*L;vector<unsigned char> color(N,0);vector<int> pos(N,-1);ll cycles=0,positive=0,total_len=0,maxcycle=0,maxpositive=0,maxcycleexample=-1;ll numabs=0;
 auto nxt=[&](int z){int n=z/(int)L,C=z%(int)L,d=calc(n,C);int newn=(n+1)%(2*L);return pair<int,int>(newn*(int)L+(C+d-1)%(int)L,d);};
 for(int initial=0;initial<N;initial++)if(!color[initial]){
    vector<int> path;int cur=initial;
    while(!color[cur]){color[cur]=1;pos[cur]=int(path.size());path.push_back(cur);cur=nxt(cur).first;}
    if(color[cur]==1){cycles++;ll grow=0;int len=0;for(int t=pos[cur];t<int(path.size());t++){grow+=nxt(path[t]).second-1;len++;}if(grow>0){positive++;maxpositive=max(maxpositive,grow);maxcycleexample=cur;}total_len+=len;maxcycle=max(maxcycle,ll(len));}
    for(int z:path){color[z]=2;pos[z]=-1;}
 }
 for(int C=0;C<L;C++)if(absorber(C))numabs++;
 cout<<"ALL_STATES cap="<<cap<<" L="<<L<<" states="<<N<<" cycles="<<cycles<<" positive_cycles="<<positive<<" max_cycle_length="<<maxcycle<<" positive_cycle_max_growth="<<maxpositive<<" example_state="<<maxcycleexample<<" absorbing_horizon_residues="<<numabs<<"\n";
 if(mode=="all" && ((cap==3&&cycles!=1)||(cap==5&&cycles!=3)||(cap==7&&cycles!=15)||(cap==11&&cycles!=135)))throw runtime_error("all-states regression mismatch");
return positive?4:0;
}
