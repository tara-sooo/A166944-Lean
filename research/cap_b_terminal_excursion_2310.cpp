// A166944 Cap B: finite mod-2310 first-hit certificate, 2026-11-21.
// Self-contained C++17. NOT a Lean proof, nor a proof of Cap B.
// This deliberately overapproximates genuine first-hit event states.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

namespace {
constexpr int MOD = 2310;                   // 2*3*5*7*11
constexpr int STATE_COUNT = MOD * (MOD / 2); // s mod 2310, even C mod 2310
constexpr std::array<int,4> SMALL = {3,5,7,11};
int key(int s, int c) { return (c / 2) * MOD + s; }

// Earliest possible clipped hit from the small-prime divisibility rules.
// If clipped gcd at that index is composite, it is not a small-prime edge.
struct Hit { int gap=0, residue=0, increment=0; };
Hit clipped_hit(int s, int c) {
  int best = MOD;
  for (int p : SMALL) {
    if (c % p == 1) {
      int g = (2*p - (s % (2*p))) % (2*p);
      if (g == 0) g = 2*p;
      best = std::min(best, g);
    }
    if (c % p == p-1) {
      int g = (p+2 - s % (2*p) + 2*p) % (2*p);
      if (g == 0) g = 2*p;
      best = std::min(best, g);
    }
  }
  if (best > 22) return {};
  int r = (s + best) % MOD;
  int f = (r % 2 == 0) ? r : r-2;
  int h = (r % 2 == 0) ? c-1 : c+1;
  return {best, r, std::gcd(std::gcd(f,h),MOD)};
}

bool is_small(int e) {
  return std::find(SMALL.begin(), SMALL.end(), e) != SMALL.end();
}
bool is_prime(std::uint64_t e) {
  if (e < 2) return false;
  for (std::uint64_t d=2; d*d<=e; ++d) if (e % d == 0) return false;
  return true;
}

struct Graph {
  std::vector<int> next = std::vector<int>(STATE_COUNT,-1);
  std::vector<int8_t> weight = std::vector<int8_t>(STATE_COUNT,0);
  std::vector<int8_t> potential = std::vector<int8_t>(STATE_COUNT,0);
  std::vector<int8_t> longest = std::vector<int8_t>(STATE_COUNT,0);
  int edges=0, max_run=0, max_potential=0, canonical_max=0;
  Graph() {
    for (int c=0;c<MOD;c+=2) for (int s=0;s<MOD;++s) {
      Hit h=clipped_hit(s,c);
      if (!is_small(h.increment)) continue;
      int i=key(s,c);
      int c_after=(c+h.increment-1)%MOD;
      next[i]=key(h.residue,c_after);
      weight[i]=static_cast<int8_t>(h.gap-2*(h.increment-1));
      ++edges;
    }
    // A functional graph: verify absence of directed cycles, and compute
    // longest paths plus the least nonnegative edge potential by reverse DP.
    std::vector<std::uint8_t> color(STATE_COUNT,0);
    std::vector<int> path;
    for (int start=0;start<STATE_COUNT;++start) {
      if (color[start]) continue;
      path.clear();
      int v=start;
      while (v>=0 && color[v]==0) {
        color[v]=1;
        path.push_back(v);
        v=next[v];
      }
      if (v>=0 && color[v]==1) {
        throw std::runtime_error("directed cycle in the small-prime graph");
      }
      for (auto it=path.rbegin();it!=path.rend();++it) {
        int i=*it, j=next[i];
        if (j>=0) {
          longest[i]=static_cast<int8_t>(1+longest[j]);
          potential[i]=static_cast<int8_t>(std::max(0, int(weight[i])+int(potential[j])));
        }
        max_run=std::max(max_run,int(longest[i]));
        max_potential=std::max(max_potential,int(potential[i]));
        color[i]=2;
      }
    }
    for (int i=0;i<STATE_COUNT;++i) {
      int j=next[i];
      if (j>=0 && int(weight[i])+int(potential[j])>int(potential[i])) {
        throw std::runtime_error("potential edge certificate failed");
      }
    }
    for (int M=1;M<=MOD;M+=6) {
      int s=(M+2)%MOD, c=(2*M-2)%MOD;
      canonical_max=std::max(canonical_max,int(potential[key(s,c)]));
    }
    if (edges!=2230860 || max_run!=22 || max_potential!=9 || canonical_max!=3)
      throw std::runtime_error("unexpected finite certificate statistics");
    // Positive prime p>=13 cost requires gap g>=2p-10.
    // The first-hit congruences imply p divides X-(2h-1) for even hits
    // or X-(2h+5) for odd hits, with h=2p-g in [0,10].
    // Hence X<=10 rules out positive debt for every prime p>=29.
    // Enumerate the only remaining primes 13,17,19,23.
    int candidate_count=0;
    for (int c=0;c<MOD;c+=2) for (int X=0;X<=10;X+=2)
      for (int branch=0;branch<=1;++branch) {
        int s=((c+X)/2+branch*(MOD/2))%MOD;
        Hit clipped=clipped_hit(s,c);
        for (int p : {13,17,19,23}) for (int h=0;h<=10;++h) {
          int g=2*p-h;
          if(clipped.gap>0 && g>=clipped.gap)continue;
          int r=(s+g)%MOD;
          int condition=(r%2==0) ? X+2*g+1 : X+2*g-5;
          if(condition%p != 0)continue;
          ++candidate_count;
          int successor=key(r,(c+p-1)%MOD);
          int net=g-2*(p-1)+int(potential[successor])-int(potential[key(s,c)]);
          if(net>0)throw std::runtime_error("low-offset prime-debt barrier failed");
        }
      }
    std::cout << "PASS: every prime>=13 event from X<=10 has nonpositive "
              << "2-growth debt; finite candidates=" << candidate_count << "\n";
    if(candidate_count!=3255)throw std::runtime_error("candidate count changed");
  }
  int W(std::uint64_t s,std::uint64_t C) const {
    return potential[key(int(s%MOD),int(C%MOD))];
  }
};

void direct_control(const Graph& graph,std::uint64_t M,int steps) {
  std::uint64_t s=M+2,C=2*M-2,T=0,G=0;
  int Wstart=graph.W(s,C);
  std::uint64_t debt=0,large_count=0,small_count=0,composite_count=0;
  for(int i=0;i<steps;++i) {
    bool hit=false;
    std::uint64_t r=0,e=0;
    for(std::uint64_t j=s+1;j<=C;++j) {
      std::uint64_t v=(j%2==0)?std::gcd(j,C-1):std::gcd(j-2,C+1);
      if(v>1){r=j;e=v;hit=true;break;}
    }
    if(!hit || e>M) throw std::runtime_error("missing/uncapped direct event");
    std::uint64_t Cnext=C+e-1, g=r-s;
    std::int64_t signed_cost=std::int64_t(g)-2*std::int64_t(e-1)
      +graph.W(r,Cnext)-graph.W(s,C);
    if(is_small(int(e))) ++small_count;
    else if(!is_prime(e)) ++composite_count;
    else ++large_count;
    if(!is_prime(e) || is_small(int(e))) {
      if(signed_cost>0) throw std::runtime_error("small/composite charge failed");
    } else if(signed_cost>0) debt+=std::uint64_t(signed_cost);
    s=r;C=Cnext;T+=g;G+=e-1;
  }
  if(T+graph.W(s,C)>2*G+Wstart+debt || debt>11*large_count)
    throw std::runtime_error("path budget failed");
  std::cout << "M=" << M << " steps=" << steps << " T=" << T
      << " G=" << G << " Wstart=" << Wstart << " debt=" << debt
      << " prime>=13_events=" << large_count << " small_events=" << small_count
      << " composite_events=" << composite_count << "\n";
}
} // namespace
int main(){
  try {
    Graph graph;
    std::cout << "PASS: mod=" << MOD << " states=" << STATE_COUNT
      << " small-prime-edges=" << graph.edges << " max_run=" << graph.max_run
      << " Wmax=" << graph.max_potential << " canonical_Wmax=" << graph.canonical_max << "\n";
    direct_control(graph,5419,9);
    direct_control(graph,45895573,37);
    direct_control(graph,5875882249ULL,26);
    // Genuine local first-hit counterexample to p^2<=C+1 in a large-X state.
    // It is NOT an authentic canonical-record history or a Cap B counterexample.
    constexpr std::uint64_t s=296451300, C=592874280, r=296483776, p=31091;
    if(!is_prime(p) || p*p<=C+1 || 2*s-C!=28320 || 2*r-(C+p-1)!=62182)
       throw std::runtime_error("large-offset witness data invalid");
    for(std::uint64_t j=s+1;j<=r;++j) {
      std::uint64_t e=(j%2==0)?std::gcd(j,C-1):std::gcd(j-2,C+1);
      if((j<r && e!=1) || (j==r && e!=p))
         throw std::runtime_error("large-offset first-hit witness invalid");
    }
    std::cout << "PASS: local first-hit counterexample to p^2<=C+1 "
              << "without low-offset assumptions\n";
    // Necessary terminal-excursion length under G<3M/8 at first crossing.
    constexpr std::uint64_t M0=45895573, K0=(7*M0-1)/4,
      G0=(3*M0-1)/8, U0=2*M0-1+G0, R0=10441;
    static_assert((R0-1)*(R0-1)<U0 && U0<=R0*R0);
    constexpr std::uint64_t numerator=2*K0-2*M0-6-G0-4*R0;
    constexpr std::uint64_t denominator=3*R0+1;
    constexpr std::uint64_t min_consecutive=(numerator+denominator-1)/denominator;
    static_assert(min_consecutive==1648);
    std::cout << "PASS: first crossing with G<=3M/8 at M=" << M0
              << " requires >=" << min_consecutive
              << " consecutive events since the last X<=10 state\n";
    std::cout << "Cap B remains open.\n";
  } catch(const std::exception& ex) {
    std::cerr << "FAIL: " << ex.what() << "\n";
    return 1;
  }
}
