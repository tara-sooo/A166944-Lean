// Exact finite-state certificate for A166944 small-increment exhaustion.
// Build: c++ -O3 -std=c++17 research/reuse_small_wheel_exhaustion.cpp -o /tmp/wheel-check
// Run: for L in 105 315 1155 3465; do /tmp/wheel-check $L; done
// The gcd is truncated to L; this matches the genuine recurrence on any
// segment whose every increment divides L. In particular, e <= 11
// (odd) implies e | 3465.
// Finite exhaustive enumeration, NOT a Lean-kernel proof or Cap B proof.
#include <bits/stdc++.h>
using namespace std;

static int step_gcd(int n, int c, int L, int mod) {
  int r = (n + 1) % mod;
  int index_arg = (r & 1) ? r - 2 : r;
  int horizon_arg = (r & 1) ? c + 1 : c - 1;
  return gcd(gcd(abs(index_arg), abs(horizon_arg)), L);
}

int main(int argc, char **argv) {
  const int L = argc > 1 ? atoi(argv[1]) : 3465;
  if (L != 105 && L != 315 && L != 1155 && L != 3465) return 2;
  const int mod = 2 * L;
  const int64_t total = 1LL * L * mod;
  vector<int32_t> nxt(total);
  vector<uint8_t> state(total, 0), score(total, 0);
  vector<int32_t> path;
  path.reserve(mod * 3);

  for (int c = 0; c < L; ++c) {
    for (int n = 0; n < mod; ++n) {
      const int d = step_gcd(n, c, L, mod);
      const int r = (n + 1) % mod;
      nxt[(int64_t)c * mod + n] = ((c + d - 1) % L) * mod + r;
    }
  }

  int cycles = 0, positive_cycles = 0, max_hits = 0;
  for (int64_t start = 0; start < total; ++start) {
    if (state[start]) continue;
    path.clear();
    int32_t x = start;
    while (state[x] == 0) {
      state[x] = 1;
      path.push_back(x);
      x = nxt[x];
    }
    if (state[x] == 1) {
      ++cycles;
      int j = int(path.size()) - 1;
      while (path[j] != x) --j;
      bool active = false;
      for (int k = j; k < int(path.size()); ++k) {
        int y = path[k];
        if (step_gcd(y % mod, y / mod, L, mod) > 1) active = true;
        state[y] = 2;
        score[y] = 0;
      }
      positive_cycles += active;
      path.resize(j);
    }
    for (int j = int(path.size()) - 1; j >= 0; --j) {
      int y = path[j];
      int val = int(score[nxt[y]]) + (step_gcd(y % mod, y / mod, L, mod) > 1);
      if (val > 255) return 3;
      score[y] = uint8_t(val);
      state[y] = 2;
    }
  }

  int max_canonical = 0, max_twin_admissible = 0, admissible = 0;
  for (int64_t i = 0; i < total; ++i) max_hits = max(max_hits, int(score[i]));
  for (int Mres = 1; Mres < mod; Mres += 2) {
    const int s = (Mres + 2) % mod;
    const int c = int((2LL * Mres - 2) % L);
    const int value = score[c * mod + s];
    max_canonical = max(max_canonical, value);
    bool prime_pair_mod_small = true;
    for (int q : {3, 5, 7, 11}) {
      if (L % q == 0 && (Mres % q == 0 || Mres % q == 2))
        prime_pair_mod_small = false;
    }
    if (prime_pair_mod_small) {
      ++admissible;
      max_twin_admissible = max(max_twin_admissible, value);
    }
  }

  struct Expected { int L, cycles, max_hits, max_can, max_twin, admissible; };
  static const Expected ref[] = {
    {105, 15, 9, 8, 5, 15},
    {315, 45, 10, 8, 5, 45},
    {1155, 135, 22, 18, 13, 135},
    {3465, 405, 29, 19, 16, 405}
  };
  const Expected *want = nullptr;
  for (const auto &a : ref) if (a.L == L) want = &a;
  if (!want || positive_cycles || cycles != want->cycles ||
      max_hits != want->max_hits || max_canonical != want->max_can ||
      max_twin_admissible != want->max_twin ||
      admissible != want->admissible) {
    cerr << "FAIL: exhaustiveness certificate mismatch\n";
    return 4;
  }
  cout << "PASS L=" << L
       << " states=" << total
       << " quiet_cycles=" << cycles
       << " max_all=" << max_hits
       << " max_canonical=" << max_canonical
       << " max_twin_admissible=" << max_twin_admissible
       << " admissible_residues=" << admissible << "\n";
  return 0;
}
