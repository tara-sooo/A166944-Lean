// Synthetic canonical starts with twin-prime input, factorized first hits.
// Build: c++ -O3 -std=c++17 research/twin_input_canonical_cutoff_scan.cpp -o /tmp/a166944-twinscan
// Run: /tmp/a166944-twinscan 20000000
// This is a FINITE TEST of artificially assigned states, NOT a proof of twin primes.
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <numeric>
#include <vector>
using namespace std;
using ll = long long;
vector<int> smallPrimes;
vector<unsigned char> sieve;

void init(int N) {
  sieve.assign(N + 1, 1);
  sieve[0] = sieve[1] = 0;
  for (int i = 2; 1LL*i*i <= N; ++i)
    if (sieve[i])
      for (int j = i*i; j <= N; j += i) sieve[j] = 0;
  for (int i = 3; i <= N; i += 2) if (sieve[i]) smallPrimes.push_back(i);
}
vector<ll> distinctFactors(ll n) {
  vector<ll> out;
  for (int p : smallPrimes) {
    if (1LL*p*p > n) break;
    if (n % p == 0) {
      out.push_back(p);
      do { n /= p; } while (n % p == 0);
    }
  }
  if (n > 1) out.push_back(n);
  return out;
}
bool prime(ll n) {
  if (n < 2 || n % 2 == 0) return n == 2;
  for (int p : smallPrimes) {
    if (1LL*p*p > n) break;
    if (n % p == 0) return false;
  }
  return true;
}
ll gcdTest(ll r,ll C) {
  return gcd(r % 2 ? r-2 : r, r % 2 ? C+1 : C-1);
}
pair<ll,ll> nextHit(ll s,ll C) {
  ll J = numeric_limits<ll>::max();
  for (ll p : distinctFactors(C-1)) {
    ll d = (-s) % (2*p);
    if (d <= 0) d += 2*p;
    J = min(J,s+d);
  }
  for (ll p : distinctFactors(C+1)) {
    ll d = (p+2-s) % (2*p);
    if (d <= 0) d += 2*p;
    J = min(J,s+d);
  }
  ll e = gcdTest(J,C);
  if (e <= 1) { cerr << "broken factor-map next hit\n"; exit(3); }
  return {J,e};
}
struct Result { ll M,K,S,C; int events; };
Result run(ll M) {
  ll K = (7*M-1)/4, C = 2*M-2, S=M+2;
  int events=0;
  while (true) {
    auto [J,e] = nextHit(S,C);
    if (J > K) break;
    if (e > M) { cerr<<"unexpected capped-window new record\n"; exit(4); }
    C += e-1; S=J; ++events;
  }
  return {M,K,S,C,events};
}
void checkDirect() {
  int checked=0;
  for (int M=7; M<20000; M+=2) {
    if (!(sieve[M] && sieve[M-2])) continue;
    auto r=run(M);
    ll C=2*M-2, S=M+2; int events=0;
    for (ll j=M+3;j<=r.K;j++) {
      ll e=gcdTest(j,C);
      if (e>1) {C+=e-1;S=j;events++;}
    }
    if (C!=r.C || S!=r.S || events!=r.events) {
      cerr << "direct gcd crosscheck failed, M=" << M << "\n"; exit(5);
    }
    checked++;
  }
  cout << "Direct per-index gcd comparison, twin-input starts: "
       << checked << " PASS\n";
}
int main(int argc, char **argv) {
  int N=argc>1?atoi(argv[1]):20000000;
  if (N<20000 || N>100000000) {
    cerr << "Use a bound between 20000 and 100000000\n"; return 1;
  }
  init(N);
  checkDirect();
  ll count=0, events=0; vector<ll> failures;
  for (int M=7; M<=N; M+=2) {
    if (!(sieve[M] && sieve[M-2])) continue;
    Result r=run(M);
    count++;events+=r.events;
    if (!(prime(r.C-1) && prime(r.C+1))) {
      failures.push_back(M);
      cout << "NON-TWIN artificial input M=" << M
           << " K=" << r.K << " C=" << r.C << "\n";
    }
  }
  cout << "N=" << N << " twin-prime starting inputs=" << count
       << " first-hit events=" << events
       << " terminal non-twin count=" << failures.size() << "\n";
  if (N==20000000) {
    if (count != 107406 || events != 4859867 ||
        failures != vector<ll>{13,43}) {
      cerr << "known finite certificate mismatched\n"; return 6;
    }
  }
  cout << "PASS: finite twin-input scan only; no universal twin-prime proof\n";
}
