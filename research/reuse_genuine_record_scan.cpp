// Genuine A166944 canonical-record R_M and N_M measurement.
// Build: c++ -O3 -std=c++17 research/reuse_genuine_record_scan.cpp -o /tmp/real-scan
// Run: /tmp/real-scan 80000000   (or 220000000 for the extended run)
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
struct Record { ll M, K, N=0, R=0, G=0, H=0; unordered_set<ll> seen; };
vector<ll> prime_factors(ll n) {
  vector<ll> out;
  for (ll p=3; p*p<=n; p+=2) if (n%p==0) {
    out.push_back(p);
    do { n/=p; } while (n%p==0);
  }
  if (n>1) out.push_back(n);
  return out;
}
int main(int argc, char **argv) {
  ll LIM=argc>1 ? stoll(argv[1]) : 80000000, C=2, lastM=5;
  vector<Record> open;
  ll events=1, completed=0;
  for (ll n=3; n<=LIM; ++n) {
    ll e=gcd((n&1) ? n-2 : n, (n&1) ? C+1 : C-1);
    if (e>1) {
      C+=e-1;
      ++events;
      auto fs=prime_factors(e);
      for (auto &r:open) if (n>r.M+2 && n<=r.K) {
        r.N++;
        r.G+=e-1;
        r.H+=(e>11);
        bool repeated=false;
        for (ll p:fs) if (r.seen.count(p)) repeated=true;
        if (repeated) ++r.R;
        for (ll p:fs) r.seen.insert(p);
      }
      if (e>lastM && e>=7 && n==e+2) {
        lastM=e;
        Record z;
        z.M=e;
        z.K=(7*e-1)/4;
        open.push_back(move(z));
      }
    }
    for (size_t i=0; i<open.size();) {
      auto &r=open[i];
      if (n==r.K) {
        cout << "M=" << r.M << " K=" << r.K
             << " N=" << r.N << " R=" << r.R
             << " Hgt11=" << r.H << " G=" << r.G
             << " R/sqrtM=" << fixed << setprecision(6)
             << double(r.R)/sqrt(double(r.M))
             << " C=" << C << "\n";
        ++completed;
        open.erase(open.begin()+i);
      } else ++i;
    }
  }
  cerr << "completed=" << completed << " events=" << events
       << " last_C=" << C << " open_records=" << open.size() << "\n";
}
