// Exact parity-GCD squarefree-wheel audit of the cross-prime four-residue
// correlation for A166944. Finite observations only; NOT a uniform theorem.
//
// Build: g++ -O3 -std=c++17 cross_prime_four_residue_audit.cpp -o cross_prime_audit
// Run:   ./cross_prime_audit 4096
//        ./cross_prime_audit 16384
//        ./cross_prime_audit 65536
//        ./cross_prime_audit 262144 fast    // skip expensive full reference
//
// The reference 4 * sum_p sum_v G_{L_p}(v) is a deterministic comparison,
// not evidence of stochastic independence or a proved equidistribution law.

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using i64 = long long;

vector<int> spf;

vector<int> distinct_factors(int n) {
    vector<int> factors;
    while (n > 1) {
        const int p = spf.at(n);
        factors.push_back(p);
        do { n /= p; } while (n % p == 0);
    }
    return factors;
}

// Smallest position strictly after pos in the residue r (mod 2p).
i64 next_hit(i64 pos, int p, int r) {
    i64 gap = (r - pos) % (2LL * p);
    if (gap <= 0) gap += 2LL * p;
    return pos + gap;
}

// Initial canonical seed at odd M: s=M+2 and D(s)=2M-2.
// The capped increment multiplies every distinct factor <= P of the raw gcd;
// this is gcd(raw_gcd, squarefree primorial through P).
int growth_by_events(int M, int P) {
    i64 n0 = M + 2, K = (7LL * M - 1) / 4, C = 2LL * M - 2;
    while (n0 < K) {
        i64 next = K + 1;
        for (int q : distinct_factors(int(C - 1)))
            if (q <= P) next = min(next, next_hit(n0, q, 0));
        for (int q : distinct_factors(int(C + 1)))
            if (q <= P) next = min(next, next_hit(n0, q, q + 2));
        if (next > K) break;
        const int g = int(gcd((next & 1) ? next - 2 : next,
                              (next & 1) ? C + 1 : C - 1));
        int d = 1;
        for (int q : distinct_factors(g)) if (q <= P) d *= q;
        if (d <= 1) throw runtime_error("first-hit clock mismatch");
        C += d - 1;
        n0 = next;
    }
    return int(C - (2LL * M - 2));
}

// Deliberately independent step-by-step recurrence, for small test cases.
int growth_by_steps(int M, int P) {
    i64 C = 2LL * M - 2;
    const int K = int((7LL * M - 1) / 4);
    for (int n = M + 3; n <= K; ++n) {
        const int g = int(gcd((n & 1) ? n - 2 : n,
                              (n & 1) ? C + 1 : C - 1));
        int d = 1;
        for (int q : distinct_factors(g)) if (q <= P) d *= q;
        C += d - 1;
    }
    return int(C - (2LL * M - 2));
}

struct RefireAudit {i64 verified_windows, least_slack;};
RefireAudit verify_refire_recharge() {
    i64 verified = 0, least = -1;
    for (int cap : {5, 7, 11, 17, 31, 41}) {
        for (int M = 7; M <= 999; M += 2) {
            i64 C = 2LL * M - 2;
            vector<bool> seen(cap + 1, false), last_odd(cap + 1, false);
            vector<i64> between(cap + 1, 0);
            for (int n = M + 3, K = int((7LL * M - 1) / 4); n <= K; ++n) {
                const int g = int(gcd((n & 1) ? n - 2 : n,
                                      (n & 1) ? C + 1 : C - 1));
                int d = 1;
                for (int q : distinct_factors(g)) if (q <= cap) d *= q;
                for (int q = 5; q <= cap; q += 2) {
                    if (spf[q] != q) continue;
                    if (d % q == 0) {
                        if (seen[q]) {
                            const i64 threshold = q + (last_odd[q] ? 1 : -1);
                            if (between[q] < threshold)
                                throw runtime_error("p-refire recharge modular lemma failed");
                            least = (least < 0) ? between[q] - threshold
                                                : min(least, between[q] - threshold);
                            ++verified;
                        }
                        seen[q] = true;
                        last_odd[q] = (n & 1);
                        between[q] = 0;
                    } else if (seen[q]) {
                        between[q] += d - 1;
                    }
                }
                C += d - 1;
            }
        }
    }
    return {verified, least};
}

struct Regression {int X, B, count; i64 E, w_sum, w_sq;};
const Regression regressions[] = {
    {4096,   170,   35,     36344568LL,       304218LL,      63145432LL},
    {16384,  339,   64,    485635362LL,      2163729LL,     847926453LL},
    {65536,  678,  119,   5672417264LL,     15849484LL,            -1LL},
    {262144,1355,  213,  69630701976LL,    112570828LL,            -1LL}
};

int main(int argc, char **argv) {
    const int X = argc > 1 ? atoi(argv[1]) : 4096;
    const bool fast = argc > 2 && string(argv[2]) == "fast";
    if (X < 256 || X > 262144 || (X & 1)) return 2;
    const int B = int(ceil(sqrt(7.0 * X)));
    // c=2 common window for the post-freeze height-zero L1 transfer.
    const int U = 2 * X + (3 * B + 7) / 2 + 5;
    const int Z = 7 * U + 100;
    spf.resize(Z);
    iota(spf.begin(), spf.end(), 0);
    for (int p = 2; 1LL * p * p < Z; ++p)
        if (spf[p] == p)
            for (int j = p * p; j < Z; j += p)
                if (spf[j] == j) spf[j] = p;

    // Cross-check event skipping against a literal step-by-step gcd trajectory.
    for (int M = 7; M <= 119; M += 2)
        for (int p : {1, 3, 5, 7, 11, 13})
            if (growth_by_events(M, p) != growth_by_steps(M, p))
                throw runtime_error("direct-gcd vs jump mismatch");

    const RefireAudit refire = verify_refire_recharge();

    const i64 V = (U - X) / 2; // odd v: X+1, X+3, ..., <U
    vector<i64> w(V, 0), envelope(V, 0);
    i64 E = 0, total_T1 = 0, hits = 0, S1 = 0, S2 = 0;
    i64 old_all = 0;
    int countP = 0;
    int previous_prime = 7;
    for (int p = 11; p <= B; p += 2) {
        if (spf[p] != p) continue;
        // L_p is the product of ALL odd primes strictly below p, including 3,5,7.
        // After p>=11, the last prime strictly below p is kept by this iterator.
        const int oldP = previous_prime;
        ++countP;
        S1 += p;
        S2 += 1LL * p * p;
        for (int v = X + 1; v < U; v += 2) {
            const int r = v % p;
            const bool selected = r == 0 || r == 1 || r == 3 || r == 5;
            if (!selected && fast) continue;
            const int h = growth_by_events(v, oldP);
            if (!fast) old_all += h;
            if (!selected) continue;
            const i64 i = (v - X - 1) / 2;
            E += 1LL * p * h;
            total_T1 += h;
            ++hits;
            w[i] += p;
            envelope[i] = max(envelope[i], i64(h));
        }
        previous_prime = p;
    }
    i64 wsum = 0, wsq = 0, wmax = 0, vmax = 0, weighted_envelope = 0;
    for (i64 i = 0; i < V; ++i) {
        wsum += w[i];
        wsq += w[i] * w[i];
        weighted_envelope += w[i] * envelope[i];
        if (w[i] > wmax) {wmax = w[i]; vmax = X + 1 + 2 * i;}
    }
    if (E > weighted_envelope) throw runtime_error("envelope upper bound failed");
    if (wsum > 4 * V * countP + 4 * S1)
        throw runtime_error("exact congruence mass bound failed");
    // 4 residues mod p; 16 simultaneous residues mod pq for p!=q.
    const i64 second_upper = 4 * V * S1 + 4 * S2
        + 16 * V * countP * (countP - 1) + 16 * (S1 * S1 - S2);
    if (wsq > second_upper) throw runtime_error("CRT second-moment bound failed");
    for (const auto &t : regressions) if (t.X == X) {
        if (B != t.B || countP != t.count || E != t.E || wsum != t.w_sum
                || (t.w_sq >= 0 && wsq != t.w_sq))
            throw runtime_error("stored finite result regression failed");
    }
    cout << setprecision(10)
        << "PASS X=" << X << " B=" << B << " U=" << U
        << " primes=" << countP << " v_count=" << V << '\n'
        << "E=" << E << " E/(X*B^2/log(B))="
        << double(E) * log(double(B)) / (double(X) * B * B) << '\n'
        << "T1_sum=" << total_T1 << " candidate_hits=" << hits << '\n'
        << "weighted_residue_mass=" << wsum << " max_w=" << wmax
        << " max_w_at_v=" << vmax << '\n'
        << "w_second_moment=" << wsq << " rigorous_CRT_upper=" << second_upper << '\n'
        << "weighted_envelope_upper=" << weighted_envelope << '\n'
        << "refire_windows_verified=" << refire.verified_windows
        << " min_recharge_slack=" << refire.least_slack << '\n';
    if (!fast) cout << "reference_4_sum_all_old=" << 4 * old_all
        << " ratio_to_reference=" << double(E) / (4 * old_all)
        << " signed_discrepancy=" << E - 4 * old_all << '\n';
    cout << "Uniform-in-X growth-correlation bound remains OPEN.\n";
}
