#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

// Enumerate continuations after a small offset using only increments
// below a cutoff and dividing the modulus. A genuine continuation with
// these increments agrees with the clipped first hits up to its end.

struct Step { int gap; int increment; };

Step next_clipped(int s, int horizon, int modulus, const std::vector<int>& primes) {
    int gap = modulus + 1;
    for (int prime : primes) {
        const int period = 2 * prime;
        for (int odd = 0; odd <= 1; ++odd) {
            if ((horizon + (odd ? 1 : -1)) % prime == 0) {
                const int residue = odd ? prime + 2 : 0;
                const int distance = 1 + (residue + period - (s + 1) % period) % period;
                gap = std::min(gap, distance);
            }
        }
    }
    if (gap > modulus) return {0, 1};
    const int hit = s + gap;
    const int left = hit - ((hit % 2) ? 2 : 0);
    const int right = horizon + ((hit % 2) ? 1 : -1);
    return {gap, std::gcd(std::gcd(left, right), modulus)};
}

void scan(int modulus, int cutoff, const std::vector<int>& primes) {
    int max_offset = 0;
    int max_steps = 0;
    int max_growth = 0;
    std::array<int, 4> arg{};
    std::int64_t events = 0;
    for (int index = 0; index < modulus; ++index) {
        for (int initial_offset : {0, 2, 4, 6}) {
            int s = index;
            int horizon = (2 * index + modulus - initial_offset) % modulus;
            const int origin = horizon;
            int offset = initial_offset;
            int steps = 0;
            for (;;) {
                const auto [gap, increment] = next_clipped(s, horizon, modulus, primes);
                if (gap == 0 || increment > cutoff) break;
                assert(increment > 1 && modulus % increment == 0);
                offset += 2 * gap - (increment - 1);
                if (offset < 0) break;
                s += gap;
                horizon += increment - 1;
                assert(horizon <= modulus);
                ++events;
                ++steps;
                if (offset > max_offset) {
                    max_offset = offset;
                    arg = {index, initial_offset, steps, horizon - origin};
                }
                max_steps = std::max(max_steps, steps);
                max_growth = std::max(max_growth, horizon - origin);
            }
        }
    }
    std::cout << "modulus=" << modulus << " cutoff=" << cutoff << " starts=" << 4 * modulus
              << " events=" << events << " max_offset=" << max_offset << " max_steps=" << max_steps
              << " max_growth=" << max_growth << " witness=" << arg[0] << ',' << arg[1] << ','
              << arg[2] << ',' << arg[3] << '\n';
}

int main() {
    scan(210, 7, {3,5,7});
    scan(210, 210, {3,5,7});
    scan(630, 9, {3,5,7});
    scan(6930, 11, {3,5,7,11});
    scan(90090, 15, {3,5,7,11,13});
}
