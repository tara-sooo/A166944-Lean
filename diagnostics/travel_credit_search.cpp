// Exact bounded search for unpaid same-phase long-prime balances.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <vector>

struct Event {
    int hit;
    int horizon;
    int increment;
    int excess;
    int balance;
};

std::vector<int> residue_potentials() {
    std::vector<int> table(210 * 105);
    for (int horizon = 208; horizon >= 2; horizon -= 2) {
        for (int index = 0; index < 210; ++index) {
            for (int gap = 1; gap <= 14; ++gap) {
                const int hit = index + gap;
                const int increment = std::gcd(210, std::gcd(
                    hit % 2 ? hit - 2 : hit, horizon + (hit % 2 ? 1 : -1)));
                if (increment <= 1) continue;
                const int growth = increment - 1;
                assert(horizon + growth <= 210);
                const int after = table[((horizon + growth) % 210) / 2 * 210 + hit % 210];
                const int excess = std::max(0, 24 * gap - growth);
                table[horizon / 2 * 210 + index] = std::max(0, excess + after - 2 * growth);
                break;
            }
        }
    }
    assert(*std::max_element(table.begin(), table.end()) == 1260);
    return table;
}

std::vector<uint16_t> odd_factors(int bound) {
    std::vector<uint16_t> factor(bound / 2 + 1);
    for (int p = 3; int64_t(p) * p <= bound; p += 2) {
        if (factor[p / 2]) continue;
        for (int64_t n = int64_t(p) * p; n <= bound; n += 2 * p) {
            if (!factor[n / 2]) factor[n / 2] = p;
        }
    }
    return factor;
}

int next_hit(int index, int horizon, const std::vector<uint16_t>& factor) {
    assert(horizon / 2 < int(factor.size()));
    int earliest = horizon + 1;
    for (int odd = 0; odd < 2; ++odd) {
        int term = horizon + (odd ? 1 : -1);
        while (term > 1) {
            int p = factor[term / 2];
            if (!p) p = term;
            const int residue = odd ? p + 2 : 0;
            const int period = 2 * p;
            const int candidate = index + 1 + (residue - (index + 1) % period + period) % period;
            earliest = std::min(earliest, candidate);
            do {
                term /= p;
            } while (term % p == 0);
        }
    }
    return earliest;
}

int main(int argc, char** argv) {
    const bool funded = (argc == 4 || argc == 6) && std::string(argv[2]) == "--funded";
    if ((argc != 2 && !funded) || (argc == 6 && std::string(argv[4]) != "--growth-charge")) {
        std::cerr << "Usage: travel_credit_search LIMIT [--funded MULTIPLIER [--growth-charge 2|4]] | --table\n";
        return 2;
    }
    const int multiplier = funded ? std::stoi(argv[3]) : 0;
    const int growth_charge = argc == 6 ? std::stoi(argv[5]) : 2;
    if (multiplier < 0 || multiplier > 24) {
        std::cerr << "MULTIPLIER must be between 0 and 24\n";
        return 2;
    }
    if (growth_charge != 2 && growth_charge != 4) {
        std::cerr << "GROWTH_CHARGE must be 2 or 4\n";
        return 2;
    }
    const auto potential = residue_potentials();
    if (std::string(argv[1]) == "--table") {
        for (int value : potential) std::cout << value << '\n';
        return 0;
    }
    const int limit = std::stoi(argv[1]);
    if (limit < 13 || limit > 100000000) {
        std::cerr << "LIMIT must be between 13 and 100000000\n";
        return 2;
    }
    const auto factor = odd_factors(3 * limit + 10);
    auto is_prime = [&](int n) {
        return n > 2 && (n % 2) && factor[n / 2] == 0;
    };
    auto value = [&](int index, int horizon) {
        return potential[(horizon % 210) / 2 * 210 + index % 210];
    };
    int starts = 0, demands = 0, cutoff_stops = 0, event_limit_stops = 0;
    int64_t maximum_startup = 0;
    for (int record = 13; record <= limit; record += 6) {
        if (!is_prime(record) || !is_prime(record - 2)) continue;
        ++starts;
        int index = record + 2, horizon = 2 * record - 2;
        std::unordered_map<int64_t, int> previous_phase;
        std::unordered_map<int64_t, int> previous_positive;
        std::vector<Event> history;
        std::vector<std::pair<int, int>> credits;
        int64_t first = 0, startup = 0, signed_sum = 0;
        while (true) {
            if (history.size() >= 3000) {
                ++event_limit_stops;
                break;
            }
            const int hit = next_hit(index, horizon, factor);
            if (hit > horizon) break;
            const int increment = std::gcd(hit % 2 ? hit - 2 : hit, horizon + (hit % 2 ? 1 : -1));
            if (increment > record || 2 * (hit - (record + 2)) > record) {
                ++cutoff_stops;
                break;
            }
            const int gap = hit - index, updated = horizon + increment - 1;
            const bool long_prime = gap > 10 && is_prime(increment);
            const int64_t key = int64_t(increment) * 420 + (horizon % 210) * 2 + (hit % 2);
            const auto found = previous_phase.find(key);
            const int previous = long_prime && found != previous_phase.end() ? found->second : -1;
            const int excess = gap <= 10 || previous >= 0 ? std::max(0, 24 * gap - (increment - 1)) : 0;
            const int balance = excess + value(hit, updated) - value(index, horizon) - growth_charge * (increment - 1);
            const auto positive_found = previous_positive.find(key);
            const int prior_positive = positive_found != previous_positive.end() ? positive_found->second : -1;
            const int anchor = previous >= 0 ? previous : prior_positive;
            if (long_prime && previous < 0) {
                first += gap;
                if (funded) credits.emplace_back(2 * history.size() + 1, multiplier * gap);
            }
            if (210 % increment) {
                signed_sum += balance;
                if (balance < 0) {
                    credits.emplace_back(2 * history.size(), -balance);
                } else if (balance > 0 && anchor >= 0) {
                    ++demands;
                    int owed = balance;
                    for (auto& credit : credits) {
                        if (credit.first <= 2 * anchor) continue;
                        const int used = std::min(owed, credit.second);
                        owed -= used;
                        credit.second -= used;
                        if (owed == 0) break;
                    }
                    if (owed) {
                        std::cout << "Unpaid synthetic start " << record << ", increment " << increment
                                  << ", earlier hit " << history[anchor].hit << ", hit " << hit
                                  << ", balance " << balance << ", unpaid " << owed << '\n';
                        for (int j = anchor; j < int(history.size()); ++j) {
                            const auto& event = history[j];
                            std::cout << event.hit << ' ' << event.horizon << ' ' << event.increment
                                      << ' ' << event.excess << ' ' << event.balance << '\n';
                        }
                        return 1;
                    }
                } else if (funded && balance > 0) {
                    assert(increment <= 630 && balance <= 29613);
                    if (growth_charge == 4) assert(increment <= 315 && balance <= 14810);
                    startup += balance;
                }
                if (funded && balance > 0) previous_positive[key] = history.size();
            }
            if (funded) assert(signed_sum <= startup + multiplier * first);
            if (long_prime) previous_phase[key] = history.size();
            history.push_back({hit, horizon, increment, excess, balance});
            index = hit;
            horizon = updated;
        }
        maximum_startup = std::max(maximum_startup, startup);
    }
    std::cout << "synthetic starts=" << starts << " paid demands=" << demands
              << " cutoff stops=" << cutoff_stops << " event-limit stops=" << event_limit_stops
              << " through=" << limit << '\n';
    if (funded) std::cout << "multiplier=" << multiplier << " maximum startup=" << maximum_startup << '\n';
    if (growth_charge != 2) std::cout << "growth charge=" << growth_charge << '\n';
}
