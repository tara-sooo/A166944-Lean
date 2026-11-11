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
    bool reused_long_prime;
    int net_cost;
};

struct PrimeReuseWindow {
    int left;
    int right;
    int increment;
    int cost;
};

struct ReuseOverlapStats {
    static constexpr int64_t scale = 1000000;
    int64_t windows = 0, overlapping_pairs = 0, crossings = 0, distinct_equal_width = 0;
    int64_t short_pairs = 0, overloaded_starts = 0;
    int64_t minimum_pair_margin = INT64_MAX, maximum_load = 0;
    int pair_record = 0, pair_horizon = 0, load_record = 0, load_horizon = 0, maximum_depth = 0;
    int64_t components = 0, short_signed_components = 0, short_reuse_components = 0;
    int64_t minimum_signed_component = INT64_MAX, minimum_reuse_component = INT64_MAX;
    int component_record = 0, component_horizon = 0;
    int64_t prefix_component_checks = 0, short_two_thirds = 0, minimum_two_thirds = INT64_MAX;
    int two_thirds_record = 0, two_thirds_horizon = 0, two_thirds_prefix = 0;
    int64_t remainder_checks = 0, maximum_triple_remainder = 0;
    int remainder_record = 0, remainder_hit = 0;

    void observe(int record, const std::vector<PrimeReuseWindow>& entries, const std::vector<Event>& history) {
        windows += entries.size();
        std::vector<std::pair<int, int64_t>> changes;
        for (size_t i = 0; i < entries.size(); ++i) {
            const auto& current = entries[i];
            const int width = current.right - current.left;
            const int64_t rate = (2 * scale * current.cost + width - 1) / width;
            changes.emplace_back(current.left, rate);
            changes.emplace_back(current.right, -rate);
            for (size_t j = 0; j < i; ++j) {
                const auto& earlier = entries[j];
                if (current.left >= earlier.right) continue;
                ++overlapping_pairs;
                crossings += earlier.left < current.left;
                const int64_t margin = current.right - std::min(earlier.left, current.left) -
                    2LL * (earlier.cost + current.cost);
                if (std::max(earlier.increment, current.increment) >= 86) assert(margin >= 0);
                if (width == earlier.right - earlier.left && current.increment != earlier.increment) {
                    ++distinct_equal_width;
                    assert(width % (210LL * earlier.increment * current.increment) == 0);
                    assert(margin >= 0);
                }
                short_pairs += margin < 0;
                if (margin < minimum_pair_margin) {
                    minimum_pair_margin = margin;
                    pair_record = record;
                    pair_horizon = current.right;
                }
            }
        }
        // Negative changes sort before positive ones at a shared endpoint.
        std::sort(changes.begin(), changes.end());
        int64_t load = 0;
        int depth = 0;
        bool overloaded = false;
        for (const auto& change : changes) {
            load += change.second;
            depth += change.second > 0 ? 1 : -1;
            maximum_depth = std::max(maximum_depth, depth);
            overloaded |= load > scale;
            if (load > maximum_load) {
                maximum_load = load;
                load_record = record;
                load_horizon = change.first;
            }
        }
        assert(load == 0 && depth == 0);
        overloaded_starts += overloaded;

        int64_t net = 0, covered = 0;
        size_t count = 0;
        if (record >= 50000000) ++remainder_checks;
        for (const auto& event : history) {
            net += event.net_cost;
            if (count < entries.size() && entries[count].right == event.horizon) {
                ++count;
                covered = observe_components(record, entries, history, count);
            }
            if (record >= 50000000) {
                ++remainder_checks;
                const int64_t remainder = 3 * (net - covered);
                if (remainder > maximum_triple_remainder) {
                    maximum_triple_remainder = remainder;
                    remainder_record = record;
                    remainder_hit = event.hit;
                }
            }
        }
        assert(count == entries.size());
    }

    int64_t observe_components(int record, const std::vector<PrimeReuseWindow>& entries,
                              const std::vector<Event>& history, size_t count) {
        std::vector<PrimeReuseWindow> ordered(entries.begin(), entries.begin() + count);
        std::sort(ordered.begin(), ordered.end(), [](const auto& a, const auto& b) { return a.left < b.left; });
        int64_t covered = 0;
        for (size_t i = 0; i < ordered.size();) {
            const int left = ordered[i].left;
            int right = ordered[i].right;
            int64_t charges = ordered[i].cost;
            for (++i; i < ordered.size() && ordered[i].left < right; ++i) {
                right = std::max(right, ordered[i].right);
                charges += ordered[i].cost;
            }
            int64_t signed_cost = 0, negative = 0;
            auto start = std::upper_bound(history.begin(), history.end(), left,
                [](int horizon, const Event& event) { return horizon < event.horizon; });
            for (auto it = start; it != history.end() && it->horizon <= right; ++it) {
                signed_cost += it->net_cost;
                negative += std::min(it->net_cost, 0);
            }
            const int64_t signed_margin = right - left - 2 * signed_cost;
            const int64_t reuse_margin = right - left - 2 * (charges + negative);
            covered += charges + negative;
            const int64_t two_thirds_margin = 2LL * (right - left) - 3 * (charges + negative);
            ++prefix_component_checks;
            short_two_thirds += two_thirds_margin < 0;
            if (two_thirds_margin < minimum_two_thirds) {
                minimum_two_thirds = two_thirds_margin;
                two_thirds_record = record;
                two_thirds_horizon = right;
                two_thirds_prefix = entries[count - 1].right;
            }
            if (count != entries.size()) continue;
            ++components;
            short_signed_components += signed_margin < 0;
            short_reuse_components += reuse_margin < 0;
            minimum_signed_component = std::min(minimum_signed_component, signed_margin);
            if (reuse_margin < minimum_reuse_component) {
                minimum_reuse_component = reuse_margin;
                component_record = record;
                component_horizon = right;
            }
        }
        return covered;
    }

    void print() const {
        std::cout << "positive prime reuse windows=" << windows << " overlapping pairs=" << overlapping_pairs
                  << " crossings=" << crossings << " distinct equal widths=" << distinct_equal_width
                  << " negative pair margins=" << short_pairs << '\n';
        if (overlapping_pairs) {
            std::cout << "minimum overlap pair margin=" << minimum_pair_margin << " record=" << pair_record
                      << " horizon=" << pair_horizon << '\n';
        }
        if (windows) {
            std::cout << "maximum reuse load=" << maximum_load << " scale=" << scale << " record=" << load_record
                      << " horizon=" << load_horizon << " maximum depth=" << maximum_depth
                      << " overloaded starts=" << overloaded_starts << '\n';
            std::cout << "reuse components=" << components << " negative signed margins=" << short_signed_components
                      << " minimum signed component margin=" << minimum_signed_component
                      << " negative reuse margins=" << short_reuse_components << '\n';
            std::cout << "minimum reuse component margin=" << minimum_reuse_component << " record="
                      << component_record << " horizon=" << component_horizon << '\n';
            std::cout << "prefix component checks=" << prefix_component_checks
                      << " negative two-thirds margins=" << short_two_thirds << '\n';
            std::cout << "minimum two-thirds margin=" << minimum_two_thirds << " record=" << two_thirds_record
                      << " horizon=" << two_thirds_horizon << " prefix=" << two_thirds_prefix << '\n';
        }
        if (remainder_checks) {
            std::cout << "remainder checks=" << remainder_checks << " maximum triple remainder="
                      << maximum_triple_remainder << " record=" << remainder_record << " hit=" << remainder_hit << '\n';
        }
    }
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
    const bool check_half_reserve = argc == 5 && std::string(argv[4]) == "--residual-reserve";
    const bool residual = argc == 5 && (std::string(argv[4]) == "--residual" || check_half_reserve);
    const bool funded = (argc == 4 || argc == 5 || argc == 6) && std::string(argv[2]) == "--funded";
    if ((argc != 2 && !funded) || (argc == 5 && !residual) ||
        (argc == 6 && std::string(argv[4]) != "--growth-charge")) {
        std::cerr << "Usage: travel_credit_search LIMIT [--funded MULTIPLIER [--growth-charge 2|4 | --residual | --residual-reserve]] | --table\n";
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
    int64_t reserve_checks = 0, minimum_reserve_margin = INT64_MAX;
    int reserve_record = 0, reserve_hit = 0;
    int64_t minimum_signed_margin = INT64_MAX;
    int signed_record = 0, signed_hit = 0;
    int one_middle = 0, reused_middle = 0;
    int minimum_middle_margin = INT32_MAX, middle_record = 0, middle_hit = 0;
    ReuseOverlapStats reuse_overlap;
    for (int record = 13; record <= limit; record += 6) {
        if (!is_prime(record) || !is_prime(record - 2)) continue;
        ++starts;
        int index = record + 2, horizon = 2 * record - 2;
        std::unordered_map<int64_t, int> previous_phase;
        std::unordered_map<int64_t, int> previous_positive;
        std::vector<Event> history;
        std::vector<std::pair<int, int>> credits;
        std::vector<PrimeReuseWindow> reuse_windows;
        int64_t first = 0, startup = 0, signed_sum = 0;
        int64_t unused_credit = 0;
        auto reserve_ok = [&](int hit) {
            if (!check_half_reserve || record < 50000000) return true;
            ++reserve_checks;
            const int64_t margin = record + 2 * unused_credit - 2 * (24 + multiplier) * first;
            if (margin < minimum_reserve_margin) {
                minimum_reserve_margin = margin;
                reserve_record = record;
                reserve_hit = hit;
            }
            const int64_t signed_margin = record - 2 * (24 * first + signed_sum);
            if (signed_margin < minimum_signed_margin) {
                minimum_signed_margin = signed_margin;
                signed_record = record;
                signed_hit = hit;
            }
            if (margin < 0) {
                std::cout << "Half-reserve failure record=" << record << " hit=" << hit
                          << " margin=" << margin << '\n';
                return false;
            }
            return true;
        };
        if (!reserve_ok(index)) return 1;
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
            const int balance = residual ?
                (long_prime && previous < 0 ? 0 : 24 * gap) + value(hit, updated) -
                    value(index, horizon) - 11 * (increment - 1) :
                excess + value(hit, updated) - value(index, horizon) - growth_charge * (increment - 1);
            const auto positive_found = previous_positive.find(key);
            const int prior_positive = positive_found != previous_positive.end() ? positive_found->second : -1;
            const int anchor = previous >= 0 ? previous : prior_positive;
            if (long_prime && previous < 0) {
                first += gap;
                if (funded) {
                    credits.emplace_back(2 * history.size() + 1, multiplier * gap);
                    unused_credit += multiplier * gap;
                }
            }
            if (210 % increment) {
                signed_sum += balance;
                if (check_half_reserve && previous >= 0 && balance > 0) {
                    const auto& old = history[previous];
                    assert((hit - old.hit) % (2 * increment) == 0);
                    assert((horizon - old.horizon) % (210LL * increment) == 0);
                    reuse_windows.push_back({old.horizon, horizon, increment, balance});
                }
                if (balance < 0) {
                    credits.emplace_back(2 * history.size(), -balance);
                    unused_credit -= balance;
                } else if (balance > 0 && anchor >= 0) {
                    ++demands;
                    if (check_half_reserve && int(history.size()) == anchor + 2) {
                        const auto& middle = history[anchor + 1];
                        assert(middle.increment >= 463);
                        ++one_middle;
                        reused_middle += middle.reused_long_prime;
                        const int margin = std::max(0, -middle.balance) - balance;
                        if (!middle.reused_long_prime) assert(margin >= 0);
                        if (margin < minimum_middle_margin) {
                            minimum_middle_margin = margin;
                            middle_record = record;
                            middle_hit = hit;
                        }
                    }
                    int owed = balance;
                    for (auto& credit : credits) {
                        if (credit.first <= 2 * anchor) continue;
                        const int used = std::min(owed, credit.second);
                        owed -= used;
                        credit.second -= used;
                        unused_credit -= used;
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
                    if (residual) assert(increment <= 169 && balance <= 1478);
                    startup += balance;
                }
                if (funded && balance > 0) previous_positive[key] = history.size();
            }
            if (funded) {
                assert(signed_sum + unused_credit == startup + multiplier * first);
                assert(unused_credit >= 0);
            }
            if (!reserve_ok(hit)) return 1;
            if (long_prime) previous_phase[key] = history.size();
            const int first_gap_cost = long_prime && previous < 0 ? 24 * gap : 0;
            const int net_cost = first_gap_cost + (210 % increment ? balance : 0);
            history.push_back({hit, horizon, increment, excess, balance, previous >= 0, net_cost});
            index = hit;
            horizon = updated;
        }
        maximum_startup = std::max(maximum_startup, startup);
        if (check_half_reserve) reuse_overlap.observe(record, reuse_windows, history);
    }
    std::cout << "synthetic starts=" << starts << " paid demands=" << demands
              << " cutoff stops=" << cutoff_stops << " event-limit stops=" << event_limit_stops
              << " through=" << limit << '\n';
    if (funded) std::cout << "multiplier=" << multiplier << " maximum startup=" << maximum_startup << '\n';
    if (growth_charge != 2) std::cout << "growth charge=" << growth_charge << '\n';
    if (residual) std::cout << "balance=residual\n";
    if (check_half_reserve && reserve_checks) {
        std::cout << "half-reserve checks=" << reserve_checks << " minimum margin=" << minimum_reserve_margin
                  << " record=" << reserve_record << " hit=" << reserve_hit << '\n';
        std::cout << "minimum signed margin=" << minimum_signed_margin << " record=" << signed_record
                  << " hit=" << signed_hit << '\n';
    }
    if (check_half_reserve) {
        std::cout << "one-middle requests=" << one_middle << " reused long-prime middles=" << reused_middle << '\n';
        if (one_middle) {
            std::cout << "minimum one-middle margin=" << minimum_middle_margin << " record=" << middle_record
                      << " hit=" << middle_hit << '\n';
        }
        reuse_overlap.print();
    }
}
