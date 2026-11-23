# Twin-prime-first: upper-band q-return donor diversity and coalesced source fibres

2026-11-23 JST, Issue #3 and #4. This is a **direct investigation of the outstanding source-weighted return estimate** behind the LOW7 twin-prime sufficient condition. The conclusion is a rigorous (paper-level) two-prime alphabet lemma, a coalescent episode identity, and exact original-GCD finite diagnostics. **The needed asymptotic return bound, infinitely many twin primes, and the A166944 conjecture remain unproved.** The new paper-level lemma was not submitted to Lean; the separate LOW7 finite certificate in draft PR #5 was previously accepted by the Lean kernel in GitHub Actions.

## 1. Genuine elementary lemma: a two-prime clipped wheel has at most three events

Let the squarefree parity-GCD wheel use precisely two **distinct** odd prime factors `5 <= p < q` (no 3/5/7 or other primes) and start at an arbitrary even plateau C and arbitrary clock time. A firing of p leaves C modulo p equal to 0 (even clock) or -2 (odd clock), neither of which is +1 or -1 modulo p since p>=5. Thus **p cannot fire twice without an intervening q event**. The same holds interchanging p and q.

After **any** q-bearing event, q is inactive. Before a possible second q-bearing event, only p may fire; moreover p can fire **at most once** since q is not firing between the two q events. That p event adds p-1<q-1 to C. An even q hit requires at least q-1 non-q growth to recharge its clock, while an odd q hit requires at least q+1. Hence **q cannot fire twice**. The entire event list consists of at most one q event and at most one p event on either side, i.e. **at most three nonunit events**. If p and q fire together as a pq event, both are deactivated and the trajectory stops immediately. This bound is independent of the magnitudes of p and q.

For the special case p=3 the same proof is false because after an odd 3 hit, C=-2 ≡1 (mod3) can immediately activate the even 3 clock. An actual q return within the full `{3,5,7,...,B}` wheel may use low-prime donations and/or many distinct high primes; the two-prime lemma alone does not bound full-wheel returns.

This lemma is reproducibly cross-checked by finite-state enumeration (e.g. the 2*p*q dimensional time/residue automaton for 5/7, 5/11, 7/11, 11/13): maximal actual nonunit event count is three for these pairs. The inequality above is a direct symbolic proof for **all** 5<=p<q, not a finite extrapolation.

## 2. Exact source-coalescence identity for top-band returns

Let X be dyadic and B=ceil(sqrt(7X)), and J={prime q: B/2<=q<=B}. For every odd M in [X,2X), follow the **original exact** squarefree parity-GCD wheel to K=floor((7M-1)/4). At each q-bearing event for q in J, retain its event time t and the **post-event even state** C; if q fires again at t'>t, define the episode key

    e = (q,t,C,t').

For each key let w_e count how many distinct original starts M produce this SAME adjacent-in-q event pair. The exact identity is

    R_J(X) = sum_{e} w_e,

where R_J counts source-tagged q returns, with no assumption of independence or uniform distribution. Because the update only depends on the current (t,C), common cutoff B and parity-specific clock, **all sources that meet at the same (t,C) subsequently follow the same event trajectory** until the minimum of their K cutoffs. The common second q hit at t' is therefore one coalesced episode counted with source weight w_e, not w_e independent mixing trials.

There is an exact fibre energy inequality. For an episode e, list its w_e odd start values M_1<...<M_k. At its first q event, post state C is common. Partial growth since each start is G_i=C-(2M_i-2)>=0. As consecutive odd starts differ by >=2, G_i-G_(i+1)>=4, and hence

    sum_{i=1..k} G_i >= 2*k*(k-1) = 4*binom(k,2).

Since growth is nondecreasing after this event, the same lower bound holds with **terminal** growth G_B(M_i) in place of G_i. This is an *episode-local* specialization of the previously established terminal-fibre collision budget; it is not a bound on the total R_J until the total charged growth/episode multiplicity is itself controlled. In particular, for each e,

    4*binom(w_e,2) <= sum_{M in fibre(e)} G_B(M).

## 3. Independent exact data: source incidences versus coalesced episode classes

The strict C++17 auditor `research/twin_prime_topband_donor_diversity.cpp` uses original frozen-state first-hit GCD clocks. Each q incidence is counted even if q is not the smallest prime factor of d; an intervening donor means a non-q event bearing >=11. The donor **diversity** is the number of *distinct* high prime factors among all such intervening events, not the number of donor events. The identical small-X results from a separate Python per-integer implementation are below.

| X | q>=B/2 q-incidences | first q occurrences | source-weighted returns R_J | distinct episode keys | max episode fibre w_e | minimum different donor primes (when returns exist) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 90 | 79 | 11 | 2 | 7 | 1 |
| 512 | 149 | 149 | 0 | 0 | 0 | -- |
| 1024 | 155 | 152 | 3 | 2 | 2 | 1 |
| 2048 | 356 | 332 | 24 | 1 | 24 | 2 |
| 4096 | 582 | 571 | 11 | 1 | 11 | >=4 |
| 8192 | 1500 | 1498 | 2 | 1 | 2 | >=4 |
| 16384 | 2147 | 2139 | 8 | 1 | 8 | >=4 |
| 32768 | 4049 | 3962 | 87 | 2 | 86 | 3 |
| 65536 | 8585 | 8585 | 0 | 0 | 0 | -- |
| 131072 | 13890 | 13890 | 0 | 0 | 0 | -- |
| 262144 | 29749 | 29749 | 0 | 0 | 0 | -- |
| 524288 | 44798 | 44767 | 31 | 1 | 31 | >=4 |
| 1048576 | 99276 | 99271 | 5 | 2 | 4 | >=4 |

**Concrete coalescence witness** at X=524288 (B=1916): all 31 returned top-band source incidences derive from ONE key with q=1201, t=1035262 and t'=1036465. The intervening 7 high donor primes were `{11,13,17,47,109,269,709}` (seven different primes). For instance M=1033293 and M=1033295 are distinct source starts that have merged into exactly the same post-q state. At X32768, 86 of 87 returns share the key with q=421, t=50520 and t'=50943, through high donors `{11,13,17,23,41,53,79,127}`; one more return belongs to a distinct key.

Crucial lesson for the existing q-deleted phase-set `A_q(v)` and discrepancy `D_J`: successive source starts are not distinct samples once they have coalesced. One q-clock phase can be weighted 31 or 86 times in the original source ensemble. This is WHY an unweighted Fourier or distinct prime-pair count cannot be substituted for the source-weighted analytic estimate.

## 4. The exact unfinished target

The earlier paper reduction using Lean-verified LOW7 finite state certificate shows it is sufficient to prove

    liminf_(dyadic X) R7(X)/(X*B) < 9/224,

where R7 uses the minimum high-prime event owner, not all q events. For the *top-band all-q* proxy here, a sufficient input for its individual negligible contribution is

    sum_{e in top-band episodes} w_e = o(X*B).

A possible different analytic route is to estimate the **number of distinct q-return episodes** AND the **source basin weights** together, using the quadratic fibre energy, rather than assuming that q tags are independent CRT phase draws. The current finite data suggest extreme coalescence, but do not supply a uniform bound on either quantity. Nor does a top-band result alone settle the lower q bands. This is a concrete open source-weighted transport problem, not a theorem on twin primes.

## 5. Replay and independent oracle

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_topband_donor_diversity.cpp -o /tmp/top_diversity
/tmp/top_diversity 256 512 1024 2048 4096 8192 16384 32768 65536 131072 262144 524288 1048576
python3 research/twin_prime_topband_donor_diversity_literal.py 256 512 1024
```

The C++ executable includes checked regression values for X2048/16384/65536/262144/524288/1048576. Independent Python exactly reproduces q-incidences, first hits, donor-diversity histogram, distinct episode count and maximal source fibre at X256/512/1024. An intermediate C++ debug version with incorrect negative-modulo handling was discarded; the final pinned source uses positive circular gaps and matches pre-existing top-band q-return audits and independent Python.

No GitHub `main` changes, no new kernel theorem and no claim of twin-prime infinitude.
