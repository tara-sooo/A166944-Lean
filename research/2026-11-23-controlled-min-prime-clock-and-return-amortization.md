# Twin-prime-first: controlled squarefree clocks, MIN-prime renewal, and attempted amortization

Date 2026-11-23 JST. Scope: `tara-sooo/A166944-Lean`, Issue #3 with Issue #4 / parent #1 cross-reference. Main branch unchanged. Full twin-prime infinitude and A166944 remain OPEN. The symbolic reductions below are paper arguments, small-state bounds/diagnostics are complete integer computation, and the **new** LOW7-MIN table and insertion argument are NOT yet Lean-kernel checked. The ORIGINAL LOW7 PRODUCT 22,050-state time56/growth106 module was separately kernel-checked in draft PR #5.

## 1. First attempt — CRT trace saturation reveals a loss of information

For each actual PRODUCT event, record the full signed increment prefix word and P(w), the product of its distinct prime factors. The previous SOURCE-CRT argument proves that each fixed prefix word is realized by at most floor((X/2−1)/P(w))+1 odd starts. In particular P(w)>X/2 already uniquely determines M. `prime_clock_crt_saturation.cpp` records the FIRST such saturation index and categorizes repeated **minimum high owners** (prime >=11) before/after it.

| X | original high-owner R7 | after P(w)>X/2 | fraction after | mean saturation event index (among saturated sources) |
|---:|---:|---:|---:|---:|
| 4096 | 2015 | 1980 | 98.263% | 5.817 |
| 16384 | 17402 | 17124 | 98.402% | 6.616 |
| 65536 | 83606 | 81382 | 97.340% | 7.531 |
| 262144 | 496800 | 483611 | 97.345% | 8.441 |

Thus the +1 term in full-prefix CRT cylinders is not just a minor technical annoyance: the source is uniquely determined *before* almost all repeat-owner events in these samples. More CRT constraints on each further FULL prefix do not lower its weight below 1; a weighted bound requires control of the **number of admissible suffixes** or a dynamical renewal potential. This does not refute a carefully organized trace/expansion estimate, only the idea that longer CRT words alone force the sum to vanish.

## 2. Second attempt — bound owner repeats by first-time owners

For each canonical PRODUCT trajectory, let F7(M) count distinct minimum high owners q>=11 and R7(M) count high events beyond each owner's first event. The following OPEN statement is very strong and immediately sufficient:

    for all large dyadic X, all canonical odd M in [X,2X):
           R7(M) <= C * F7(M)         (constant C independent of X).

Proof of sufficiency: sum F7(M) <= (X/2) pi(B)=O(XB/log B), whence R7(X)=O(XB/log B)=o(XB). The already established LOW7 block argument then gives infinitely many twins. An aggregate version Σ_M R7(M)<=CΣ_M F7(M) is enough; pointwise is stronger than needed.

Actual exhaustive canonical original GCD diagnostics (`prime_clock_owner_ratio.cpp`):

| X | F7 total | R7 total | max_M R7(M)/F7(M) |
|---:|---:|---:|---:|
| 4096 | 7460 | 2015 | 1.11111 |
| 16384 | 38241 | 17402 | 1.77778 |
| 65536 | 190640 | 83606 | 1.86667 |
| 262144 | 943843 | 496800 | 2.60870 |
| 524288 | 1965708 | 1060127 | 2.33333 |
| 1048576 | 4268290 | 2362723 | 2.60714 |

All tested canonical sources satisfy R7<3F7, but this is NOT evidence of a universal constant 3 proof. `prime_clock_owner_ratio_adversarial.cpp` searched arbitrary CRT initial states and found B97 (24 primes), F7=10 and R7=46 (ratio 4.6), 155 nonunit events. `prime_clock_multitrack_literal.py` INDEPENDENTLY reconstructed this in BIG-INTEGER parity-specific gcd arithmetic from an explicit CRT even integer C, choosing a time representative with C<=2t. The arbitrary state does **not** have canonical initial form C=2t−6; thus it falsifies the naive all-state R<=3F extension, not the canonical conjecture.

### Fresh/stale owner's first-event charge

For each owner-q repeat interval (last owner-q event, current owner-q event), ask whether any first **minimum high owner** event occurred strictly inside. Assign fresh intervals to the LATEST such first event; leave others stale. This is a deterministic classification. (`prime_clock_fresh_charge.cpp`)

| X | fresh-owner intervals | stale intervals | largest charge per single first-owner event |
|---:|---:|---:|---:|
| 4096 | 1699 | 316 | 6 |
| 16384 | 14136 | 3266 | 7 |
| 65536 | 72537 | 11069 | 8 |
| 262144 | 432175 | 64625 | 10 |
| 524288 | 914342 | 145785 | 12 |

This test does NOT give a uniform per-event charge bound: the observed peak increases. A source-averaged bound on charges together with a bound on stale closed-label excursions would suffice. Individual q-return intervals overlap, so naive injective charging is false. These are deterministic exact enumeration counts, not a probabilistic transport theorem.

## 3. Third attempt — a dual divisibility height

After any nonunit event at time n with even new state C', define h'=2n−C'>=0. If the selected increment is an odd squarefree divisor e>1 of the clipped event product d, then

    n EVEN: e | h',
    n ODD:  e | (h'−6).                    (DUAL-HEIGHT)

Proof: every p|e divides n and C_pre−1 in the even case; C'=C_pre+e−1 gives 2n−C' ≡0 modp. In the odd case p divides n−2 and C_pre+1; hence 2n−C'≡6 modp. Squarefreeness gives divisibility by their product e. This formula is the earlier TIME-GAIN congruence expressed in the post-event height coordinate — it is a useful representation, **not an additional independent congruence constraint**.

For original PRODUCT at X262144: of 4,082,904 events, 306,025 finish at h=0, 652,929 at h=6, and 3,574,763 (87.56%) have h<B. The maximum h is 6480 while B=1355. At X1048576, max h=17138 vs B=2710; the ratio grows, so an unqualified constant multiple h<=5B is false in these finite canonical scans. A divisor-graph/height-dependent potential may be easier than the full C-state graph, but rare large-h excursions and h=0/6 resets must be handled. The audited C++ `prime_clock_dual_fresh_audit.cpp` asserts DUAL-HEIGHT at every event, and an independent literal oracle checks the small samples.

## 4. Fourth and most productive attempt — change the wheel's update rule

The ORIGINAL event clock uses the full clipped product d of tied odd prime factors and changes C to C+d−1. We can instead select ANY nonunit squarefree divisor e|d, including a SINGLE prime, and set C'=C+e−1. Select the next event at the first genuine nonunit clipped clock; the choice is made only at that event. Then:

1. Invariant 2M−2<=C<=2n survives. Relative to the *same pre-event state*, the original product update had C+d−1<=2n and e<=d.
2. Any selected p|e was an active clock at the preceding plateau, so its elapsed gap g<=2p<=3(p−1)<=3(e−1). Consequently the full last-event travel still obeys S−s<=3G, where G=Σ_events(e−1).
3. If after the final event the plateau K−S>=2B, then C±1 are BOTH prime, by the unchanged least-prime-factor and 2p-clock argument. The choice of update does not weaken this terminal certificate.
4. Therefore the exact conditional sufficiency `liminf_(dyadic X) [Σ_M G_policy(M)]/X² < 3/16` still yields infinitely many twin prime pairs, for ANY fixed deterministic or source-dependent admissible policy. Its premise is OPEN.

Five concrete policies were compared in `prime_clock_policy_lookahead.cpp`:

- PRODUCT: e=d (original).
- MIN: e is the smallest prime factor of d.
- MAX: e is the largest prime factor of d.
- MIN_ACTIVE: among every nonunit squarefree divisor e|d, choose the resulting C' with the fewest active primes <=B (ties to smallest e).
- MAX_WAIT: among those e, maximize the time to the next prime clock or the cutoff K (ties to smallest e).

**Important accounting distinction:** for controlled policies, a high prime q may be in the FULL tied d but NOT in selected e. A high `raw factor` is not necessarily a *selected* high event. Track both separately. The table below gives totals of selected high-owner *repeats* (min high factor of SELECTED e), not raw-incidence returns, together with mean selected growth.

| X=262144, B=1355 | mean G | selected high-owner F | selected high-owner R | terminal twin-producing sources |
|---|---:|---:|---:|---:|
| PRODUCT | 1059.75 | 943843 | 496800 | 131072 / 131072 |
| MIN | 943.246 | 912432 | 425129 | 131072 / 131072 |
| MAX | 949.183 | 938047 | 481688 | 131072 / 131072 |
| MIN_ACTIVE | 921.438 | 898156 | 416806 | 131072 / 131072 |
| MAX_WAIT | 946.307 | 903426 | 419329 | 131072 / 131072 |

MIN_ACTIVE reduces total selected high-owner repeats about 16.1% and mean growth about 13.1% versus PRODUCT, **only on this finite X**. In the small X256 interval the MIN policy yields five bad terminal sources, versus one for PRODUCT, so no pointwise or windowwise domination is claimed. Strict C++17 `-O3 -Wall -Wextra -Werror` runs and completely independent n-by-n Python `prime_clock_policy_greedy_literal.py` at X256,512,1024 agree in counts and final primality checks.

## 5. Stronger low-prime base and a universal one-high selected-prime lemma for MIN

Exhaustive 22,050-state event graph, with all 18,900 nonterminal states:

| LOW7 deterministic policy | max full travel | max entire LOW7 growth | max events |
|---|---:|---:|---:|
| PRODUCT | 56 | 106 | 9 |
| MIN | **56** | **34** | 9 |
| MAX | 62 | 34 | 10 |
| MIN_ACTIVE | 62 | 34 | 9 |
| MAX_WAIT (infinite horizon) | 62 | 40 | 9 |

`prime_clock_controlled_low7.py` exhaustively computes these values and independently solves the full CONTROLLED shortest-time Bellman graph allowing any divisor e|d. The controlled worst-case travel is still 56; local choice does NOT improve the worst LOW7 travel. These **new** policy numbers are finite-state computational theorems (not newly Lean checked).

For the **specific MIN policy**, the following general q-insertion argument is symbolic and uses only finite LOW7 MIN bounds L=56, G=34:

    For any prime q>=37, the {3,5,7,q} MIN wheel from ANY even state
      SELECTS q in at most one event, and
      total time to its last nonunit update <=2q+112.

Reason: A selected q event kills q activity (post C modq=0 or −2). Until the next selected q, every selected event is LOW7-only and (because MIN chooses the smallest tied prime) it follows a prefix of the LOW7 MIN orbit, including the cases where q is tied with a smaller prime but not selected. Such a block gains at most 34; re-selecting q needs >=q−1>=36. Hence impossible. Before/after the sole q selection are each low-only intervals of elapsed time <=56, and the q calendar gives at most a 2q waiting gap. The statement is about **q being selected**, not mere q being a factor of the full tied raw d.

Crucially, MIN's low-only block transitions are literally independent of unselected high-prime ties. The MIN_ACTIVE and MAX_WAIT controls can react to a high tied prime even if they select a low increment, so their 62/34/40 isolated-LOW7 bounds do NOT automatically transfer to low-only segments inside the FULL B-wheel.

### Every MIN high-donor word is now LINEAR, no exceptions

Two consecutive selected high-q events in a full MIN wheel, with m intervening high selected-prime events r_1,...,r_m and low-only growth L, satisfy

    E=Σ_{j=1}^m (r_j−1)+L,
    0<=L<=34(m+1), L even,
    q | [Σ_j r_j + L − m − c], c∈{−1,+1,+3}.       (MIN-LINEAR)

There are **NO donor coefficients a_j|105**, and NO nonlinear high-composite donor cases — every update is a single prime. If r occurs exactly once, its coefficient mod q is 1, so it pins r to ONE residue modulo q. More generally, if the coefficient of EVERY distinct r vanishes modq, then each r appeared at least q times, whence **m>=q**, a much stronger rank-zero barrier than the previous m>=q/105. For q>=37, m=0 cannot occur.

For m=1 and q>(B+68)/2, the congruence forces q=r+L−(1+c), and therefore −4<=q−r<=68. This is a bounded even prime difference suitable for a standard TWO-linear-form upper-bound sieve at the level of DISTINCT q,r labels, but source-weighted multiplicity and m>=2 remain OPEN. In the actual MIN source scans, the narrow top-band m=1 class was empty for the sampled larger X. It cannot by itself control all returns.

Exact original-GCD **MIN-selected** donor decomposition (`prime_clock_min_donor_audit.cpp`):

| X | selected high q repeats R | m=0 | m=1 | m=2 | m>=3 |
|---:|---:|---:|---:|---:|---:|
| 4096 | 2174 | 119 | 666 | 381 | 1008 |
| 16384 | 12840 | 563 | 2844 | 2821 | 6612 |
| 65536 | 74022 | 2917 | 16136 | 12612 | 42357 |
| 262144 | 425129 | 16070 | 70737 | 64324 | 273998 |

Every class in this table satisfied MIN-LINEAR and the LOW7<=34(m+1) check; no q>=37 rehit with m=0. Independent n-by-n `prime_clock_min_donor_literal.py` matched the full X256,512,1024 counts, including the parity-sensitive c.

## 6. Tried-and-rejected single-prime potential

The simplest hope V(t,C)=Σ_{p<=B}f_p(t mod2p,C/2 modp), with Bellman `V(before) >= g+V(after)`, would yield an O(Σp) stopping budget if each f_p were O(p). The prior PRODUCT LOW7 is rigorously refuted by an integer 133-edge projected circulation (separately archived). We set up the exact LOW7 LP for fixed controlled policies using `scipy.optimize.linprog` on 18,900 transition inequalities and 166 p-local variables (`prime_clock_singleton_lp.py`): PRODUCT, MIN, MAX, MIN_ACTIVE, MAX_WAIT all numerically returned INFEASIBLE. The MIN result is solver evidence, not an exact integer dual certificate; the previously kernel-checked original PRODUCT graph remains unaffected. Simple weighted per-prime next-clock or active-flag potentials also have thousands of directly checkable transition failures under arbitrary divisor choices. Interacting pairwise or multi-prime terms remain necessary for these fixed policies, or a more subtle disjunctive adaptive controller must be invented.

## 7. Literature bridges and next exact open theorem

- Helfgott–Radziwill, *Expansion, divisibility and parity*, https://arxiv.org/abs/2103.06853 ; Helfgott's primary exposition https://webusers.imj-prg.fr/~harald.helfgott/Expansion_1.html . Their distinct/repeated prime-label trace technique and graph norm inequalities are genuine inspiration, **not** a theorem on the source-selected moving clock. The MINI-POLICY `Σr_j` (unit coefficients) is algebraically closer to a prime-walk trace than the PRODUCT donor `Σa_jr_j` plus composite exceptions, but the long-word source-conditioned trace estimate is STILL OPEN, and their original prime range restriction is much shorter than B~sqrt X.
- *Weighted sieves with switching*, Math. Proc. Camb. Philos. Soc. 179 (2025), https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C . This uses Chen-style switching to vary which variable is sieved. Our ability to select a tied prime factor is an algorithmic control freedom, **not** a direct application of Chen switching or a solution to the sieve parity problem.
- The previous CRT word note `research/2026-11-23-donor-word-crt-trace-and-fresh-label-rank.md` gives exact SOURCE-CRT and time-gain congruences. §1 above explains their finite experimental saturation limit; §5 gives a strictly simpler NEW selected-prime donor word.

**Most promising concrete next proof task:** Work with MIN-prime update, not PRODUCT. Prove a source-weighted trace/renewal inequality for *linear unit-coefficient* high donor words, perhaps the aggregate owner amortization

    sum_M R7^MIN(M) <= C sum_M F7^MIN(M)        (constant C),

or any liminf_(X) R7^MIN(X)/(XB)<9/224. The unchanged LOW7 MIN travel L=56 and unchanged terminal certificate immediately yield infinitely many twin primes. A proof would need to handle the m>=2 donor words dominating actual repeats. The `m>=q` rank-zero barrier is potentially useful: all shorter donor words have at least one honest mod-q rank. The accompanying code and independent literal oracles verify finite ranges only. The new asymptotic bound and twin-prime theorem remain OPEN.

## 8. Replay commands

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_crt_saturation.cpp -o /tmp/clock_sat
/tmp/clock_sat 4096 16384 65536 262144

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_owner_ratio.cpp -o /tmp/owner_ratio
/tmp/owner_ratio 4096 16384 65536 262144 524288 1048576

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_owner_ratio_adversarial.cpp -o /tmp/owner_stress
/tmp/owner_stress 97 18000

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_dual_fresh_audit.cpp -o /tmp/dual
/tmp/dual 4096 16384 65536 262144 1048576

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_policy_lookahead.cpp -o /tmp/policies
/tmp/policies 256 1024 4096 16384 65536 262144

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_min_donor_audit.cpp -o /tmp/min_donors
/tmp/min_donors 256 512 1024 4096 16384 65536 262144

python3 research/prime_clock_multitrack_literal.py
python3 research/prime_clock_policy_greedy_literal.py
python3 research/prime_clock_min_donor_literal.py
python3 research/prime_clock_controlled_low7.py
OPENBLAS_NUM_THREADS=1 python3 research/prime_clock_singleton_lp.py
```

All tested compiler invocations used strict `-Wall -Wextra -Werror` flags. The Python literal oracles make independent per-integer gcd decisions on X256/512/1024 and verify the arbitrary-state CRT witness. No fresh Lean compilation was performed and `main` was not changed.