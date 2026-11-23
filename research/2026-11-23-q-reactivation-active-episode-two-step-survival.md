# A166944 Issue #4: dormant-prime activation balance, exact two-event survival, and large-increment bridges

Date: 2026-11-23 JST. Original parity-specific squarefree-clipped GCD research, dedicated branch `research/issue-4-terminal-survivor-positive-budget`; Issue #4 / parent #1. Follows [the full LOW23 reset slice and first-vs-repeat prime incidence note](2026-11-23-reset-slice-low23-and-first-vs-repeat-prime-budget.md). Mathematical propositions here follow directly from the clipped GCD update and elementary modular arithmetic; full-source data are finite C++17 scans with independent literal-step Python checks. The necessary asymptotic estimate remains OPEN. No twin-prime infinitude, A166944 strict-record theorem, or Lean kernel proof is claimed.

## Definitions

At even dyadic X, let B=ceil sqrt(7X), and let M run over odd canonical starts in [X,2X), with s=M+2, C(s)=2M−2, cutoff K(M)=floor((7M−1)/4). For each n>s:

    raw gcd at even n: gcd(n,C(n−1)−1),
    raw gcd at odd  n: gcd(n−2,C(n−1)+1),
    d_M(n)=gcd(raw gcd, L_B),
    C(n)=C(n−1)+d_M(n)−1,

where L_B is the product of distinct odd primes <=B. Nonunit events are d>1; all d are positive odd squarefree. Let Q_B be odd primes q∈[19,B]. A q-hit is a nonunit event with q|d. For each source and q, only FOLLOWING ITS FIRST q-HIT, track a binary active state `a_q(C)=1{q|(C−1)(C+1)}`.

Define H_X as the total #q-hits with multiplicity over sources, q; F_X as one FIRST hit per (source,q) with >=1 hit, R_X=H_X−F_X as all repeat q-hits. A_X^{act} is the number of **0→1** active changes at an event after q has first fired. L_X^{loss} is the number of **1→0** changes at an event with no q-hit, and D_X^{cut} is the number of previously hit q which remain active at their source's final K(M). Here “active” depends only on C, not on whether the next q clock rings before another event. `A_X^{act}` must NOT be confused with the earlier first-moment weighted q-incidence A_X=Σ_q qH_q in other research notes.

## 1. Exact activation conservation (PAPER)

Immediately after every q hit, q is inactive: from an even event its post-state C≡0 modq, from an odd event C≡−2 modq. Both are outside {±1} for q>=19. Each q active episode, after the very first q hit, begins at a non-q event which changes a_q from 0 to1 and ends in exactly one of: another q hit (a repeat), deactivation by a non-q event, or still being active at cutoff. Therefore, **for every original finite dyadic window**,

    BOXED: A_X^{act} = R_X + L_X^{loss} + D_X^{cut}.             (A1)

This is a deterministic event-ledger identity, including composite clipped increments, original source deadlines and full coalesced source multiplicity. Equivalently H_X−A_X^{act}=F_X−L_X^{loss}−D_X^{cut}. A positive asymptotic margin `H_X−A_X^{act} >> H_X/log B` along an unbounded dyadic subsequence is a sufficient (but stronger) version of the earlier F_X/H_X >> 1/logB criterion for infinitely many twins; neither statement is proved.

## 2. Exact odd-increment survival table and a TWO-EVENT lemma (PAPER)

Suppose q>=19 is active in a pre-event C (so C≡+1 or−1 modq), a non-q event fires with odd d>=3, and q is STILL active in C'=C+d−1. The FOUR possible side transitions imply:

| pre C mod q | post C' mod q | necessary exact congruence |
|---|---|---|
| +1 | +1 | q|(d−1) |
| +1 | −1 | q|(d+1) |
| −1 | +1 | q|(d−3) |
| −1 | −1 | q|(d−1) |

Thus always `q|(d−3)(d−1)(d+1)`. Since d is odd, all three factors are EVEN. If d>3, a nonzero even multiple of an ODD q is at least 2q, and consequently

    BOXED: q remains active across a non-q event ⇒
           [d=3 and pre C≡−1 (modq), post C'≡+1 (modq)]
           OR [d>=2q−1 and q|(d−3)(d−1)(d+1)].          (A2)

In particular **a second successive d=3 event cannot also preserve q activity**, unless there was an intervening event with d>=2q−1 which changed its active side again.

**Corollary, canonical active-episode trichotomy.** For EVERY repeated q-hit, locate its most recent 0→1 activation after the previous q-hit. Exactly one case occurs:

* **DIRECT**: the first subsequent nonunit event carries q;
* **THREE-FLIP**: the next nonunit event has d=3 and preserves q, and the event immediately after that carries q;
* **LARGE-BRIDGE**: some intervening non-q event while q remains active has clipped odd d>=2q−1. (There may have been other d=3 events separated by such a bridge.)

This trichotomy is EXACT; activation may itself come long after the previous q-hit, so it does not bound the entire dormant period. The stronger point is that the **final active spell** is local, except for a rigorously identified large-increment divisor event.

## 3. Exceptional large-bridge prime support (PAPER)

Let V_X be the number (over original sources and nonunit events) of triples (M,n,q) with q>=19 already seen, q not dividing current d>3, and q active in BOTH C_pre and C_post. Assign each LARGE-BRIDGE repeat episode to its FIRST such persistence. Distinct episodes of the same q cannot share the assigned time, so

    BOXED: R_X^{large} <= V_X
          <= sum_(M,n:d_M(n)>3) # {q∈Q_B:
                q|(C_pre²−1), q|[(d−3)(d−1)(d+1)] }
          <= sum_(M,n:d>3) omega_[19,B]((d−3)(d−1)(d+1)). (A3)

Here omega_[19,B] counts DISTINCT prime factors q in [19,B]. This condition requires simultaneous divisibility by an earlier GCD state and by one of three small shifts of the current increment. It is a specific arithmetic, source-weighted divisor-correlation estimate, rather than an assumption that two distant q-hit times are independent.

**Top-half q corollary:** if q>(B+1)/2 and q survives a non-q event with d>3, necessarily d>=2q−1>B. Thus, in the original clipped wheel, such a bridge cannot have a prime-only clipped increment (since every prime-only d<=B): it requires a **COMPOSITE clipped increment >B**. The q-hit itself need not be composite. In actual scans most d are prime-only, suggesting an attractive exceptional-case arithmetic bound; proving the required composite-event estimate asymptotically remains open.

## 4. Original clipped-GCD full-source data (INDEPENDENTLY TESTED FINITE ONLY)

The new C++17 `research/recharge_activation_audit.cpp` computes exact original parity-dependent squarefree-clipped GCD event jumps and factors both C±1 before and after every event. It checks (A1) at every X, (A2) at EVERY actual q activity-preserving non-q event, and trichotomy A3. It also checks old q-incidence H,F regression values and earlier high13/high17 counts and literal M7..119 growth. An independently coded Python `research/independent_activation_literal.py` advances **every integer n, not jump clocks**, for full original starts X256/512/1024/4096, and matches every H,F,R,A,L,cutoff and trichotomy count exactly. Separately, `research/return_overlap_audit.cpp` measures number of high>=19 events and low/high growth in intervals between consecutive q hits, also with full parity-specific GCD and old regressions.

| X | H total q>=19 | F first | R repeats | 0→1 activations A | lost activations L | DIRECT | THREE-FLIP | LARGE-BRIDGE |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 5391 | 4823 | 568 | 2340 | 1772 | 492 | 75 | 1 |
| 16384 | 31042 | 25450 | 5592 | 20632 | 15040 | 4277 | 1211 | 104 |
| 65536 | 160698 | 136058 | 24640 | 107161 | 82521 | 18828 | 5560 | 252 |
| 262144 | 868502 | 703647 | 164855 | 698125 | 533270 | 124907 | 39517 | 431 |
| 1048576 | 4031949 | 3248703 | 783246 | 3274416 | 2491170 | 598339 | 181727 | 3180 |
| 1999996 | 8564171 | 6757307 | 1806864 | 7539751 | 5732887 | 1363959 | 434986 | 7919 |

At all these original canonical windows, D_X^{cut}=0 (the original state at K was a full-wheel sink in the finite scans), so A=R+L. **The TWO local cases account for 99.594% of repeated q hits at X1048576 and 99.562% at X1999996.** The exceptional category is 0.406% and 0.438%, respectively. Actual large-persistence crossing events V_X were 14382 and38228, respectively, confirming R_large<=V. The ratio A/H increased from0.434 (X4096) to0.812 (X1048576) and0.880 (X1999996): a GLOBAL A/H<1 contraction is NOT proved; finite trend does not establish one.

**Dormant period versus active period:** `return_overlap_audit.cpp` finds among all X1048576 repeated q hits 72376 (9.2%) with NO other high>=19 event between consecutive q hits,122535 (15.6%) with exactly ONE,103203 (13.2%) with TWO, and485132 (61.9%) with THREE OR MORE. Average other high events interposed ≈5.19. Thus long between-q recharge histories are COMMON, even though the final 0→1 activation-to-q-hit period is almost always ≤2 events. The new local approach compresses the LAST active episode, not the whole preceding arithmetic history.

At X1048576 B2710, 775960 of783246 repeated q hits (99.07%) belong to q<=B/16, while that q-band contributes3098536 of4031949 overall prime incidences (~76.85%). At X1999996, 1795867 of1806864 repeats (99.39%) are in q<=B/16. Medium and large q repeat much less often empirically. These are diagnostics, not a theorem about any growing q cutoff.

## 5. Proposed analytic program using A2 and A3

The FIRST-vs-repeat sufficient criterion from the previous note requires `(F/H)*log B→∞` along an unbounded dyadic subsequence (for example, F/H>=c/sqrt(log B) with fixed c>0); a mere fixed-constant lower bound of order 1/log B is not enough for the earlier o(XB) proof. Write R=R_direct+R_3+R_large and use R_large<=V. Then a **precise, more local** sufficient hypothesis is

    BOXED: R_direct(X)+R_3(X)+V_X <= (1−δ_X) H_X
           on unbounded dyadic X with δ_X log B→∞.        (OPEN)

By (A3), V can in principle be bounded using a source-weighted common-divisor correlation of current clipped increments with C²−1. The **local** R_direct+R_3 counts q-hit races in the next one or two nonunit events after newly acquiring q activity, rather than the full previous q-return interval. Both pieces remain difficult for the dynamically selected actual C states; no unproved CRT equidistribution is being assumed.

Another possible, but STRONGER, local activation-flux sufficient target is `A_X^{act}<= (1−δ_X)H_X` with δ_X logB→∞; by A1 and R<=A, it also yields twins. Its finite ratio A/H trends upward, while the true repeat fraction R/H remains around .19-.21, so the **direct short-return + exceptional divisor decomposition** is a better target than requiring a uniform full activation-count contraction.

**Open obstacles:** (i) a source-weighted two-event q-clock correlation bound when q has already appeared earlier in the same canonical source; (ii) a power-saving or sufficiently small coefficient for V_X, perhaps by combining d>=2q−1 with the near-increment divisibility and rarity of simultaneous prime factors in d; (iii) controlling contributions of frequently repeated small q (q<=B/16 in tested ranges) without assuming any fixed prime-wheel termination estimate extends uniformly with B. The LOW23 RESET-slice 599-step bound applies only at true resets; it cannot be used to control arbitrary charged-state high-event chains.

### Reproduce

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/recharge_activation_audit.cpp -o /tmp/recharge_activation
/tmp/recharge_activation 256 512 1024 4096 16384 65536 262144 1048576 1999996
python3 research/independent_activation_literal.py 256 512 1024 4096

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/return_overlap_audit.cpp -o /tmp/return_overlap
/tmp/return_overlap 4096 16384 65536 262144 1048576 1999996
```
