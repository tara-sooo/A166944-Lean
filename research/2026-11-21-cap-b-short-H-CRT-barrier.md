# Cap B: exact CRT barrier for consecutive short selective-H events

Date: 2026-11-21 JST. **Status: new reproducible finite-arithmetic/paper lemma; not Lean-kernel formalized, and NOT an unconditional Cap B proof.**

Primary reproducible certificate: [cap_b_short_H_crt_certificate.py](cap_b_short_H_crt_certificate.py), Python 3 standard library only. Companion joint-phase and restricted-prime CRT audit: [cap_b_joint_cooldown_crt.py](cap_b_joint_cooldown_crt.py). Both were locally executed and committed to GitHub with remote content readback.

This studies the selective growth H = trace.growthAtLargeGaps in A166944/RebalancedCrossingGrowth210.lean and A166944/ReplayOffset210.lean. The user-uploaded workspace ZIP's cap_bound/WeightReal.lean, AllIndices.lean and slow_backward.md were directly inspected.

## 1. Sharp short-H-run lemma at a low offset

A genuine event from (s,C) to (r,C+e-1) has odd increment e=d(r)>1 and gap g=r-s. It is counted in H exactly if e-1<3(g+1). The kernel-proved large_relative_gap_cases theorem identifies **short H events** as those with g≤10, e≤33; the remaining H events with g>10 have prime increment.

**Finite-certified lemma:** At **any** moving-horizon state with C even and offset X=2s-C in {0,2,4,6,8,10}, a consecutive path consisting **only of short H events** satisfies simultaneously

\[
\boxed{\#\text{events}\le31,\quad H_{\rm short}=\sum(e-1)\le234,\quad T_{\rm short}=\sum g\le152.}
\]

The necessary-condition enumeration treats all **36** pairs (X,s mod 6), explores **214,780 prefix nodes**, has no imposed maximum depth, and does **not merge distinct histories**. The maximum depth is 31. All three maxima are attained by *genuine full-gcd first-hit local paths* at synthetic initial states (not certified A166944 record states):

| Sharp statistic | Synthetic initial s | Initial X | Events | T | Hshort |
| --- | ---: | ---: | ---: | ---: | ---: |
| #events=31 | 48,685,793,956 | 0 | 31 | 140 | 220 |
| Hshort=234 | 13,500,671,025,254 | 10 | 28 | 142 | 234 |
| T=152 | 3,199,701,545 | 8 | 30 | 152 | 176 |

Each asserted full-gcd witness has every intermediate unit gcd, each full nonunit gcd, horizon membership r≤C and nonnegative post-offset independently checked in the script.

At any **authentic canonical start** (s,C)=(M+2,2M-2) with M>5 a twin prime, X=6 and s≡3 (mod 6). The single restricted root has 5,123 nodes, and the sharper bound

\[
\boxed{\#\text{short H events}\le26,\quad H_{\rm short}\le204,\quad T_{\rm short}\le129}
\]

holds if its following events are all consecutive short H events. A 26-event local synthetic full-gcd witness beginning at s=41,191,488,705 has the same initial X and s mod 6. **No synthetic start is claimed to be attained by the actual A166944 recurrence.**

## 2. Why the CRT enumeration rigorously covers every real short H run

At any state set X=2s-C. Before an event with gap g, the tentative hit index is r=s+g, so 2r-C=X+2g. The exact gcd rule gives:

* **Even r:** e divides r and C-1, so e divides X+2g+1.
* **Odd r:** e divides r-2 and C+1, so e divides X+2g-5.

A true first hit also satisfies g≤2e, and the next offset is X'=X+2g-(e-1)≥0.

For a proposed word of gaps/increments, the parity of each r is known from initial s mod 6 and cumulative gaps. Each event forces a residue on the **same initial index** s0:

* even hit: s0 ≡ -(T+g) (mod e);
* odd hit: s0 ≡ 2-(T+g) (mod e).

The program merges every congruence using the **generalized CRT**; this is valid for *composite increments* 9, 15, 21, 25, 27 and 33 as well as primes. The modulus L is always the least common multiple of 6 and all event increments seen so far. Since an actual increment e divides L, the real full-gcd equality at each earlier hit requires gcd(d(r),L)=e; every earlier unit index requires gcd(d(j),L)=1. **After every CRT modulus enlargement the verifier recomputes the projected gcd at every preceding event and intermediate index**, preventing a later factor (e.g. 13) from contradicting an earlier alleged hit. It examines *all* candidate integers 1≤g≤10 and odd 3≤e≤33 satisfying the short-H condition at each surviving prefix.

Because untracked factors and the old-horizon limit can only **remove** candidates, every genuine short H path is among the explored prefixes. The absence of 32-step candidates certifies the upper bound. The finite search is not yet represented as a Lean theorem.

Reproduce:

```sh
python3 research/cap_b_short_H_crt_certificate.py
```

## 3. New exact simultaneous index/horizon factor cooldown

If a common odd factor q≥5 divides increments at two events, denote their hits and pre-horizons by (r_i,C_i),(r_j,C_j). For even q-hits,

\[
r\equiv0,\quad C\equiv q+1\pmod {2q};
\]

for odd q-hits,

\[
r\equiv q+2,\quad C\equiv q-1\pmod {2q}.
\]

Thus the *exact residue classes modulo 2q* and their least positive representatives for the differences are:

| First → second hit | r_j-r_i | C_j-C_i |
| --- | ---: | ---: |
| even → even | 2q | 2q |
| even → odd | q+2 | 2q-2 |
| odd → even | q-2 | 2q+2 |
| odd → odd | 2q | 2q |

For the horizon difference in the odd→even case, the residue 2 modulo 2q is also algebraically possible but is **too small**, since the first event alone raises C by at least q-1≥4. Therefore 2q+2 is the first feasible representative.

Summing these necessary waiting costs over k appearances of a common factor q gives

\[
\boxed{T\ge(k-1)q-2,\qquad G\ge(2k-1)q-3.}
\]

The index bound is new relative to the preceding horizon-only cooldown; it holds for composite q, not just primes. The companion audit verifies all 16 qualifying factor-sharing pairs among the actual threshold M=45,895,573's 37 certified first-hit events.

## 4. Compact symbolic CRT for restricted prime alphabets

For a word of *prime increments only* p_i, write B_i=sum_{j<i}(p_j-1). An even initial horizon C0 satisfies all *horizon-only necessary divisibilities* iff, for each prime p, the intersection of the sets {1-B_i,-1-B_i} modulo p over occurrences with p_i=p is nonempty. Different primes are independent by CRT. This is exact for the horizon-only model, and ignores true hit order, gap and other increments.

The companion Python audit finds:

| Exclusive increment alphabet | Maximum horizon-only hits |
| --- | ---: |
| {11,13,17} | 4 |
| {11,13,17,19,23} | 11 |
| {11,13,17,19,23,29} | 19 |

For the first two alphabets, these maxima are independently confirmed by full horizon-period DP (periods 4,862 and 2,124,694); the 61,616,126-period six-prime DP was also independently run locally in C++17. All 35 prime triples selected from {11,13,17,19,23,29,31} have at most 7 horizon-only hits, the maximum at {11,13,31}. This **does not** bound paths with intervening increments outside those alphabets.

An important limit: if all primes in such a word are distinct, the horizon-only CRT criterion always has a solution when the initial horizon may be freely chosen. Repetitions and actual first-hit conditions, plus authentic record history, are indispensable for a global argument.

## 5. Relation to the remaining Cap B gap

An alleged first Cap B crossing at the official M=45,895,573 requires H≥5,291,742 on its predecessor prefix (from existing Lean trace bounds and the square-gap bound). A short-only run beginning at offset X≤10 contributes **at most 234** to H. If *every* contribution came from low-offset-starting short-only runs with **no long H events**, there would have to be at least ceil(5,291,742/234)=**22,615** separate runs, with other event types intervening.

A useful three-way numerical necessary condition follows. Split the predecessor prefix into maximal consecutive short-H runs. Let R count the runs that **start** with X≤10, let S_high count short-H events in all other runs (those starting with X>10), and let L count long-prime H events. Every low-start run costs at most 234; every other short event costs at most 32; every long-prime H event contributes at most 31,038 at this M. Consequently any first crossing requires

\[
\boxed{234R+32S_{\rm high}+31,038L\ge5,291,742.}
\]

For instance, if L=0 and S_high=0 it needs R≥22,615; if L≤169 and S_high=0 it needs R≥198. This is a **necessary condition**, not an asserted global bound on these counts. It locates the precise remaining packing problem.

The missing global step is now more localized: control **(a)** long-prime H events, **(b)** short H runs starting at higher offset X>10, and **(c)** repeated transitions/returns that allow many low-X short blocks. Nothing in the present certificate globally bounds the number of those returns. **The universal Cap B theorem, fixed-sample upper bound and twin-prime infinitude remain unproved.**
