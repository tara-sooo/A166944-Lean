# Twin-prime-first: exact q-deleted phase-race set and a 1/8 one-sided spectral criterion for the top prime band

2026-11-23 JST. Issue #3 / Issue #4 continuation of LOW7 kernel certificate in draft PR #5 and the prior `2026-11-23-high-band-exclusivity-and-growth-spectrum-plan.md`. This is a **new elementary paper-level implication and exact reproduced finite data**, NOT a proof of the asymptotic source-selected phase discrepancy, NOT an infinite twin-prime theorem, and NOT a new Lean kernel checked module. A finite LOW7 residue checker (not the return estimate) was separately accepted by the pinned Lean 4.33.1 GitHub Actions run `45130164879`.

## 1. What was actually measured

Dyadic `X`, odd `M` in `[X,2X)`, `s=M+2`, `K=floor((7M-1)/4)`, `B=ceil(sqrt(7X))`, full squarefree clipped parity-GCD wheel, even horizon `C`. The event increment is the product of distinct odd prime factors `<=B` of `gcd(n,C-1)` at even n, or `gcd(n-2,C+1)` at odd n. At an event at time `t`, post `C := C+d-1`.

Fix a prime `q >= B/2`, and **each actual q-bearing event** (including composites, returns, and events whose high owner is smaller than q). Call its tagged post-state `v=(M,q,t,C,K)`. Starting exactly at `v`, run the FULL-HORIZON `q`-deleted ghost: advance through genuine non-q clipped-GCD event clocks to `K`, always omitting q, but not removing any other prime. The ghost may differ from the original after the first future q hit; this is intentional. Its **first prospective q hit**, if any, is exactly the first future actual q-bearing event, including ties with non-q clocks. The C++ auditor asserts this for EVERY tagged q event. A separately written literal Python n-by-n implementation checks the same fact at X256,512,1024,2048 (including the shift statistic).

`G_q(v)` denotes the total q-free ghost clipped growth through K. The even post-q state has `C mod q = 0` and needs growth at least `q-1` to reactivate; the odd post-q state has `C mod q = -2` and needs at least `q+1`. Hence `G_q(v)<q-1` or `<q+1` respectively is a **sound sufficient no-return barrier**. This barrier is far from complete: at X65536 and top q>=B/2, 4028 of 8585 FIRST-tag states have `G_q` above the minimum while no q actually returns.

## 2. Exact clock calendar, phase offsets and the one-step identity (NEW)

For odd prime q, the only time indices at which q could ever fire are

    even n == 0 (mod 2q), or odd n == q+2 (mod 2q).       (CAL)

This is independent of C; whether q actually fires additionally requires `C-1 == 0 (mod q)` for the even calendar or `C+1 == 0 (mod q)` for the odd calendar.

On each q-deleted plateau `[u, next_nonq)` after the tagged q hit, compute at each calendar slot `n` up to the NEXT non-q event (tie included) and cutoff `K`:

    phase a(n) = (Cghost-1) mod q, if n even,
               (Cghost+1) mod q, if n odd.

Exclude the very first post-q plateau from this phase-set diagnostic. It has **no actual q clock activation** because the q hit leaves C congruent 0 or -2, and the exclusions create no change in the actual phase-0 hit predicate. Let `A_q(v) subset Z/qZ` be the set of distinct such `a(n)` over the remaining ghost calendar slots. This is a **counterfactual ADDITIVE phase-offset set**, not a new original recurrence and not a probability distribution: for an artificial additive phase offset a, the q clock at the appropriate calendar n would fire no later than the other-prime clock on that fixed q-free ghost. The original phase is `a=0`.

**Exact one-step lemma:**

    1{there is another actual q hit after v and by K} = 1{0 in A_q(v)}.  (PHASE0)

Proof: q is inactive immediately after a q hit. Before its first subsequent q hit, original and q-deleted ghosts coincide, including other-prime event ties. At any q calendar clock, the required C divisibility is precisely `a(n)=0`. Conversely the earliest such calendar slot on the ghost is the next actual q hit. Any later q-free ghost divergence after this first hit is immaterial to set membership 0.

Let `V_J(X)` be the multiset of ALL actual tagged q post-states for primes `q in J=[B/2,B]`, one tag per actual q-bearing event, including repeat hits. Define

    F_J = sum_(M,q in J) 1{N_q(M)>0},
    R_J = sum_(M,q in J) (N_q(M)-1)_+,
    T_J = |V_J| = F_J+R_J,
    P_J = sum_(v in V_J) |A_q(v)|/q,
    D_J = R_J-P_J.

By PHASE0 we have the EXACT identity

    R_J = sum_(v in V_J) 1{0 in A_q(v)}.             (TAGGED)

For `e_q(z)=exp(2 pi i z/q)`, the discrete Fourier indicator gives an exact signed decomposition

    D_J = sum_(q in J) (1/q) sum_(a=1..q-1)
                  sum_(v in V_J tagged q) sum_(b in A_q(v)) e_q(a*b).   (FOURIER)

No independence of selected source states or false CRT equidistribution has been assumed. The Fourier sum is real because conjugate frequencies pair.

## 3. Unconditional strict 6/7 contraction of PHASE-AVERAGED top-band hazard (NEW)

**q calendar lemma:** If `t` itself is a q clock calendar slot (as at every q event), the m-th strictly LATER q calendar slot occurs at an elapsed time >= m*q-2, for every m>=1. Indeed successive clock gaps alternate q+2 and q-2; two successive gaps sum 2q. Thus there can be at most

    floor((K-t+2)/q)

future calendar slots by K. Each contributes at most one distinct phase offset to `A_q(v)`, so

    |A_q(v)|/q <= (K-t+2)/q^2.                       (SLOTS)

Since t >= M+3, M<=2X-1, and K<= (7M-1)/4,

    K-t+2 <= (3M-9)/4 + 1 <= 3X/2 - 2 < 3X/2.

Because q>=B/2 and B^2>=7X,

    q^2 >= 7X/4.

Therefore EVERY tagged top-band q post-state satisfies the strict deterministic bound

    |A_q(v)|/q < 6/7,  and hence  P_J < (6/7)*T_J.    (TOP-PHASE)

This is a universal arithmetic fact about the **uniform additive phase average of an exact q-deleted ghost**, NOT a claim that the original source-selected phase 0 is uniformly sampled. Its proof depends on the q event calendar and the original exact dyadic horizon, NOT on the numerical data, PNT, LOW7 growth, or any open analytic estimate.

### New quantitatively modest sufficient spectral input, still OPEN

It suffices to establish on arbitrarily large dyadic X, or eventually for all X,

    D_J = sum_(v in V_J) [1{0 in A_q(v)} - |A_q(v)|/q]
          <= (1/8)*T_J.                              (DISCREPANCY-1/8)

Indeed, with the unconditional TOP-PHASE:

    R_J <= P_J + T_J/8 < (6/7+1/8)*T_J = (55/56)*T_J.

As T_J=F_J+R_J, this forces

    R_J < 55*F_J <= (55X/2)*pi(B) = O(XB/log B) = o(XB).   (TOP-RETURNS)

The threshold 1/8 is simply a comfortable constant below the sharp limiting margin 1/7: any one-sided discrepancy `D_J <= eta*T_J` for fixed eta<1/7 works. **This proves the top-band return estimate ONLY conditionally. It does not bound lower-band q returns and hence does not prove twin infinitude.** Importantly, the needed input is NOT uniform phase mixing: the original phase may be positively biased by almost 1/7 of all selected q tags, and the argument still closes.

## 4. Strict compiled original-GCD data (all tagged q post-states)

`research/twin_prime_band_phase_race_audit.cpp` checks, for every source and every q-bearing event in the bands B/4<=q<B/2 and q>=B/2, the exact q-deleted first return time equals the ACTUAL next-q event; it then continues the ghost through K to collect distinct hypothetical additive phase shifts, growing its own state without q. It stratifies actual q returns by whether LOW7 clocks were still active at the final ghost plateau, and by the number of intervening foreign-high (>=11) events. `research/twin_prime_band_phase_race_literal.py` independently implements the ORIGINAL full wheel and every ghost integer-by-integer, crossmatching the full stats at X256/512/1024/2048.

Top band J=q>=B/2. `P_J` is a **formal shifted-phase average**, not a measured actual return probability.

| X | F_J | T_J | actual R_J | P_J shifted | growth-too-small tagged states | low-clock-active actual returns | actual returns with >=3 high donors |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 79 | 90 | 11 | 10.7499 | 46 | 0 | not yet filtered in this table |
| 512 | 149 | 149 | 0 | 8.7242 | 80 | 0 | n/a |
| 1024 | 152 | 155 | 3 | 6.7943 | 101 | 0 | not yet filtered in this table |
| 2048 | 332 | 356 | 24 | 11.7810 | 218 | 0 | not yet filtered in this table |
| 4096 | 571 | 582 | 11 | 11.7958 | 381 | 0 | 11 |
| 16384 | 2139 | 2147 | 8 | 25.3125 | 1344 | 0 | 8 |
| 65536 | 8585 | 8585 | 0 | 56.1968 | 4557 | 0 | n/a |
| 262144 | 29749 | 29749 | 0 | 90.3922 | 17092 | 0 | n/a |
| 524288 | 44767 | 44798 | 31 | 86.9089 | 30223 | 0 | 31 |
| 1048576 | 99271 | 99276 | 5 | 140.9900 | 62829 | 0 | 5 |

Every enumerated top-band q return happened with **NO 3,5,7 clock active at the last frozen plateau**; this is ONLY an observation, not a theorem. Every top-band return at X>=4096 had at least three other high events in between (also observation). Mid-band q in [B/4,B/2) DID have low-active q returns, e.g. 128 at X262144.

Important falsifications:

1. 'Top-band q never repeats for sufficiently large X' is not established and fails as a purported simple finite extrapolation: R_J=0 at X65536/262144 but reappears as 31 at X524288 and 5 at X1048576.
2. A blanket **signed** claim `D_J<=0` for every X is false: X2048 has R_J=24 while P_J=11.7810, so D_J=12.2190>0. However `D_J/T_J approx 0.0343`, which is below the proposed 1/8 threshold. Finite checking of DISCREPANCY-1/8 over the listed X is not an asymptotic theorem.
3. More total q-free growth than the minimum q recharge does NOT imply q return. At X65536 there are 4,028 FIRST tagged top-q trajectories with enough total ghost growth and zero actual top-q returns.
4. 'Nearby-prime one-donor sieve alone suffices' fails empirically: all 31 top-q returns at X524288 and all five at X1048576 have three or more foreign-high donor events.
5. The proposed one-sided discrepancy is **NOT pointwise**. A real original-GCD state in the literal oracle at X256, M423, q23 has the first q hit at t485 and next at t552, with the ghost's exact shifted winning set A={0,2,11,19,21}. Thus at that ONE tag 1{0 in A} - |A|/q = 1-5/23 = 18/23 >1/8. The bound requires cancellation/averaging over the whole source-selected ensemble, not a per-state potential inequality.

## 5. LOW7 clock racing and the new analytic subproblem

At a q-active ghost plateau with any low prime p in {3,5,7} active, a low-p clock occurs in <=2p<=14 steps. For q to win from this plateau, its next calendar slot must occur within <=14 steps. If none of the low primes is active, q competes with OTHER primes >=11; the q clock can be preempted by a foreign high-prime event.

At X262144, among top q tags the ghost visits 1,579 plateaus where q and some LOW7 clock are both active; the LOW7 clock won every time. It visits another 597 q-active LOW7-inactive plateaus; a foreign high clock won every time. At X524288, of 152 q-active LOW7-inactive plateaus, 121 were preempted by other high primes and 31 produced actual top-q returns. All are finite original-process measurements.

A concrete **next proof target** is the one-sided frequency bound DISCREPANCY-1/8 on the SOURCE-SELECTED all-tag ensemble `V_J` for the top band, *not* an invalid randomly independent CRT model. The q-free phase set and its 6/7 contraction are exact. The missing bound is the signed nonzero-frequency contribution in (FOURIER). A proposed route is to condition the q-free clocks on LOW7's 22,050-state residue type and charge small/large frequency surplus through the foreign-high events, not the first donor only. The LOW7 state and the q post-reset phase can be strongly correlated: selected-phase 0 is not a uniformly random shift of the q-deleted ghost. This final analytic inequality is OPEN.

For lower q bands, `(K-t+2)/q²` is not <1 for the full horizon, so even a phase mean argument will need shorter time slabs of length <q² and a method to restart/source-transport the tagged measure between slabs. No legitimate lower-band contraction was derived here.

## 6. Replay instructions and verification class

Strict C++17 original-GCD event-jump, all q tags, full q-deleted shadow and bitset-distinct additive shifted winning phases:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/twin_prime_band_phase_race_audit.cpp -o /tmp/phase_race
/tmp/phase_race 256 512 1024 2048 4096 16384 65536 262144 524288 1048576
```

Independent Python integer-by-integer original full wheel and independent literal q-free ghost:

```sh
python3 research/twin_prime_band_phase_race_literal.py 256 512 1024 2048
```

The comparisons include exact all-tag first q-next-hit timestamps, and numerical `P_J` values (floating weighted sum, checked to displayed precision by independent Python). The finite certificate checks in draft PR #5 remain Lean-kernel verified; **the new paper-level phase-window and discrepancy implication is NOT yet Lean compiled**.