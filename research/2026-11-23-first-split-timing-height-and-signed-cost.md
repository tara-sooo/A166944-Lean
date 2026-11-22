# A166944 squarefree prime insertion: signed cost is decided by first-split TIMING; post-freeze height lattice

2026-11-23 JST. **Status: exact elementary paper lemmas and independent finite original-gcd event-jump tests; NO proof of uniform dyadic mean-growth, Cap B, or twin-prime infinitude. No new Lean-kernel proof.**

Follows [safe first-split AP packing and L1 renewal](2026-11-23-squarefree-early-prime-cost-L1-residue-packing.md), [4-state safe p-hit renewal](2026-11-23-squarefree-prime-first-hit-regeneration-and-fibre-transfer.md), and [squarefree sqrt-wheel mean reduction](2026-11-22-squarefree-sqrt-wheel-mean-reduction.md). Reproducible exact scanner: [squarefree_first_split_timing_audit.cpp](squarefree_first_split_timing_audit.cpp).

## 1. NEW exact first-split SIGN barrier without any p>6h+7 hypothesis

Fix an odd canonical-shaped M>=7 and a common cutoff K. Let L be an odd squarefree wheel and p>=3 a prime NOT dividing L. Let h=G_L(M), and S_L be the LAST nonunit L-wheel event in (s,K], s=M+2 (or s if none). Let τ be the first n where the L and Lp recurrences differ. If no split occurs, Delta_p=0.

At τ both trajectories have the SAME previous even horizon, the old L increment is e0>=1 and the enlarged Lp increment is EXACTLY p e0. The initial extra horizon growth is (p−1)e0. Let

    R_old = sum_(τ<n<=K) (d_L(n)−1),

the entire remaining old growth *after* τ. All subsequent new Lp increments contribute nonnegative growth. Hence universally:

    BOXED: Delta_p(M)=G_Lp(M)−G_L(M)
           >=(p−1)e0−R_old.                          (1)

In particular, τ>=S_L implies R_old=0, so Delta_p>= (p−1)e0>0. Consequently

    BOXED: Delta_p<0 ==> τ<S_L and R_old>(p−1)e0.  (2)

This makes the earlier informal "cancellations happen when an inserted prime preempts old events" an EXACT timing and growth condition. It holds at ANY p, no squarefree sqrt cutoff assumption beyond p fresh, and no complete CRT-period averaging. It does not UPPER-bound positive costs.

## 2. NEW exact POST-FREEZE first-hit height normal form, without safety

If the first split occurs at τ>S_L, old e0=1, so new e=p and the old terminal horizon is already frozen

    C=2M−2+h.

The post-split deficit X=2τ−(C+p−1) is nonnegative and, by universal parity p-hit residue,

    BOXED: if τ even, X=2k p;
           if τ odd,  X=6+2k p,                   (3)

for an integer k>=0, except that for p=3 and τ odd the representation could use k=-1 if X=0. Hereafter take p>=11 so k>=0.

Define the frozen-horizon target parameter u=(C+p+1)/2. Then the exact first p-split INDEX is

    τ=u−1+k p    (even p-hit),
    τ=u+2+k p    (odd  p-hit).                        (4)

For k=0, the p insertion lands at X=0 (even) or X=6 (odd). Therefore WITHOUT ANY growth-adaptive safety p>6h+7:
- odd k0 post-freeze hit: immediate canonical-shaped seed u at n=u+2;
- even k0 post-freeze hit: universal 3/5 bridge returns X=6 in 3/5/7 further steps (bridge cost0/4/8), with target v=u+b/2.
The target residues modulo p remain {0,1,3,5}; however h can now be much larger than p, so the previous bounded target fibre-size k_v<O(p) and displacement O(p) are unavailable. One can instead apply the earlier universal quadratic collision budget and a restricted moment over a wider interval.

For k>=1 the new deficit is >=2p: no unconditional bounded-time canonical regeneration theorem exists (e.g. L=1,p=11,M=39 first hit n57 leaves X28 and never returns to X6).

## 3. NEW deterministic HIGH-HEIGHT ENERGY budget

The old wheel's last event relative time t_last=S_L−s obeys t_last<=3h by the exact first-hit travel/growth bridge. The very first p-clock opportunity AFTER S_L lies at most 2p indices later (period2p). Hence for any first split τ>S_L,

    τ−s<=3h+2p.

At its p-hit, using X=2τ−(2M−2+h+p−1)=7−h+2(τ−s)−p,

    BOXED: X<=5h+3p+7.                              (5)

Together with X>=2kp, for any integer r>=2,

    BOXED: k>=r ==> h >=((2r−3)p−7)/5.            (6)

In particular POST-FREEZE height k>=2 REQUIRES h>=(p−7)/5. In a finite set I of starts, write W=sum_(M∈I)h(M). Then for p>=11,

    BOXED: #post-freeze first splits with k>=2
           <= 5W/(p−7).                             (7)

And for r>=2 with (2r−3)p>7, the number with k>=r is bounded by

    # <= 5W/((2r−3)p−7).

These are deterministic Markov-style high-height frequency bounds paid for by OLD growth energy; they do not bound the later NEW growth after a large-height hit.

**Why this improves the earlier safety partition:** the old condition p>6h+7 guaranteed no early split and k∈{0,1}, but it is only sufficient. Many comparisons with p<=6h+7 actually split AFTER S_L, enjoy nonnegative signed cost, and may have k0 canonical regeneration. The splitting-time / post-deficit-height taxonomy is more exhaustive.

## 3b. NEW bounded-old-growth k=0 L1 transfer without safety

The safety test p>6h+7 is NOT required for the post-freeze k=0 regeneration. Fix c>0. Consider all fresh-prime p>=11 stages with:
- first split τ>S_L, so the old wheel has already frozen and its first split increment is exactly p;
- post-deficit X(τ) in {0,6} (height k=0);
- old terminal growth 0<=h(M)<=c*p;
- the canonical 3/5 bridge, if needed, completes before K;
- no p refire before the cutoff (ONE-SHOT).

The earlier universal <=7-step bridge gives v=(C+p+1+b)/2, b∈{0,4,8}, v modp∈{0,1,3,5}, and exact gain

    Delta_p(M)=p−1+b+H_L(v;K(M)) <=p+7+G_L(v).

Here the OLD horizon is C=2M−2+h(M). Because h<=cp, the regeneration shift is still controlled, now by c instead of the prior growth-adaptive safety:

    BOXED: (p−1)/2 <=v−M <=((1+c)p+7)/2.           (T1)

Each fixed target v determines b by its distinct residue among {0,1,3,5} (modp), hence determines C. Different odd sources M mapping to the same v have h decreasing by >=4 as M increases by2. Thus

    BOXED: k_v <= 1+cp/4.                             (T2)

Define the expanded AP first moment
    T1^(c)_p(X,L)= sum_{u odd, X<=u<2X+((c+1)B+7)/2+5,
                           u modp∈{0,1,3,5}} G_L(u).

Then for the entire post-freeze k0 ONE-SHOT subset with h<=cp,

    BOXED: sum Delta_p <=(p+7)N + (1+cp/4)*T1^(c)_p. (T3)

The conditional AP first moment estimate T1^(c)_p<=A X B/p would yield O_(A,c)(XB) aggregate at each p stage. This is a direct extension of the earlier safe-early L1 theorem to **actually post-freeze UNSAFE** insertions with old growth up to c*p. It still does NOT cover k>=1, refirings, or pre-freeze signed costs.

**Finite relevant sizes with c=2, p>=11** (the stage scan was extended to count p-events in the enlarged wheel):
    X       post-freeze X0/6 and h<=2p     growth sum    subset with exactly ONE p-hit    growth sum
    4096                883                  85116               865                     82806
    16384              3960                 690942              3791                    655098

For the **wider c=2** target window, independent exact old-wheel four-AP means give max p*T1^(2)/(X B):
    X4096: 3.042397174 at p149;
    X16384: 2.819034543 at p269;
    X65536: 2.073511849 at p619.

These finite results support studying the larger post-freeze k0 class but are not a uniform L1 theorem. They also show that numerous post-freeze X0/6 contributions come from sources that fail p>6h+7, so the earlier safe-only partition was too narrow to prioritize.

## 4. Full prime-stage dyadic signed COST partition, from EXACT original parity-gcd

All odd M in [X,2X), primes p<=B_X=ceil sqrt(7X) inserted into ascending squarefree prefixes. The exact first divergence τ is found using each OLD event horizon and its p clock, not a guess from the final old horizon. Every signed stage difference is checked by exact recomputation of the full Lp wheel.

    X      pre-last +    pre-last −    post X=0/6 +   post X=2p/(2p+6) +  post other X +
    1024      6726            486           12268          16452          4980
    4096     57960          46536           99878         162170        125670
    16384   369372         524112          761250        1556242        752574

All negative differences were PRE-last in these scans, as (2) proves universally.
The table includes small inserted primes p=3,5,7, so the post-freeze labels are literal X categories rather than the k>=0 height classification, whose simple non-overlapping form is stated for p>=11. There were ZERO negative post-last first splits.

A crucial empirical research PRIORITY: the previously studied "growth-adaptive SAFE" comparisons cover only a small portion of total positive costs. Classifying by actual first split, not p>6h+7, covers far more of the dynamics. At X=16384, post-last starts contribute ~3.07 million of the ~3.44 million positive growth-difference total, and pre-last net is negative:
    369372−524112=−154740.
Thus the accurate next attack should bound post-freeze cost by LOW and HIGH deficit HEIGHTS, and the PRE-freeze component as a signed compensated difference, not only the safe-early-one-shot L1 class.

## 5. Precise remaining theorem

To obtain the sufficient squarefree mean bound for twin-prime infinitude, one could prove for every p<=B_X:

(a) a uniform upper bound on TOTAL POSITIVE post-freeze first-split cost (including high deficits k>=1 and repeated p-events) of O(X B_X);

(b) a uniform *signed* upper bound on PRE-freeze first-split total, potentially exploiting old event cancellation (finite pre-last net can be negative).

The previous four-AP L1 criterion controls part of (a), namely k0 one-shot cases with bounded fibre multiplicity. High-height frequency (7) controls how often k>=2 is possible but NOT the cost of those events. Low-height k1 with X=2p or2p+6 still has no automatic bounded return to canonical. Uniformity in X remains unproved.

No result in this note proves twin-prime infinitude or Cap B.
