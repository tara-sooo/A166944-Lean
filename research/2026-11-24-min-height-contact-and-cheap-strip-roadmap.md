# Height-constrained full-mass contacts and cheap-strip compression: candidate next route

2026-11-24 JST. Continues a4eada21e9559e103c8d16e96b2bc03f152ed450 on the existing research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions, not Lean-checked; no new computation or novelty claim. The total contact bound and twin-prime conjecture are open.

## 1. A full-cap deletion using height rather than the gap between prime labels

Use canonical MIN and LOW7 L=210. X dyadic, N=X/2, B=ceil(sqrt(7X)), original sources and cutoffs. Use uniform high-key absorbing cap T=ceil(B log^(1/4) B). The previously established arithmetic S_key bound gives R_pre=O(X^2/log^(11/4) B) plus O_L(X T log log B)=o(X^2); the latter is negligible relative to the first term. Thus the same sufficient contact target liminf P_d/(NT)<1/2, d=floor(T/2), applies. Every executed high predecessor key has mass <T.

Let q,q' be the preceding selected HIGH labels of two incoming classes, at their own earlier pre-horizons D,D'. Write their post-high states as (u,H_a),(v,H_b) where H_a=D+q-1 and H_b=D'+q'-1. Distinguish these horizon symbols from height h=2t-C. The established height identity (2026-11-23-min-clock-gap-height-regeneration-dyadic-renewal.md) gives
    h_a=2u-H_a=b_a+2kq, h_b=2v-H_b=b_b+2k'q',
    b=0 for even clock, b=6 for odd clock, k,k'>=0.
The even and odd event-clock classes are 0 and q+2 mod 2q respectively. A reset has k=0.

Consider cross-class contacts at a proposed common high key (p,C). Impose on both preceding post-high heights 0<=h_a,h_b<=B, and q,q'>=Q=ceil(B/log^(1/16) B). Suppose the two tags have the SAME actual arrival physical state (t,C) after their intervening LOW-only prefixes. More generally, allow them to have distinct arrival times at C but the SAME next clock event n,p,C with r(C)<=z=ceil(log^(1/8) B). The LOW-only prefixes have horizon gain <L and elapsed time <=3L. In the same-clock case their actual arrival time difference is <2r(C)<=2z. Consequently
    |u-v|<=3L+2z, |H_a-H_b|<L,
    |h_a-h_b|<=7L+4z.
For same-arrival contacts alone one may replace z by zero in these inequalities. This describes a subset of projected contacts, not all asynchronous contacts sharing p,C.

If q=q' and q>3L+2z+2, two clock phases of different parity cannot lie this close, since their residues 0 and q+2 mod 2q are at least q-2 apart on the circle. The same phase forces u=v. Then the distinct even post-horizons in the same residue class mod q are at least 2q apart, contrary to the bound L; hence H_a=H_b and D=D'. The two previous high keys would be the same. Thus the distinct previous-key pairs considered here must have q!=q' for large B.

If exactly one height index is zero and the other positive, the height difference is >=2Q-6, impossible. If both positive, then
    2kq-2k'q'=c, |c|=O_L(1+z), 1<=k,k'<=O(B/Q).
For a fixed q,k,k',c, q' is determined. Even ignoring whether it is prime, at most
    O_L(pi(B) (B/Q)^2 (1+z))
possible label-index tuples exist. For each tuple, the possible u-v differences are O_L(1+z). Fix a difference and both parity sides. The two event-clock congruences give at most one residue class modulo 2qq', and u lies in an O(X) interval, so there are O(1+X/(qq'))=O(log^(1/8) B) possibilities for u. The post-horizons and pre-horizons are then determined. Enumerate the finitely many even LOW prefix gains g,g'<L, which determine the common C if consistent. The number of candidate predecessor pairs with common C, excluding two-reset pairs, is therefore
    O_L(B log^(4/16-1) B (1+z)^2)
       = O_L(B/log^(1/2) B)
for z=ceil(log^(1/8) B), or O_L(B/log^(3/4) B) in the same-arrival-only case. No extra factor for possible current p: at the fixed C the incoming subsets for different p are disjoint; sum their cross-products <= product of the whole previous masses <T^2. The actual far cross-pair count (including repetitions) in this class is at most
    O_L(T^2 B/log^(1/2) B)
        = O_L(NT/log^(1/4) B) = o(NT).
For same physical arrival alone the bound is O_L(NT/log^(1/2) B). The ratio uses B^2~7X. This permits BOTH predecessor masses near the full cap. It differs from the preceding close-top-prime deletion: the two labels need not be close, but they satisfy a short height relation with small multipliers. No upper-bound prime-pair sieve is required, just pi(B)=O(B/log B) and CRT.

This establishes a concrete partial bound at full mass. Both-reset pairs (k=k'=0) are the exact exception to the height relation determining q'. The result also leaves parents below Q, heights above B, distinct next clocks and long acceptance intervals outside its scope. It does not assert these complement classes have small mass. The cap here is B log^(1/4) B, not the previous B log^2 B; all arguments for the first-contact implication remain valid with this smaller cap, but finite results obtained at other caps do not prove it.

## 2. Cheap-and-low-height strip compression

At an event from (t,C) to (n,C+p-1), with pre-height h=2t-C and post-height h' >=0,
    h'=h+2(n-t)-(p-1),
    p-1<=h+4r(C).
The second inequality uses the exact MIN wait n-t<=2r(C). Take y an integer tending to infinity slowly (e.g. floor(c log log B) with fixed sufficiently small c>0), y>=11 eventually. Define an event in the cheap/low-height strip by
    h<=y/2,  r(C)<=(y-2)/8.
Then p-1<=y-1, hence p<=y. Thus EVERY consecutive run of such events is a low-only run for the cutoff y, regardless of adaptive choices and actual times. With L_y=2 product_(3<=p<=y) p, the established low-wheel barrier gives total gain <L_y (or <=L_y suffices), r-cost <=3L_y/2, elapsed <=3L_y. Chebyshev's bound on sum log p permits L_y<=log^eta B for any chosen fixed eta>0 by choosing c small enough. More generally one could use y=c log B for L_y<=B^eta, at a larger enumeration cost.

As a result a root with an entire prefix in this strip can reach a given horizon C only from an original C0 within L_y, yielding O(L_y) possible roots. For any proposed group of mass m>=a>>L_y, all but O(L_y) tags must previously have executed an event outside the strip. For each such tag take its LAST outside-strip event before the contact, then the intervening suffix has gain <L_y and elapsed <=3L_y. The same statement holds for a tag at a stopped key, without executing that key. This suggests compressing the cheap history to last outside-strip states, not assuming that r small alone forces p small. One must retain every source tag; a last outside-strip event may be a low selected prime with large height. The possible outside-strip causes are r>(y-2)/8 or h>y/2, possibly both. Neither their population nor mass product has yet been bounded.

## 3. Proposed research sequence (the unresolved complement, not a new claim of proof)

The existing arithmetic contact classification still leaves cheap/cheap and large mass. A concrete next experiment is to replay the stopped-cohort witness pairs at first projected contact and record:
- whether they have the same next event clock n (physical coalescence) or distinct n (asynchronous projected contact), and whether their arrival intervals overlap;
- previous high post-heights and indices k,k', reset/reset vs nonreset, and the actual low prefix gains and time offsets;
- the most recent outside-strip event per source, with actual physical state, prior mass, cost and age; retain original cutoffs and compute the witness-pair mass cross product, rather than just candidate counts.

The last-exit compression enables CRT/clock estimates for the pair of exceptional states near each contact, with a growing but small offset budget L_y. It is not yet established that this closes the low-label/high-height or reset/reset cases. For genuinely physical reset states, there is an exact one-dimensional renewal graph: reset h=0 on even t or h=6 on odd t; each state has a deterministic next reset or no next reset under untruncated dynamics, and original cutoff tags restrict whether that transition is used. Odd resets coincide with canonical initial states. A root-set recursion over the first subsequent reset can be used instead of enumerating all intermediate histories; it must count both existing incoming roots and newly injected canonical roots and retain cutoffs. This recursion itself does not provide a contraction. The needed result would be a quantitative bound on the mass-weighted products of incoming reset branches, or on the amount of mass transferred through repeated resets. If a reset graph is used, asynchronous projected contacts must be separately accounted for.

No all-class bound, no proof of the twin-prime conjecture, no Lean compilation. This is a specific mathematical direction and a partial full-cap estimate, not evidence that the final proof is close. No new branch or main edit.
