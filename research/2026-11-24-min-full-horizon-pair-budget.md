# Full-horizon minimum-clock budget and separated-source pair roadmap

2026-11-24 JST. Continues 9267606842aa5caa882aa37243ee0580719ef1f0. Paper deductions and finite tests, not Lean-checked. The key new route removes the separate small-label excess A and the large-label recurrence classifications. The pair bound below is OPEN.

## 1. Entire actual trajectories, not short prefixes

Use dyadic X divisible by four, N=X/2 odd sources M in [X,2X), s=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)), the original clipped MIN wheel, and every event up to its own K(M). The verified canonical clock lemma and invariant C<=2t apply. All horizons lie in [2X,7X), and every update strictly increases the even horizon. Define r(C) to be the least prime dividing (C-1)(C+1) among odd primes <=B, or zero when none exists. At an actual pre-event horizon r(C)>0 and the wait is at most 2r(C), regardless of which prime wins. If the terminal pair is not twin, its final quiet tail is shorter than 2B because a composite neighbor has a factor <=B. No LOW cutoff or prefix length prerequisite is needed.

Let V_M be the set of pre-event horizons in the entire actual trajectory, and W(C)=#{M:C in V_M}. This counts original sources, not distinct physical states. Each source occurs at most once per horizon. Put
    R = sum_C r(C) W(C),  S0 = sum_(even C in [2X,7X)) r(C).
Since the selected prime p>=r(C), p<=3(p-1)/2, the total growth bound gives R=O(X^2) unconditionally. The total elapsed time to the last events is <=2R. If every source has a non-twin terminal, the exact dyadic travel identity implies
    9X^2/16 - 5X/4 <= 2R + 2BN.                       (1)
Therefore liminf R/X^2<9/32 on unbounded dyadic windows suffices for infinitely many twin primes (the terminal smaller prime is >=2X-3).

## 2. NEW single weighted heavy-horizon criterion

Take z=floor(B^(1/4)). Horizons with 0<r(C)<=z contribute O(Xz) to S0. If r(C)>z both C-1,C+1 have no prime divisor <=z. The standard dimension-two upper-bound sieve used in the previous note applies directly to the two forms 2j-1,2j+1, C=2j. For each odd prime ell<=z their two forbidden residues are distinct. Squarefree d has two-root product 2^omega(d), with remainder O(2^omega(d)); sum of remainders for d<=z is O(z log(2z)), negligible compared with X/log^2 B. Mertens and the upper-bound sieve give O(X/log^2 B) such horizons. Reference: Ford, Sieve Methods (Spring 2023), Theorem 2.4, as used in research/2026-11-24-min-sieved-multidonor.md; https://ford126.web.illinois.edu/sieve2023.pdf. This is an upper bound for rough pairs, not a lower bound for twin primes. Thus
    S0=O(X B/log^2 B).
For any fixed gamma<2 with gamma>0 choose tau=floor(B log^gamma B) and
    J(X) = sum_C r(C) (W(C)-tau)_+.
Then
    R <= tau*S0+J = o(X^2)+J.
Combining with (1), the OPEN sufficient condition is
    liminf_(dyadic X) J(X)/X^2 < 9/32.                (2)
Unlike the preceding prefix criterion, this needs no A(X) or J_w(X)/Q term, and ignores label history completely. The quantity W is now for all actual events of the FULL trajectories, including small-prime events. A uniform W(C)=O(B log^gamma B) for any gamma<2 would suffice directly by the S0 estimate, but has not been established. The trivial W<=N does not suffice. This reduction does not show (2) itself.

## 3. NEW sufficient estimate per dyadic band of source separations

Choose gamma=3/2 and E=sum_C r(C) W(C)^2. For w>=0 and tau>0, (w-tau)_+<=w^2/(4tau), so J<=E/(4tau).
Exactly,
    E = sum_(ordered M,M') sum_(C in V_M intersect V_M') r(C).
For each M there are at most B+1 odd M' with |M-M'|<=B. Their combined contribution E_near <=(B+1) R=O(X^2 B), with no independence assumption. For d>=B put
    E_d = sum_(ordered M,M': d<|M-M'|<=2d) sum_(C in V_M intersect V_M') r(C).
The following explicit OPEN target suffices:
    E_d <= K0 X^2 B for all d=B*2^j<X, with a constant K0 independent of X,d,
on an unbounded sequence of dyadic X. There are O(log B) bands; hence E=O(X^2 B log B), J=O(X^2/sqrt(log B)), and (2) follows. In particular no little-o saving is needed per separation band. A bound on the sum of band energies would also suffice. The per-pair scale suggested by this bound is average common weighted horizon length O(XB/d); it is not claimed.

To attack the band estimate, split into projected coincidences at distinct arrival times and coincidences at the same physical state. Let F_d count ordered pairs in the band that ever share an actual physical state. Once they meet, their forward choices agree until the earlier cutoff. Total weighted common horizons for one such pair is O(X) by the growth bound. Let G_d be the weighted sum of common pre-event horizons reached at different arrival times. Then
    E_d <= O(X) F_d+G_d.
Concrete sufficient subtargets are F_d=O(XB) and G_d=O(X^2 B), uniformly per band. They need not be separately proved if the total E_d can be controlled. For F_d, count the first shared physical state only, using original-root pairs from distinct incoming predecessor states (also the root itself if present), and the exact reverse clock intervals from the preceding note. A pair with different predecessors at the meeting state cannot have met earlier, by determinism. For G_d, count the roots of two distinct arrival-time states at one C, retaining their separation band. Both counts must use original source weights and actual cutoffs, or a valid common-cutoff overcount. A direct reverse-time implementation may drop the high-rank budget; when counting pre-event sources at (t,C), restrict the roots to K(M) at least the next selected time, as in the earlier F_T recurrence. Root separation must be retained, e.g. by interval-tagged root masses.

A useful local restriction on backward branching: write delta=2t-C>=0. If a post-event state was produced by an even-time q selection, q divides both t and C, hence q|delta; if produced by an odd-time selection, q divides t-2 and C+2, hence q|(delta-6). Both delta and delta-6 are even, so away from the respective reset values 0 and 6 the candidate q is at most half the absolute nonzero deficit. Reset states need separate treatment. Together with the previous exact admissible predecessor interval this is a concrete constraint for counting first meetings. It does not yet bound distant root mass, and no induction using it has been completed. The task is the pair estimate, not another sufficient-condition reclassification.

## 4. Finite full-run diagnostic

Code research/min_full_horizon_budget_audit.cpp. Compile and run:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_full_horizon_budget_audit.cpp -o /tmp/min_full_horizon_budget_audit
    /tmp/min_full_horizon_budget_audit 256 1024 4096 16384 65536 262144 1048576 4194304
The tested code blob 995067c02c29590f5f64afb1bbcdc6cd482e29a2 was remotely read back identically at 9629c9b13a76cc19b69d516afadffdc9e675044b. The code counts every original-source pre-event horizon, verifies elapsed <=2R, the exact travel sum, C<=2t, the terminal quiet-tail condition, and R<=tau*S0+J with the stricter diagnostic gamma=1. It does not compute E_d or F_d,G_d.

| X | B | all events | max W | tau=B log B (floor) | J |
|--:|--:|--:|--:|--:|--:|
|256|43|1354|33|161|0|
|1024|85|4146|62|377|0|
|4096|170|30191|122|873|0|
|16384|339|161096|259|1975|0|
|65536|678|796161|387|4419|0|
|262144|1355|3946588|669|9771|0|
|1048576|2710|19219036|1619|21421|0|
|4194304|5419|91629974|1819|46590|0|

At largest X: N=2097152, S0=305311594, R=5119047422, elapsed=4466918502; all sources end at twins. At X256, five non-twin terminal sources, none at other tested X. The finite counts of J=0 are diagnostic only: the asymptotic sieve term is not numerically bounded here. No new Lean compilation. Next concrete work: exact first-meeting and distinct-time pair statistics by separation band, seek a uniform pair estimate (and counterexamples), then formalize the finite clock-to-budget argument and the analytic bridge. Main unchanged.
