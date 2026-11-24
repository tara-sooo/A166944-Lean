# First-heavy selected-key stopping: extra logarithmic sieve saving and exact reverse ancestry

2026-11-24 JST. Continues dff4215f2f4f4e67f61c078f5090caf38a1be79f on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions using established MIN clock/growth lemmas and standard upper-bound sieve, exact finite audits. No Lean compilation. The long-ancestry anti-concentration estimate and twin-prime conjecture remain OPEN.

## 1. Improved arithmetic budget (one additional logarithm)

Keep odd canonical M in [X,2X), dyadic X divisible by 4, N=X/2, t0=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). r(C) is the least odd prime <=B dividing either C-1 or C+1, zero if none, for even 2X<=C<7X. Define
    S0=sum_C r(C),
    S_p=sum_{C: p|(C-1)(C+1)} r(C), p odd prime <=B,
    S_key=sum_{p<=B odd prime} S_p.
Every nonzero r(C) has at least one such p (itself). Thus S0<=S_key, even though a single C may contribute to many keys.

Reuse the uniform per-p sieve estimate from section 3 of research/2026-11-24-min-merge-mass-ledger.md. For completeness: fix p, a side sigma in {-1,1}, and write C+sigma=p h. There are O(X/p) candidates h. When r(C)<=z=floor(p^(1/4)), their total r-cost is O(X z/p). Otherwise, for sufficiently large p, h and ph-2sigma avoid both distinct forbidden residues modulo each odd prime ell<=z (ell!=p automatically). The uniform dimension-2 upper-bound sieve gives O(X/(p log^2 p)) candidates; the interval length X/p is at least a constant multiple of p, and the squarefree residue remainder sum O(z log(2z)) is negligible. Same standard sieve reference and proof parameters as the parent merge-mass note (Ford lecture notes, Spring 2023, Theorem 2.4, https://ford126.web.illinois.edu/sieve2023.pdf, previously inspected in the repository's sieve work). Each rough candidate costs <=p. Finite small p are absorbed in the absolute constant. Hence uniformly
    S_p=O(X/log^2 p).
Split prime sum at sqrt(B): small primes cost O(X sqrt(B)); large primes cost O(X pi(B)/log^2 B). Therefore
    S0 <= S_key = O(X B/log^3 B).
This improves the former S0 upper bound O(XB/log^2 B). It applies to S0 itself, not merely the selected-key stopping variant. No independence of the actual paths has been used. The arithmetic estimate is a paper consequence of the earlier per-prime sieve, not a new literature or novelty claim.

Consequences, using the exact canonical no-twin travel bound and B^2~7X:
    R=sum_C r(C)W(C), no-twin => R >= (9/32-o(1))X^2.
    W(C)=O(B log^2 B) uniformly suffices for R=o(X^2).
    E=sum_C r(C)W(C)^2 = O(X^2 B log^2 B) suffices,
        by R^2<=S0 E=O(X^4/log B).
    More generally E=o(X^2 B log^3 B) suffices.
    Each distance band E_d=O(X^2 B log B) uniformly (same unbounded windows) suffices,
        as there are O(log B) bands.
The near-origin removal from min-dyadic-cut-transfer.md can now use T=floor(B log^2 B), not merely B log B, and cost O(T X^2) within the sufficient energy bound. These are relaxations of required estimates, not proofs of them.

## 2. Absorbing first-heavy selected-key process

Fix LOW7, L=210, or a growing cutoff y with L=2 product_(3<=p<=y) p <=sqrt B eventually. Fix tau=ceil(B log^2 B). Process horizons C in strictly increasing order (all updates increase C). Start all original sources at their actual canonical roots and keep their original individual cutoffs. At C, compute the actual next lexicographic MIN event for every still active source tag. If it has no next event within its cutoff, record its terminal. Group the other tags by their selected prime p. For p>y, if the number of tags in the group (p,C) is >=tau, stop all those tags BEFORE executing the high event. Otherwise execute their actual event. All low selected events execute, with no stopping test. The stopped keys are a set H_X of (p,C), not fixed in advance; at different horizons all earlier stopped keys have already been determined. If several labels at a common C satisfy the threshold, all those groups are stopped separately. Once stopped, a root never re-enters the process.

This is an absorbing process on the true trajectories with original cutoff tags, not a cap on unweighted physical vertices, not deletion and reweighting of roots, and not the first hit of a heavy key in the unmodified full occupation count. For the final H_X, stopped paths are exactly the original trajectories truncated just before their first selected event at any key of H_X. This follows by induction in C. Each stopped key has >=tau first arrivals, each source stops once, so
    |H_X|<= N/tau=O(B/log^2 B).
All executed high-event keys carry strictly fewer than tau active tags.

Let R_pre be the cost sum r(C) of ALL executed events, including those of sources that never stop. Charge the low-only initial block to each root and each later low-only block to its preceding executed high event. The existing even-multiple barrier bounds low-only gain by <L and r-cost by 3L/2. This applies also if the next event is a stop. A high-event block starting at (p,C) costs at most r(C)+3L/2. Indeed it can be sharpened to r(C)+3d/2 where d is the distance from C+p-1 to the next even multiple of L (distance zero if already a multiple).

There are O(X/p) eligible horizons for p, uniformly since p<=B and X/p>=cB. Using S_key and the prime harmonic bound,
    R_pre <= (3L/2) N + (tau-1) sum_{p>y,C eligible} [r(C)+3L/2]
          = O(XL + tau XB/log^3 B + tau XL log log B)
          = O(X^2/log B)
for fixed LOW7 or L<=sqrt B. In the last bound the low penalty is o(X^2/log B). More generally tau=B log^(3-epsilon) B for any fixed 0<epsilon<3 gives O(X^2/log^epsilon B). The final quiet tail is NOT included in R_pre.

For any unstopped source that reaches a non-twin terminal, the quiet tail is <2B, and its elapsed time before the terminal is <=2 R_pre(M). Since K(M)-t0>=3X/4-2, such a root requires >=3X/8-O(B) executed r-cost. Thus the number of unstopped NON-TWIN terminal roots is O(X/log B), independently of the stopped population. If the original full window has no twin terminal at all, then
    #stopped roots >= N-O(X/log B).
Consequently the precise OPEN first-hit target is: on unbounded dyadic windows, at least a fixed positive fraction of roots remain unstopped, equivalently #stopped <=(1-epsilon)N for some fixed epsilon>0. This would imply at least one actual twin terminal on each sufficiently large such window. It is strictly unnecessary to bound suffixes after a stop. The sufficient target is not established.

Option: stop at all selected keys (including low), instead of grouping low blocks. Then R_pre<tau S_key, no low penalty. This variant allows a variable capacity: for any fixed 0<eta,epsilon and tau_p=max(ceil(B log^2 B),ceil(X log^(2-epsilon)(2p)/(p log^eta B))), the total cap-weighted arithmetic sum is O(X^2/log B + X^2/log^eta B), since sum_p 1/(p log^epsilon(2p)) converges. This permits much larger mass on moderate/small labels than a uniform threshold. The finite audits below use the LOW7 grouped, uniform-cap variant only.

## 3. First-hit group geometry and time localization

For a stopped key s=(p,C), let m_s be its original-source mass and G_i=C-C0(M_i) the gain of each stopped root prior to its stop. The distinct root horizons are spaced by 4, so sum_{i in s} G_i >=2 m_s(m_s-1). By C<=2t and the initial deficit 6,
    G_i <= 2(t_i-t0_i)+6 <=4 R_pre(M_i)+6.
The stopped populations are disjoint, hence
    sum_s m_s(m_s-1) <= (1/2)sum_stopped G_i <=2 R_pre+3N
                    = O(X^2/log B).
Also sum_stopped (t_i-t0_i)<=2 R_pre. Consequently the number of stopped roots whose gain OR elapsed time exceeds X/sqrt(log B) is O(X/sqrt(log B)). Under the no-twin assumption, almost all roots must therefore stop within this time/horizon scale. The stopped keys must number at least Omega(log B) by Cauchy-Schwarz on m_s if #stopped ~N. These are genuine geometric restrictions, not an anti-concentration bound at the scale tau; the early-stop scale is still much larger than tau.

## 4. Uniform short-ancestry bound by reverse high-block factorization

Take fixed LOW7, L=210; a low block includes any actual prefix of the deterministic LOW-only ghost up to the next high event or the cutoff. For a target high pre-event horizon C, a possible immediately preceding high event (prime q>7, pre-horizon D) is followed by low gain g<L, g even, so
    C = D+q-1+g,
    q | C-g  OR  q | C-g+2.
The second statement follows by substituting D=C-g-q+1 into q|D-1 or q|D+1. Thus for each possible g, enumerate only the distinct prime factors >7 of C-g and C-g+2; D is then determined. Discard D<2X. There are at most b=ceil(L log(7X+2)/log 11) reverse high-block branches (a harmless overcount). Once the reverse path reaches an initial LOW-only segment, root candidates are within <L of that horizon and spaced by 4, so at most A=floor(L/4)+1 possible distinct roots.

For any target C, the total number of original roots with at most h preceding high events reaching C as a high pre-event, even before imposing exact times, stop exclusions, or cutoffs, is at most
    U_h = A(1+b+...+b^h).
This is a root-set upper bound, not a count of paths with probabilistic weights. Each actual history yields one of the reverse words enumerated. For fixed 0<delta<1, h=floor((1-delta) log B/log log B) gives U_h<=B^(1-delta+o(1)), since b=O(log B). Combining |H_X|<=N/tau,
    #stopped roots with <=h previous high events <= (N/tau) U_h = o(N).
Thus the full no-twin scenario requires almost every original root to have more than h high selections prior to its first heavy selected-key stop, while their aggregate prefix cost and early elapsed times obey sections 2-3. This rules out heavy absorption being generated by uniformly bounded high ancestry, or even the stated growing depth. It does not bound the deeper reverse branches.

There is an exact finite improvement of the branch factor for LOW7. Since the prime clock periods 6,10,14 divide 210, a LOW-only ghost is determined modulo L in time and horizon. Enumerating every even C mod L and every t mod L and all LOW-only prefixes gives the possible reverse gains indexed by ENDING C residue. The finite audit finds at most 17 possible gains per residue, with largest 34. This supports a smaller finite reverse search than enumerating all 105 even g<L; the paper asymptotic bound above uses the unconditional L barrier, not the finite enumeration.

## 5. Exact reverse ancestry including stop exclusions and original cutoffs

Given the final stop set H_X, let F(t,H) be the set of original roots reaching physical state (t,H) (a root or a post-event state) along the absorbed paths. A root is injected if t odd, H=2t-6, M=t-2 in the original window, and K(M)>=t. For an incoming prime q to (t,H), require
    even t: q|H and t=0 mod 2q;
    odd t: q|(H+2) and t=q+2 mod 2q.
Set D=H-q+1. Require (q,D) not in H_X and q to be the smallest eligible label at the exact event time t at D. Put ell(t,D) equal to the last eligible clock strictly below t, intersected with the minimal original start time. Previous arrival times u are exactly in [ell(t,D),t), restricted to roots or possible post-event states. Union F(u,D), filtering original root cutoffs K>=t; optionally record the number of executed high events. Root sets in this union are disjoint by deterministic forward dynamics; horizons strictly decrease in the recursion. This is the previous reverse recurrence with the absorbing key exclusion, using cutoff-tagged root sets so memoization does not depend on a final query time.

To query a stopped key (p,C), enumerate each possible clock time n for p at C up to Kmax, retaining only times where p is the smallest eligible label. Sum F(t,C) over t in the previous-clock interval [ell(n,C),n), filtering K(M)>=n. Do NOT exclude the queried key itself: the source is stopped before executing that event, but it has an actual next event within cutoff. Disjointness across arrival/event times follows from the deterministic first-hit rule and strictly increasing horizon. This recovers the exact stopped-root set and high-depth distribution. The time-free high-block recursion in section 4 is an upper bound, often much larger.

A usable quantitative next proof target, directly for this absorbing problem: bound the total stopped-root mass with >h preceding high selections below (1-epsilon)N on unbounded dyadic windows, with h and tau as in sections 2 and 4. The short-ancestry contribution is already o(N). Alternatively prove a uniform bound on deep cutoff-tagged reverse mass at each candidate key sufficient to prevent any first saturation. The first-hit process has bounded mass on all earlier executed keys, but counting the number of possible reverse predecessor keys times this cap is not a contraction. The required new result must exploit the chronological acceptance intervals and original root constraints in the deep recursion. Neither the geometric moment nor the sieve alone closes that step.

## 6. Exact finite audits and evidence

Two executable Node.js audits, function bodies executed in the current runtime. Both retain original source cutoffs. Integer arithmetic exact in the tested ranges; no randomized sampling.

    node research/min_first_heavy_key_audit.mjs 256 1024 4096 16384 65536 262144 1048576
    node research/min_first_heavy_reverse_audit.mjs 256 1024 4096

First audit: seven dyadic windows, fixed LOW7, caps floor(B/8), floor(B/4), floor(B/2), B, ceil(B log^2 B) (small caps >=2). Independently compares all next events/terminals against literal parity-GCD at X<=1024. At X<=16384 independently replays every original root using the final stop set and checks the exact costs and stopped populations. Checks cap, all-source conservation, exact original cutoff, no-twin tail, geometric stopped-mass bound, high/low cost, and explicit arithmetic budget upper bound using distance to next L multiple. Direct S0 and high-key Skey (p>7) are measured; Skey can be greater than S0 at finite X because of repeated eligible keys. The improved asymptotic bound does not assert Skey<S0 or specify its finite constant.

| X | B | max active high-key mass, cap B log^2 B | stopped at B/8 | stopped at B/4 | stopped at B/2 | stopped at B |
|--:|--:|--:|--:|--:|--:|--:|
|256|43|30|85|65|51|0|
|1024|85|46|232|136|46|0|
|4096|170|121|915|505|121|0|
|16384|339|217|3445|1808|353|0|
|65536|678|376|10978|6093|725|0|
|262144|1355|646|32914|11112|0|0|
|1048576|2710|1595|77221|14372|1432|0|

At X1048576: N524288, cap B/4=677, 20 stopped keys with 14372 stopped roots, largest mass 926, 509916 actual twin terminals, 0 bad. At cap B/2=1355: only one stopped key (p,C)=(197,3835788), mass1432, its root horizons span 15632, 218 of its stopped roots have <=10 previous highs, deepest 82, 522856 actual twin terminals. At cap B: zero stops and all 524288 actual twin terminals. At cap ceil(B log^2 B)=169333, also no stops. R full=730547400, S0=53288322, high Skey=90332564. These are finite diagnostics, not a proof of the asymptotic first-hit target. The smaller caps are intentionally below the asymptotic cap to expose nonempty stop sets. Script and JSON committed/read back exactly at 184d6097f998e42b0f0c55330910d2bf642349e6.

Second audit: all 45 stop-key queries across three caps at X256/1024 (18+27), largest sink for each of three caps at X4096. Checks exact stopped original-root SET and high depth using reverse clock intervals with deduplicated candidate arrival times, memoized root sets, original cutoffs and the exact stop exclusion. Counts at different caps can repeat a root. The actual checked counts are X256:85+65+51=201, X1024:232+136+46=414, X4096:41+79+121=241, hence 856 source-query matches and 48 queried keys. For the largest sink at X4096 cap85, (p,C)=(13,15510), exact mass121; depth cut h=0,1,2,3,4 gives actual stopped-root counts 3,12,17,31,39 vs time-free relaxed counts 4,20,54,103,142. This demonstrates looseness of dropping chronological conditions even at small depth. An initial more expensive reverse implementation timed out before writing; the optimized shared-memo version completed the stated windows and scope. Script and JSON committed/read back exactly at f4405ec8623ca55d21c22af2f70edd7e69c455fc. (No claim of all sinks at X4096 or larger.)

## 7. Status

The extra logarithmic sieve saving is unconditional relative to the previously established per-prime sieve estimate. It relaxes BOTH the full-horizon energy and the first-heavy stopping threshold, and the stopping/short-ancestry inequalities are paper deductions independent of source coalescence. The first-heavy absorption estimate remains genuinely open. The finite data and exact reverse solver expose the deep ancestry that must be bounded, not a proof of its decay. No new branch, no main edits, no Lean kernel proof.
