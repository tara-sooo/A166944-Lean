# Relative-clock occupation energy: bounded pair separation and quantitative twin certificate

2026-11-25 JST. Continues the full-horizon energy and Selberg-source research at 73458de887def94d00eeaf2d2d3b9c59a44b8137 and 5b2a865603bc58af8afaa21252147407bb29275c. New exact fractional-clock occupation and short-slab localization, finite quantitative certificate. No asymptotic short-slab energy estimate has been proved. Twin-prime conjecture OPEN; no new Lean compilation.

## 1. Correction to the comparison of sufficient scales

The original all-root full energy E=sum r(C)W(C)^2, R=sum r(C)W(C) and S0=sum r(C) satisfy R^2<=S0 E. The established sieve S0=O(X B/log^2 B), B^2=Theta(X), together with R>=(9/32-o(1))X^2 in a no-twin window implies immediately that

    E=o(X^2 B log^2 B)

on unbounded dyadic windows suffices directly, with ALL roots. The earlier O(X^2 B log B) was a convenient stronger per-band target, not the weakest scale supplied by Cauchy. Thus the Selberg reduction at 5b2a865 does not by itself improve the raw energy target: it adds a signed discrepancy condition at the same natural raw scale. Its mathematical identities remain valid, but the claimed logarithmic improvement over the direct method is not an independent advantage. In particular do not require signed far-pair cancellation if the raw bound at this scale can be obtained. The prime-root no-injection-merger result remains valid, as does the possibility of separate bounds that exploit primality.

## 2. Exact fractional occupation in a relative-time slab

Keep the ORIGINAL canonical MIN trajectories of all odd M in [X,2X), N=X/2, s=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). Use the established invariant C<=2t and the same lexicographic clock competition. Let 0<=a<H<=min_M(K(M)-s), h=H-a. Choose integer endpoints. For a physical state (t,C) visited by M, its waiting interval ends at the next selected event u or at its original cutoff K(M) if no event occurs before cutoff. If r(C)=0, both neighbors are prime because C<7X and every composite neighbor has a factor <=B. Stop occupation there. If r(C)>0, then the waiting interval has length <=2r(C), including the clipped non-twin terminal tail: the next unrestricted eligible clock is within 2r(C).

For an actual waiting interval [t,u) with r(C)>0 put

    w_M(C) = |[t-s,u-s) intersect [a,H)|/(2r(C)).

It is zero if the state is not visited or there is no overlap; r=0 also gives weight zero. Each horizon is visited at most once, so 0<=w_M(C)<=1. This counts PARTIAL waits, unlike pre-event incidence counts, and includes a non-twin terminal quiet tail through its cutoff. The end H always lies within the individual cutoff. Set

    U(C)=sum_M w_M(C), R_[a,H]=sum_C r(C)U(C),
    E_[a,H]=sum_C r(C)U(C)^2.

Let L_M be the relative time to the terminal twin state, or K(M)-s for a non-twin terminal. Then exactly

    2R_[a,H] = sum_M max(0,min(L_M,H)-a) <= N h.           (1)

If all original trajectories fail to reach a twin before H, the right hand side is Nh. If L=number of roots with L_M>=H, then Lh<=2R_[a,H] in all cases. With the full horizon sieve S0 and Cauchy,

    L <= 2 sqrt(S0 E_[a,H])/h.                            (2)

Consequently the finite strict certificate

    4 S0 E_[a,H] < (N h)^2                               (3)

ensures at least one actual twin reached at relative time <H. This has no extra 2B quiet-tail loss, even at H comparable to B. It is a different measure from R and E of full pre-event incidences.

Quantitative form: a twin terminal at time t=s+ell with ell<H has 0<=C-C0<=2H+6 by the invariant. For a fixed terminal C, all such original M lie in an interval of length H+3; there are at most m_H=floor((H+3)/2)+1 odd roots in it. A terminal twin pair is uniquely specified by C. Thus the number of distinct twin pairs reached before H is at least

    max(0, ceil((N-2 sqrt(S0 E_[a,H])/h)/m_H)).             (4)

Every pair has smaller prime >=2X-1. In particular if 4 S0 E_[a,H]/(Nh)^2<=rho<1 on unbounded windows and H=o(X), this yields a growing number Omega(X/H) of distinct twins per such window, not merely one.

## 3. A genuine geometric restriction on the remaining pair estimate

At any C with w_M(C)>0, the waiting state started at a time <s+H, hence

    0 <= C-(2M-2) <= 2H+6.

If w_M(C)w_M'(C)>0, both roots are in the same interval of length H+3. Therefore the pair kernel

    K_[a,H](M,M')=sum_C r(C) w_M(C)w_M'(C)

is IDENTICALLY ZERO whenever |M-M'|>H+3, independently of the later full paths. This is an unconditional support restriction on the short-slab energy. No long-horizon coalescence is included.

For |M-M'|<=d, including the diagonal, each M has at most 2 floor(d/2)+1 possible odd M'. Since w<=1, the ordered near-pair energy is at most

    E_near <= (2 floor(d/2)+1) R_[a,H] <= (d+1)Nh/2.     (5)

Choose H>=B, h comparable to H (e.g. a=floor(H/2)), and d=floor(H log^(2-epsilon) B/B) for fixed 0<epsilon<2. Then (5) is

    O(X H^2 log^(2-epsilon) B/B + XH)
      = o(X H^2 log^2 B/B).

All pairs beyond H+3 have exactly zero energy. By (3) and S0=O(X B/log^2 B), the only required estimate in this alternative route is

    sum_{d<|M-M'|<=H+3} K_[a,H](M,M')
           = o(X H^2 log^2 B/B)                         (6)

on unbounded windows (with h comparable to H). A sufficiently small constant in place of little-o also works, depending on the sieve constant. In particular H=4B, a=2B, d=Theta(log^(2-epsilon) B) suffices. This localizes the original problem to root separations between a power of log B and O(B), with only the first 4B relative clock ticks. This is NOT a proof of (6), and the needed scale is smaller than the original full-horizon scale because only O(B) elapsed time is used. The fractional weights and distance support are real unconditional changes; the new asymptotic estimate is still open.

For a local source block of span O(H), the reachable horizon range also has length O(H). The same dimension-two upper-bound sieve as the full-horizon S0 argument, taking z=floor(B^(1/4)), yields S0_block=O(H B/log^2 B) uniformly for H>=B: the small-r term is O(H z); the rough count is O(H/log^2 B) since the usual O(z log(2z)) remainder is negligible. Thus (3) applies to a single source block using its own N_block and S0_block. A proof on one block of span comparable to H on unbounded windows would already suffice. No assumption of uniform ancestor fibres or independence is used.

## 4. Actual finite audit

Standalone ECMAScript research/min_clock_prefix_energy_audit.mjs, exact readback at 276605724b2a8c616c3fc83b63d90fa2ff6781d0, blob 7a53a871b56e8296206b471b5f9b8ccbd72b6d46. Run:

    node research/min_clock_prefix_energy_audit.mjs 256 1024 4096 16384 65536 262144

Executed the actual JS function in the available JS runtime on all six windows, not a separate Node invocation. It replays the original full trajectories to collect fractional prefix and half-prefix slab occupations, with 6140 independent literal per-tick parity-GCD checks. It verifies the invariant, the bound on waiting intervals including non-twin terminal tails, the exact per-root integer slab live time, weight/support inequalities, near-pair upper bound, Cauchy, and certificate (4) against distinct terminal twins. The sliding source window counts near pairs with d=floor(H log B/B), both orders plus diagonal, evicting exact prior occupations by replay. The fractional energy and certificate tests use floating point with tolerances, not exact rational arithmetic or Lean.

For a=2B, H=4B, h=2B, let rho=4 S0 E_[a,H]/(Nh)^2. Rounded values:

| X | B | rho | roots reaching twin before H | distinct reached twins | guaranteed by (4) |
|--:|--:|--:|--:|--:|--:|
|256|43|0.589912|123|14|1|
|1024|85|0.007032|512|45|3|
|4096|170|0.191981|1991|116|4|
|16384|339|0.082828|8087|357|9|
|65536|678|0.069611|32646|1156|18|
|262144|1355|0.055874|130793|3789|37|

At X=262144, all-source events=3946588, S0=9566471, N=131072, h=2710, R_[2710,5420]=2373997.5, E=184229117.19305515, near with d=28 is approximately 20.56 million, and middle energy approximately 163.66 million. 279 roots have not reached twins by H. For [0,4B), rho=0.257499, E=3396114622.93 and certificate guarantees 24 distinct twins. For [B,2B), rho=0.588858, 5034 still live and 23 guaranteed. All these tests are finite, and use actual MIN trajectories; observed termination is not an asymptotic survival estimate. Unlike the earlier late-gain T=B log^1.5 B audits, the [2B,4B) slab is nonempty on all six windows, though the small finite live mass is already mostly terminated.

## 5. Next mathematical target

Prioritize the actual short-slab middle-separation estimate (6), not further sufficient-condition reclassification. Relative-time support permits local source blocks of span O(B), with all trajectory history needed only up to 4B ticks. Count the actual paired source masses in that region, retaining partial waiting times. Test large-B survival and distinguish which fraction of middle-pair energy comes from shared physical states vs different arrival times. A bound on the signed Selberg discrepancy is not needed for this raw-energy route. No uniform bound for the middle pairs or proof of twin infinitude has been achieved. Main untouched.
