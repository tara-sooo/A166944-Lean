# Local discovery horizons and depleted-phase ranks at small fresh predecessors

2026-11-25 JST. Continues 668379fcfbfd1ed9d8adfe36758fd29ce97e665e on the SAME research/min-cycle-forest-2026-11-24 branch. New localized stock expectation bound for upward fresh-to-known transitions even when the fresh predecessor is below sqrt(2U), and an exact deletion-rank probability bound for depleted first discoveries. Original mathematical derivation and finite CRT diagnostics. No external search or Lean compilation. Neither arbitrary late small-predecessor transitions nor the full signed peak and actual physical far-coalescence limits are solved.

## 1. Setting

Common independent CRT ghost, finite initial segment or infinite odd prime alphabet. At each selected p the pre-gain g increases by p-1, completed wait w<=2p, signed attained height h=2s-g_post. Fresh means first selection in the original trajectory. The exact tick-history law gives a uniform coordinate pair on the allowed set A_q(s-1) for an unused q before tick s, of size >=q^2-(s-1). Selected-label and quiet-tick history is included; there is no restart of the hazard for already selected primes.

Choose A>=5 with LOW period L=2 product_(3<=ell<A)ell <= log^(1/8) U, A slowly increasing. Consecutive high events q,p have intervening LOW gain d even, 0<=d<L, with LOW peak <=5L. Restrict to the prefix with post-gain<=2U, which contains every positive attained peak, and whose total sum of selected labels is <=3U. Write z0=ceil(sqrt(2U)), and consider fresh q followed by repeated p>Fq with q<z0 and p<z. Use F>=4, z<=2U+1, K>=1 and 0<delta<=1. A qualifying locally exposed q is first selected at s<=K q^2 and has |A_q(s-1)|>=delta q^2. These conditions are checkable just before its first selection, separately for each candidate q, and give hazard <=1/(delta q^2). In particular q selected by q^2/2 automatically qualifies whenever delta<=1/2.

## 2. Time-local selected-stock concentration

Partition the small q range into dyadic bands [R,2R) with R powers of two, R<=z0, and initially restrict q>=L+10 (so R>=L/2). Partition p into dyadic bands [P,2P). For p>Fq necessarily P>F R/2. Put T_R=min(U,ceil(4K R^2)). Assume F^2>=64 K, which ensures p^2>=2T_R throughout such p bands for large U (rounding is harmless). At all ticks through T_R a fresh p thus has hazard <=2/p^2 even if p itself is smaller than z0.

For fixed G integer in [0,2U], define K_s(G,P,R) as in the preceding near-stock note: count p in [P,2P) first selected before s with first pre-gain u_p<=G-P+1 and p | G-u_p+a for some integer a in [R-3,2R+L+1]. For each fixed target and each tick t<=T_R, the pre-gain u is known. Every admissible G-u+a is positive since G-u>=P-1 and R>=1 with P>F R/2 (in the restricted q range it is much larger than 1); also it is O(U). It has at most O(log(2U)/log(2P)) distinct prime divisors >=P. This bound, rather than an absolute constant, is needed when P is below sqrt(2U).

The probability of adding a stock member at a given tick is thus <=C (R+L+1) log(2U)/(P^2 log(2P)). Iterate exponential conditional expectations of the addition indicators through T_R. As in the preceding note, a union over O(U log^2 U) fixed G,P,R triples gives, with probability 1-O(U^-4), simultaneously for s<=T_R+1,
    K_s(G,P,R) <= C1 [log(2U) + T_R (R+L+1) log(2U)/(P^2 log(2P))].     (1)
The event concerns the selected stock through each local time horizon. It does not assume adaptive target G independent of the stock; uniformity is obtained by the union over fixed targets.

## 3. Upward transition expectation with a small locally exposed predecessor

At the fresh q event's pre-gain G, the repeated p was selected previously, at first pre-gain u_p<=G-p+1. The eligibility signs imply
    p | G-u_p+q-1+d+a0, a0 in {-2,0,2}.
Hence p belongs to K_s(G,P,R) before q is selected. For each such p and each of the O(L+1) LOW-gain and sign choices, the residue condition fixes at most one integer q in [R,2R) because P>F R/2>=2R. Filter prospective q by s<=K q^2 and allowed-set size>=delta q^2. These are history-measurable conditions for each candidate. Its fresh hazard is <=1/(delta R^2). Assign a ticket of weight p<=2P. The actual next high event consumes at most one ticket. Conditional expected ticket weight in this band pair is bounded by
    O((L+1) P K_s/(delta R^2)).
Use (1) as a bound on the local measurable stock before the fresh tick, not as a conditioning event in the hazard. On failure of the simultaneous event, actual capped total pair weight <=3U. Sum over at most T_R<=5 K R^2 ticks per R band:
    E W_local <= O((L+1)/delta sum_R sum_(F R/2<P<z)
        [K P log(2U) + K^2 R^3 log(2U)/(P log(2P))]) + O(U^-3).
Here R+L+1=O(R), and constants are uniform for the stated range. The first double sum is O(K z log^2(2U)). For the second, sum 1/(P log(2P)) geometrically to obtain O(1/(F R log(2R))). Then
    sum_(R<=z0 dyadic) R^2 log(2U)/log(2R)=O(U).
For example split R>=U^(1/4) (bounded log ratio) from smaller R (sum of R^2<=O(sqrt U) times log U). Therefore
    E W_local = O((L+1)/delta [K z log^2(2U)+K^2 U/F]) + O(U^-3).        (2)
This bounds p-weights, not just positive heights, for the locally exposed upward pairs in the capped prefix with q>=L+10. For q<L+10 one can use the deterministic bound z times the number of such q, O(z(L+1)), since each fresh q initiates at most one pair. This is already sublinear for our z.

Choose, for sufficiently large U,
    F=log^(1/3) U, K=log^(1/32) U, delta=log^(-1/16) U,
    z=ceil(U/log^(5/2) U), L<=log^(1/8) U.
Then F^2>=64K eventually, and (2) divided by U is
    O(log^(-9/32) U + log^(-1/12) U) = o(1).
Thus a small fresh predecessor q<sqrt(2U) can be handled even when its following repeated p is much larger and its first-selection time is as large as K q^2, provided at least delta q^2 coordinate pairs remain. The special case s<=q^2/2 has no extra allowed-set assumption. This uses the smaller local time horizon in the previously known p stock; using the full U in that stock would not give (2).

## 4. Exact first-discovery depletion rank

For a fixed prime q, condition on ALL coordinates other than q, and common parity. Run the ghost with q deleted through U (including quiet ticks after finite-model termination). At every tick where no label fires or the selected label exceeds q, form the unique coordinate pair of q that would match there along the deleted trace. Enumerate these pairs in order of first appearance, discarding duplicates, say x_1,...,x_M, M<=q^2.

If the actual q pair equals x_j, then its first selection is exactly at the first-appearance tick of x_j: until then the two paths agree, and at that tick q wins the selection. If its pair is absent it is never selected through U. Immediately before that first selection the actual tick-history allowed set for q has size q^2-j+1. This follows directly from the exact history law: only the earlier distinct matching pairs at ticks with no event or a larger winner were excluded. This is an exact identity on the actual path, not an approximation based on total elapsed ticks. Conditional on the other coordinates, the q pair is uniform over q^2 possibilities. Therefore
    Pr(q is selected by U with |A_q(s-1)|<delta q^2) <= delta.             (3)
The event may occur very late, and the bound holds even when U is much greater than q^2. No independence between depletion events of different q is claimed.

In an upward transition with fresh depleted q and repeated p, impose the additional product cap p q<=U H for H>=1. Since each q is fresh at most once, its contribution is bounded by (UH/q) times its depletion indicator. Summing over q<z0 using (3) and the harmonic prime bound gives
    E W_depleted_product <= O(delta H U log log(3U)).                    (4)
For ANY fresh q (depleted or not, arbitrary first time), the smaller product cap p q<=U/H yields deterministic weight
    W_small_product <= (U/H) sum_(q<z0 prime)1/q
                      = O(U log log(3U)/H).                              (5)
Choose H=log^(1/32) U with the above delta. Both normalized bounds tend to zero. In particular (4) reaches the larger product range p q<=U log^(1/32) U for depleted q without any elapsed discovery-time assumption. This does not bound depleted transitions with arbitrary p q; the factor delta alone is not enough when the possible p weights grow much faster than U/q.

## 5. Combined deletion in the signed record-erasure bound

At a repeated high event p use the prior exact preceding-LOW corrected increment a_i=J_i-J_(previous high), J=2s-g_post-6chi. For p>=10L+14 it is positive only when w>p/4, and a_i^+<=2w<=4p. For p<=10L+14 the first-fresh predecessor transitions contribute O(L^2) in total, since q<p/F implies O(L) possible fresh q and a_i^+=O(L). More generally comparable pairs use a_i^+<=O(L+1)p.

Combine:
- comparable p<=Fq after any fresh q: earlier bound O(F(L+1)^2 U/log U)=o(U);
- p>=z: earlier weighted rough-return sieve gives expected positive increment o(U) independently of predecessor;
- q>=z0, p>Fq, p<z: preceding near-stock theorem O((L+1)(z log U+U/F))=o(U);
- q<L+10, p<z: deterministic O(z(L+1)+L^2)=o(U);
- small locally exposed q: (2);
- all small-product pairs and depleted enlarged-product pairs: (4),(5).
The union of these positive increments has expectation o(U), and may be removed once from the earlier signed record-erasure residual; disjoint negative credits remain unchanged. Thus an as-yet-undeleted positive repeated high step immediately following a globally fresh high q must obey ALL of:
    L+10<=q<z0, Fq<p<z, p q>U/H;
    either s>K q^2 or |A_q(s-1)|<delta q^2;
    if |A_q(s-1)|<delta q^2, then p q>U H.
The first-selection tick s refers to q, not to p. Other previous residual criteria still apply (strict record if retained, earlier sieve and chain/rank restrictions). These are necessary conditions, not a claim that the remaining contribution is sublinear. In particular late q with a nondepleted allowed set can still be selected, and depleted q with large product are not estimated by this argument. We have not shown depletion probability tends to zero conditional on arbitrary late discovery. The theorem addresses the small-predecessor entrance gap rather than the entire sparse-record allocation or known-only run. The global signed peak and actual physical far-coalescence remain open.

## 6. Finite diagnostic and persistence

Saved research/min_ghost_small_fresh_local_exposure_audit.mjs and research/min_ghost_small_fresh_local_exposure_results.json, exact remote readback at 71aa99159963814108b78e6704183f3d0ff318ad. Run node research/min_ghost_small_fresh_local_exposure_audit.mjs 256 1024 4096 16384 65536. Fixed pseudorandom common CRT coordinates, finite alphabet <=4U, 96 samples per window except 64 at largest. A5,L6, diagnostic F4,K2,delta1/4. These are finite diagnostic settings, not asymptotic parameter choices; in particular F^2>=64K does not hold for them, and z equals root in these windows. Do not interpret the small sample as a numerical verification of (2) or its constants. The finite-to-infinite coupling error O(1/log U) is asymptotic, not a calibrated finite-sample error.

At every small fresh q calculate the distinct excluded coordinate pairs from the actual tick history (quiet tick ranges are truncated to their first 2q ticks at frozen gain, then any larger winning event tick is added). Check that the actual pair remains and allowed size is positive; record early/late and depleted/nondepleted status. At each locally exposed small fresh q enumerate previously selected p>Fq and exact possible next-high eligibility after LOW gain d<L, check their containment in the near-stock divisor test, and check actual capped upward pairs. The diagnostic counts include p>=z and q<L+10, deliberately to exercise necessary conditions rather than assert applicability of (2). For three fixed backgrounds per U, delete q=3,5,7 respectively, compute the first-appearance sequence, then enumerate every q coordinate pair with others fixed and run the full model. Check actual first selection tick equals the recorded deletion tick (or both absent), first-selection count equals rank-list length, and depleted count <=delta q^2. Total 5*(9+25+49)=415 exhaustive pair cases; actual q-depleted status via the exact rank is measured separately from actual-path allowed-size checks.

At U65536: 3618 executed events,790 small fresh selections,576 with first tick<=2q^2,214 later,64 depleted,565 satisfying both local-time and nondepletion tests. Three actual capped upward pairs, all small and depleted, total p-weight483, all with p q<=U log^(1/32) U. 37356 positivity tests of divisor targets, 2 exact stock checks. At U4096 and U16384 there is one actual locally exposed upward pair each, with p-weights29 and109; both have zero uncorrected positive preceding-LOW increment. These exercise actual ticket coverage even though no analytic-scale asymptotic statement is inferred from them. All structural and exact rank checks pass. No Lean compilation.

## 7. Remaining work

The new local clock horizon extends the earlier large-predecessor estimate below sqrt(2U), and the deletion-rank argument bounds deep phase depletion independently of elapsed time. The residual includes very late small fresh selections with nondepleted phases and depleted selections leading to p q>U H, as well as already-known predecessor steps. Further control of the actual time/exposure relation or direct signed cancellation is necessary. The global signed peak convergence eta->0 and physical far-coalescence bound remain unresolved. No new branch, no main edit, no twin-prime proof.
