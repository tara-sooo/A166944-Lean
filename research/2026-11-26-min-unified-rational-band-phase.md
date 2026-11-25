# All-mass rational-band transition halos and low-index adjusted-phase exclusion

2026-11-26 JST. Continues [533da8c91534](https://github.com/tara-sooo/A166944-Lean/blob/533da8c915345b919e386426d40b5eb961e14024/research/2026-11-26-min-unified-rotation-return.md) and [09559cdebe9d](https://github.com/tara-sooo/A166944-Lean/blob/09559cdebe9d44a0a2b5f6a64299e49eeaa1453a/research/2026-11-25-min-unified-deficit-packing.md). Independent heads checked unchanged from previous turn: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. Integrates the prime-root broad close-prime shifted CRT and prime-pair upper sieve with the stable-heavy adjusted arrival-phase identity. New all-mass whole-sublist clock payment for short-background transitions between distinct selected primes near bounded-coefficient rational ratios. Includes a nonhigh successor and any intervening completed selected labels. A new necessary low-index phase-drift condition for the surviving high transitions, with RESET-to-RESET kept separate. No Lean kernel check, no full clock contraction, twin-prime infinitude open.

## 1. Setup and new rational-band definition

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root gain-stopped MIN paths and all original terminal snapshots unchanged. Natural HIGH means p>=Q, r(C)>p/sqrt(log p). The original selected gain is p-1 and actual waiting time w<=2r(C)<=3(p-1). For an actual completed event at C the original tag population is O(H/u): all original prime origins lie in an interval of length H/2 and the uniform upper bound for primes in such an interval applies. No bound on synchronous mass beyond this original source-locality cap is required.

Fix integers K,J,L>=1, eventually
    K=floor(u^(1/2)), J=floor(u^(1/2)), L=floor(u^(3/4)).
For large X, K,J,L << Q. A rational-band transition has an actual initial HIGH event of selected p at C and a later ACTUAL completed event of selected q at A=C+p-1+e, with total intervening selected gain e even, 0<=e<=L, and
    |a p-b q|<=J,     1<=a,b<=K.                              (1)
The successor q need not be high or the next natural high, and e need not be comprised of LOW labels. No restriction on the number of intervening completed edges is necessary. We mark the entire original sublist from p through q inclusive, including all intervening waits. The definition uses full original paths before any accounting deletion.

The labels are distinct: if q=p, then from p|(C+sigma), p|(A+tau) one obtains p|p-1+e+tau-sigma, which is p plus a nonzero odd integer of absolute value <=L+3<p. Here sigma,tau in {-1,+1}. This is impossible. From p>2J and a>=1, (1) implies bq>=p-J>p/2, hence q>=Q/(2K) and both primes have logarithms u-O(log u). Also if ap=bq, distinct primes imply q|a and p|b, impossible for K<Q/(2K) eventually. Thus (1) has nonzero integer c=ap-bq. Divide a,b,c by gcd(a,b); a,b remain positive <=K, |c|<=J, c!=0 and gcd(a,b)=1. This reduction is important to avoid overcounting unnecessary common coefficient factors in the analytic bound.

## 2. Uniform prime-pair sieve on a rational band

For fixed coprime a,b<=K and fixed nonzero signed c with |c|<=J, every integral solution of a p-b q=c has the parameterization
    p=p0+b n,   q=q0+a n.
Restrict both p,q to primes in [Q/(2K),B], and in addition p>=Q. In a dyadic subinterval V<=p<2V the integer n values range over an interval of length O(V/b+1). Intersecting with the other range restrictions can only shorten it. For any prime l not dividing 2abc, the two forms have nonzero coefficients mod l and two distinct forbidden residue classes mod l, because their determinant is c!=0. Drop the primes dividing 2abc. They have product of distinct primes at most |2abc| and log product O(log u), uniformly. This is a two-form sieve in n, not an assumed distribution of prime pairs.

For completeness use exactly the elementary Selberg construction in [four-form rough-landing sieve](https://github.com/tara-sooo/A166944-Lean/blob/0fda077cd533a8f0cfddb8104e683e1c1ef549e2/research/2026-11-25-min-unified-rough-pair-isolation.md), with two forbidden residues instead of four, and z=floor(B^(1/40)). For squarefree d from good primes <=z put g(d)=prod_(l|d) 2/l and h(d)=prod_(l|d)(1/g(l)-1). The finite quadratic inversion weights, normalized by G=sum_(d<=z)1/h(d), give count <= V_n/G+O(z^8) on an interval of n-length V_n. The same proof gives G>>u²/ell²: take primes <=z^alpha for a sufficiently small fixed alpha, include each independently with probability 2/l in the normalized product expansion, then Markov on log d keeps at least half the weight with d<=z. Mertens gives the unrestricted product >>u². The loss from primes dividing 2abc is O(ell²) by comparison to the full product for l<=u² and the reciprocal sum O(log|2abc|/u²) for the larger exceptional factors. Both actual primes exceed z, so they avoid all the sieving primes. Since V>=Q/(2K) and b<=K, V/b>>B/u², the O(z^8)=O(B^.2) term is absorbed into V ell²/(b u²). Therefore
    # p in [V,2V), p,q prime with ap-bq=c
        << V ell²/(b u²).                                   (2)
This holds uniformly even if the interval intersection is very short: use the full dyadic interval length in the upper bound. Swapping roles gives the analogous estimate for q in a dyadic interval W<=q<2W with denominator a.

There are O(ell) dyadic subintervals covering [Q/(2K),B]. Dividing (2) by V and summing, and using the swapped estimate for 1/q, gives the weighted bound for this fixed triple:
    sum_(actual prime solutions) (1/p+1/q)
        << ell³/u² * (1/b+1/a).                              (3)
Summing over coprime coefficient pairs and signed nonzero c, enlarging to all coefficient pairs in the sum of weights, yields
    sum_(distinct prime pairs in (1)) (1/p+1/q)
       << (J+1) K log(2K) ell³/u².                           (4)
This uses sum_(a,b<=K)(1/a+1/b)=O(K log(2K)), not K² with a constant weight. The estimate counts both p>=Q and the relaxed q>=Q/(2K) range; it does not require q to be natural HIGH. It includes the simpler close-label case a=b=1. No prime-pair asymptotic or lower bound is invoked.

## 3. Spatial CRT and whole-sublist payment for arbitrary mass

For fixed distinct prime p,q, signs sigma,tau and e, the congruences
    C+sigma=0 mod p,
    C+p-1+e+tau=0 mod q
determine one residue class mod pq. Since pq<=B²=O(X), there are O(X/(pq)+1)=O(X/(pq)) possible C in the full original O(X) horizon interval. Count all integer C, dropping evenness, high roughness, and actual realizability of the intervening word. There are O(L+1) offsets, and a constant number of signs. Thus the total weighted relaxed spatial support is bounded by
    sum_(keys C,p,e,q,sigma,tau) (p+q)
       << X (L+1) (J+1) K log(2K) ell³/u².                   (5)
The same key can occur on many different original paths; we have not yet used any multiplicity estimate.

Every actual sublist from initial p through final q inclusive has total wait at most
    2p+3e+2q = O(p+q),                                      (6)
since e<=L=o(Q) and p>=Q. For a fixed key at most O(H/u) original tags visit its initial horizon. On each original tag its events have strictly increasing horizons, so at most one interval per key per tag. Pay all waits in the UNION of marked original sublists; overcounting overlaps is an upper bound by the sum of (6) over all actual incidences. By (5),
    W_band << (H/u) X (L+1)(J+1)K log(2K) ell³/u²
           = O(NT ell^4/u^(1/4))=o(NT).                     (7)
With the chosen exponents 3/4+1/2+1/2=7/4, log(2K)=O(ell). More generally the same proof works for fixed power exponents on L,J,K whose sum is <2, provided each is nonnegative and the large-X geometric conditions hold. The implied constants may depend on the fixed exponent choices. This is an all-mass linear deletion; it does not use Mstar, a stable-strand assumption, any bound on pair energy, or an arithmetic estimate on original root correlations. The final q can be nonhigh, and all intermediate actual waits are paid. If a later q has already been paid, mark the original interval anyway but sum only the unpaid union. No recursive extension of the halos.

In particular, any surviving HIGH incidence (even in the very thick sector) cannot have ANY original completed later label q with gain e<=L between its own jump and q and satisfying (1). This remains true if the q incidence itself has been removed by a different mask, since (1) is defined on original paths. If two consecutive original HIGH events have e<=L and |p-q|<=J, their full sublist is paid. The new theorem also pays bands near ratios a/b not near 1. It is different from the prime-root close-prime diamond halo which used a small difference between prehorizons on two different paths; here A-C=p-1+e can be of order B on ONE original path.

## 4. Integration with adjusted arrival phases

For an actual selected event p at C with exit v, posthorizon D=C+p-1 and exit parity s=v mod2, write adjusted phase
    phi=2v-D-6s=2p k.
This exact divisibility follows from p|D+2s and p|v-2s. For p>=5, k is a nonnegative integer: d=2v-D>=0, so phi>=-6, and a negative nonzero multiple of 2p is impossible. RESET means k=0 (including both parity classes). The two old branch results used this identity for actual recorded arrivals and pairs. Apply it here to two actual selected events on one original path, with respective phase indices k,l.

Take an initial natural HIGH p and a later natural HIGH q with intervening gain e<=L. They are distinct by section 1. Assume both indices <=K, and |phi_p-phi_q|<=2J. If exactly one index is zero then the difference is at least 2Q>2J, impossible. If both are positive then |kp-lq|<=J, the zero equality is impossible for K<Q, and (1) applies. Their entire original sublist is already paid by (7). The same conclusion is valid with q>=Q/(2K) not necessarily HIGH, since then q>=5 and both labels exceed K,J eventually. In fact for the nonhigh extension one only needs q>=5 and q>J for the one-zero argument, and q>K for the nonzero equality argument; the rational relation itself forces q>=Q/(2K).

Consequently on any surviving HIGH incidence with a later actual HIGH event whose intervening gain is <=L and whose two phase indices are <=K,
    either both are RESET (k=l=0),
    or |phi_p-phi_q|>2J.                                    (8)
No claim that RESET-to-RESET is rare; zero-zero does not give a nontrivial rational relation. If d_post<=2Q K for both HIGH events then both indices <=K, so (8) applies directly in that common deficit slab, which has size Theta(B/sqrt(u)). More generally the per-label condition d_post<=2pK+6s suffices for its own index. This connects the previous deficit-adaptive mass constraint with an all-mass arithmetic exclusion, rather than requiring the mass cap for both constraints.

An exact drift restatement uses e and actual elapsed gap W_gap after initial p through the prevertex of q (excluding both high waits), and q's own wait w_q. Since D_q-D_p=e+q-1,
    phi_q-phi_p=2(W_gap+w_q)-(e+q-1)-6(s_q-s_p).             (9)
Thus, except for the two RESET endpoints, the later event-plus-gap elapsed time must differ by >J from the adjusted half-gain (e+q-1)/2+3(s_q-s_p), provided both phase indices <=K, the initial hit survives, and e<=L. This is an absolute drift condition, not a fixed-proportion deviation or a signed drift. Total variation alone does not force a contradiction at the new J scale.

## 5. Exact residual target

Insert (7) by priority into the previous original actual-clock ledger; the previous lower bound under the no-twin hypothesis and sufficient condition
    liminf_(dyadic X -> infinity) (A_rem+L_rem)/(NT)<1/2
remain unchanged, on smaller exact residual clocks. A_rem denotes remaining non-HIGH waits, L_rem remaining HIGH waits; the L used as a short-background threshold in this note is unrelated to L_rem. The all-mass mask applies also to previously unresolved thick cohorts. It is not a global bound on all short-background transitions: most pairs need not satisfy (1), and (8) leaves high phase indices, RESET-to-RESET, and large positive or negative drift. Nor does it control arbitrary long intermediate gaps or the full non-HIGH clock. No full contraction or proof of twin-prime infinitude has been obtained. No external novelty claim, no Lean compilation. Main and independent branches unchanged.

## 6. Finite audit

Source [min_unified_rational_band_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/4fde3fb1abb19687abdb22250b3f7e5db05b9363/research/min_unified_rational_band_audit.mjs), commit 4fde3fb1abb19687abdb22250b3f7e5db05b9363, exact remote readback. The function was executed in the available ECMAScript tool runtime, not a separate Node process. Reproduce:
    node research/min_unified_rational_band_audit.mjs 256 1024 4096 16384 65536

Five normal finite tests and one stress test, all passed. T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), high r>3 and r>p/2. Normal K4,L16,J8; stress K8,L32,J16 at X65536. To preserve the proof's finite geometry restrict initial p>L+3,p>2J,p>K. The exact relation test excludes zero and uses coprime positive coefficients. The finite audit checks the nonzero band directly; the large-X impossibility of a zero equality at q<=K is not assumed for every finite candidate. For phase implications both endpoints HIGH and positive indices are checked on actual examples; the audit explicitly checks the one-zero inequality only when the later p>J. Parameters differ from the analytic ones. The new mask is isolated, not cumulative with previous masks.

Checks actual MIN with literal per-tick gcd for small X (431 and1239 comparisons), actual adjusted phase for every completed event, relaxed spatial keys on actual initial high centres, positive reduced coefficient relation, exact CRT congruences, independent prime pair enumeration by (a,b,c,p), actual sublist coverage, exact intervening gain, per-sublist actual wait upper bound, exact union cost and partition, and low-index phase implications for next actual HIGH with short background. No numerical test of the analytic sieve constants. The both-HIGH sublist union statistic is a subset of the whole marked clock, not an additive second mask.

| X/mode | raw HIGH | full marked actual clock | marked HIGH | remaining HIGH | actual rational matches | low-phase positive-index checks |
|---:|---:|---:|---:|---:|---:|---:|
|256|1753|454|383|1370|18|0|
|1024|3908|2934|2463|1445|97|2|
|4096|37458|26734|20972|16486|633|32|
|16384|195474|73109|57045|138429|966|55|
|65536|1380549|161512|140307|1240242|854|30|
|65536 stress|1380549|828613|693689|686860|5818|116|

Largest normal: 5709 tags,140255 completed events and exact adjusted phase checks, raw all clock2395330. 1396 initial high centres,3740 relaxed spatial keys including1822 with q<Q,575 distinct represented rational prime pairs checked against1209 independently enumerated pairs. Actual matches854 (273 later HIGH,581 later nonHIGH),806 with |p-q|>J. Union2730 marked events, high140307 and other21205, total161512<=sum actual matching sublists165276<=relaxed support cost11845398. For short-gap next natural high with both phase indices<=K: positive-index small-drift30 actual matches (initial high clocks6004), both RESET322, one zero259 (overlaps large drift), large drift890. This exercises the phase implication nonvacuously and also shows the RESET exception is real.

Largest stress: 28098 spatial keys,2965 represented distinct pairs,5818 actual matches including5644 outside the simple |p-q|<=J band,1340 later HIGH and4478 later nonHIGH. 116 positive-index small-drift checks,454 both RESET. Marked full union828613 including693689 HIGH and134924 nonHIGH, 20702 marked events. Finite percentages are diagnostic only; (7) is a paper upper bound in the asymptotic regime.
