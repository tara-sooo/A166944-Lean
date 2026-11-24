# Terminal eligibility obstruction and weighted small-alphabet comparison at fresh landings

2026-11-25 JST. Continues 18e38b007dcb83e3519db42aa1811128eddee5bc on the SAME research/min-cycle-forest-2026-11-24 branch. Original mathematical deductions from the CRT coupling, using the standard Mertens and Brun–Titchmarsh inequalities, and finite exact/seeded checks. No Lean compilation. Important negative result: the previous fixed-power all-short-suffix sufficient condition cannot hold. No complete twin-prime proof.

## 1. Terminal eligibility product: a two-sided cutoff lifetime comparison

Use the common CRT probability space and finite LOW ghosts of the preceding notes, with all coordinates initially independent across odd primes and common clock parity. For 5<=P<z, let tau_P,tau_z be their final event times, including zero for an initially terminal state. All event sequences are frozen after their terminal times. Let A(v)={tau_P<=v}; let E be the event that no added prime P<=p<z is eligible at the terminal horizon of the P-ghost (regardless of its time phase). Conditional on all P-ghost coordinates and parity, that terminal horizon is fixed. Each added prime has exactly two eligible initial horizon residues, so
    Pr(E | P-ghost coordinates, parity)=product_(P<=p<z prime)(1-2/p)=:W(P,z).
Consequently Pr(A(v) intersect E)=Pr(tau_P<=v) W(P,z), exactly. No assertion of independence of visited adaptive horizons is made: the reference path here does not involve any added coordinate.

By the earlier finite-time insertion coupling, the probability of a difference between the two selected event histories through integer time v is at most v sum_(P<=p<z)1/p^2. On agreement through v, {tau_z<=v} equals A(v) intersect E. For the forward implication, if the z-ghost has terminated by v then its last state is shared by the smaller ghost. It has no eligible prime <z, hence also none <P; the smaller ghost must have terminated there, and every added prime is ineligible. For the reverse implication, the shared P-terminal state has no eligible prime in either alphabet, so the z-ghost also terminates there. A small ghost that happens to have no event by v but still has an eligible prime scheduled later is NOT counted as terminal.

Thus the following unconditional estimate holds:
    |Pr(tau_z<=v) - W(P,z) Pr(tau_P<=v)|
       <= v sum_(P<=p<z prime)1/p^2
       = O(v/(P log P)).
This is a comparison of full lifetime distributions, not just of event histories. Unlike an approximation that ignores the frozen tail, it includes the possibility of an added prime that is eligible at the terminal but whose next clock is much later than v.

Standard Mertens estimates imply, uniformly as P->infinity and z>=P,
    W(P,z)=(1+o(1)) (log P/log z)^2.
For example write (1-2/p)/(1-1/p)^2=1-1/(p-1)^2; the product of these correction factors over p>=P tends to one uniformly, and the ratio of Mertens products gives the result. Use the usual upper prime-count estimate for the reciprocal square sum. These standard analytic-number-theory inequalities are not new conjectural assumptions.

## 2. Consequence: a short power-scale lifetime condition is impossible

For any fixed 0<alpha<1, set v=floor(z^alpha), P=max(5,ceil(z^alpha)). The error is O(1/log P)=o(1), and
    Pr(tau_z<=z^alpha)
      =(alpha^2+o(1)) Pr(tau_P<=floor(z^alpha))+o(1)
      <= alpha^2+o(1).
In particular
    liminf_(z->infinity) Pr(tau_z>z^alpha) >= 1-alpha^2.
More generally for v=v(z)>=1 with log(2v)/log z ->0, choose P=max(ceil(sqrt(log z)),ceil(v),5) (eventually P<z). Then P->infinity, log P/log z->0, v/(P log P)->0, so Pr(tau_z<=v)->0. These bounds do not supply an upper bound on long lifetimes; they are genuine lower bounds on their frequency. They do not contradict D_z/(z log z)->0 in probability: D_z<=2 tau_z is one-sided, and the scales here are smaller than z.

Apply the power-scale result to the previous quiet-gap reduction with z=ceil(U^theta), fixed 2/3<theta<1, v=floor(U^(3theta-2) (log U)^(3/2)). Its event BadTime includes the initial z-ghost lifetime exceeding v. Since log v/log z -> alpha=3-2/theta in (0,1), choose P=max(5,ceil(v)) directly in section1, obtaining
    liminf Pr(BadTime) >= 1-(3-2/theta)^2 >0.
At theta=4/5 this lower bound is 3/4. The still shorter earlier choices v=U^rho with rho<3theta-2 have an at least equally strong positive lower bound. Therefore the previous all-short-suffix sufficient hypothesis with fixed theta cannot be established, even before considering any fresh landing. The mathematical conditional implication in the earlier notes is valid, but its required asymptotic condition is impossible for those parameters. We should not pursue it as a sufficient route at fixed powers. This is a substantive correction to the proposed research direction, not a disproof of the clipped-height condition or of twin primes.

A useful general formulation for the next task is
    F_z(v)=W(P,z)F_P(v)+O(v/(P log P)),   F_z(v)=Pr(tau_z<=v).
The comparison is informative whenever v=o(P log P). It does not provide the value of F_P(v) in the regime P comparable to v/log v, where the needed upper tail actually lies. It suggests studying amortized time across multiple low suffixes and more carefully chosen time scales rather than forcing EVERY suffix to be short on a sub-z power scale.

## 3. Weighted candidate comparison for a short continuation after a fresh high event

This separate theorem addresses the prior terminal-support problem for short actual continuations; it is not a fix for the all-short hypothesis. Keep U a time horizon, z>=11 with z^2>=4U, 1<=v<=U, P>=5, P<z, and
    M=product_(3<=p<P prime) p <= z^(1/4).
Reveal all primes <z at time zero as before. At prehistory before tick s<=U, with relative pre-horizon g and common parity, consider every unused candidate fresh q>=z. Define the two counterfactual continuations from (s,g+q-1), using alphabets <P and <z respectively, observed through elapsed time v, with frozen tails. The <P event record of relative gains/times depends only on q mod M, since the candidate starting horizon shift is even, and all low eligible residues and time clocks are determined by these coordinates. Here 2M is the even-horizon period. For each residue a in the units mod M and each added p in [P,z), a first interference can only occur at a possible p clock among the next v ticks. Along the corresponding <P reference trace, at such a tick the match condition is
    q = sign - c_p - g + 1 - d_a (mod p),
where d_a is the reference relative gain BEFORE this tick and sign is determined by clock parity. This is a single residue class mod p for fixed a and tick. A tie with a smaller prime cannot create interference; counting all potential clocks only enlarges the bound. Combine it with q=a mod M by CRT (p not dividing M). These restrictions are measurable from the prehistory. They do not assert independence of the q-specific low suffix and q.

For actual selection of an unused q at tick s the exact history law bounds its conditional probability by 2/q^2, even with low coordinates revealed. We can therefore estimate the total probability weight of these CRT classes, not their unweighted number of terminal offsets.

For P<=p<=z^(1/4), the modulus m=Mp<=sqrt z. Only unit classes modulo m can contain a prime q>=z. The standard Brun–Titchmarsh upper bound in an interval of length D>=z is O(D/(phi(m) log(D/m))) for a coprime residue. In the dyadic intervals [2^j z,2^(j+1)z), m<=sqrt z<=sqrt D, so this gives weighted sum over the infinite class
    sum_(q>=z prime, q in class mod m) q^-2
       <= O(1/(z log z phi(M)(p-1))).
A class with residue zero mod p contributes nothing because q>p. Sum over the at most phi(M) unit classes a; for a fixed possible p clock the total is O(1/(z p log z)). This is uniform in the actual adaptive prehistory, and uses no equidistribution hypothesis or lower bound for primes in progressions.

For z^(1/4)<p<z, use the elementary integer bound on an arithmetic progression mod Mp: sum_{q>=z in class} q^-2 <= z^-2+1/(Mp z). Sum over at most M classes a to obtain O(M/z^2+1/(pz)) for each possible p clock. This is where large moduli are handled without Brun–Titchmarsh.

To sum over s, note that each revealed p has at most two possible clock residues mod 2p. The number of pairs (s,j) with 1<=s<=U,1<=j<=v and a possible p clock at s+j is O(v(1+(U+v)/p))=O(Uv/p) since p<z<=U and v<=U. This is pathwise, independent of the prior trajectory and time phase. Multiply by the uniform conditional weighted CRT bounds and sum over p. The expected number, hence probability of ANY actual fresh high event through U whose two counterfactual continuations differ through v, is
    O( Uv/(z log z P log P)
       + Uv M/z^2
       + Uv/(z^(5/4) log z)).
For the middle term use sum_{z^(1/4)<p<z}1/p=O(1) by Mertens, and for the last use the reciprocal-square upper prime-count bound. The estimate holds uniformly for a finite upper alphabet or the infinite ghost. The comparison concerns counterfactual LOW paths; combining with the earlier known-clock guard and fresh-interference bounds gives protection against actual high interference as well, if those errors vanish. It is not an estimate on how many of the continuations actually terminate by v.

## 4. One regime eliminating terminal support for short ACTUAL suffixes

For example take
    z=ceil(U/(log U)^(5/4)),
    v=floor((log U)^(3/4)),
    P=max(5,floor(c log z)),
with a sufficiently small fixed c>0, so M<=z^(1/4) by Chebyshev. Then all three terms in section3 are o(1) (the first is O(1/log log U)). The existing initial cutoff coupling through v is also o(1) since v/(P log P)->0. The previous clock/fresh interference bounds vanish because v is only polylogarithmic and z is near-linear in U. Expected fresh high count through U is bounded by O((log U)^(1/4)), not necessarily tending to zero; thus this is not just deleting every fresh high event.

Outside the new comparison exception, if the ACTUAL candidate's <z continuation finishes within v, it has agreed throughout with the <P continuation and both terminate at that state. The even-period barrier implies its terminal gain d<2M. This restricts only offsets of the realized short continuation, not the support of all hypothetical q. The new high q cannot be eligible there, since d<2M<z-1 eventually. Previous known high p can reactivate only if q belongs to one of O(M) classes mod p (sum over all even d<2M and signs). The earlier integer progression bound and E K_s=O(s/(z log z)) then give probability O(M U^2/(z^3 log z))=o(1) for ANY such bad short terminal through U. Even if one uses the previous more conservative own-label term O(MU/z^2), it also vanishes.

Consequently, with probability 1-o(1), every fresh high event through U whose <z suffix completes by v has a clean terminal (no low label and no known high label eligible), and that suffix agrees with the actual full process through termination. No separate bound on the infinite hypothetical endpoint support M_s(v) is needed in this regime. This is an unconditional short-suffix statement. It is NOT a proof that sufficiently many such completions occur. In fact section2 implies the initial z-ghost almost surely does NOT finish by this polylogarithmic v in the asymptotic limit. Thus imposing all-shortness here would be worse, not a way around the negative theorem. The new weighted estimate can instead be used as a local prefix comparison within a different time-amortized argument.

## 5. Finite verification

Saved research/min_ghost_terminal_eligibility_product_audit.mjs and results JSON, exact remote readback at c9da2e17ee20c0a37482812db691f8ebf3bc32e6. Enumerate full even-horizon/time rectangles for upper cutoffs z=7,11,13 (450,22050,2668050 states), smaller P=5,7,11 as applicable, and v=4,8,16,32,64. Compute complete deterministic traces in both alphabets, added-prime terminal eligibility, first divergence tick. Check for EVERY state that off divergence through v the upper-terminal event equals the smaller-terminal plus no-added-eligibility event. Check exact aggregate product count, symmetric difference <= divergence count, and divergence <= v sum reciprocal squares (floating tolerance only for products/ratios). For z13,P11,v8: 1454541 phases have lower tau<=8, 1190079 also have no extra eligibility, 1212802 have upper tau<=8; 144510 diverge through8, 43969 disagree on the two terminal tests. The exact product event probability .4460482375 and upper probability .4545649444 differ by .008516707, below the union bound .0661157025. In addition 200989 lower-terminal phases have added eligibility despite no divergence through8. This is precisely the frozen-tail obstruction the new theorem includes.

Saved research/min_ghost_weighted_small_alphabet_audit.mjs and results JSON, exact remote readback at 8ccf775830b18d64ccb6bc0b291a99749983140e. At each Y53,199,397,797,1597 take256 seeded shared CRT samples, finite V=8Y, U=floor(Y sqrt(logY)), z=ceil(U^.8), P7 or11, v=max(4,floor(sqrt z)). These are diagnostics, not the analytic regime of section4. At first48 actual fresh-high prehistories enumerate all unused q>=z,<V. For every candidate compute both capped LOW traces, check their small-alphabet record depends only on q mod M, verify CRT match condition at each possible added clock, and exact first divergence iff a forbidden added match occurs along the small reference path (skip smaller-event ties). Check aggregate reciprocal-square divergence weight <= union weight and d<2M at every short equal-path terminal. At Y1597, 66313 candidate/history pairs, 36256 diverge, 30057 agree, weighted divergence .5476709475 versus weighted union .7910645023; 1736788 congruence checks. Among 11626 terminating candidate suffixes, 7107 also agree; summed terminal support across48 histories drops from1553 to386 after restricting to equal-path short candidates. Three of those candidates have previous high terminal reactivation (finite parameters), none satisfy own divisibility. Actual sample:122 fresh events,79 diverge,33 short,15 short and equal. The analytic smallness bound is not tested at asymptotic parameter choices; these finite tests establish arithmetic identities and weighted counting, not the asymptotic rate or any uniform phase assumption.

## 6. Next direction

The terminal product theorem rules out the fixed-power all-short approach from the previous notes. This is not a reason to abandon the clipped-potential strategy: its target is D_z/(z log z)->0 in probability, which allows much longer LOW paths. A useful next target is an amortized occupation/elapsed-time bound at low terminals, or direct control of F_z(v) for v near z times a sublogarithmic factor, rather than a union bound requiring all suffixes to finish within a smaller power. The weighted small-alphabet comparison handles a short-prefix/terminal reactivation calculation without bounding all hypothetical offsets and may be used in that revised approach. Physical far-coalescence remains an independent unresolved part of the twin-prime strategy. No main edit, no new branch, no Lean compilation.
