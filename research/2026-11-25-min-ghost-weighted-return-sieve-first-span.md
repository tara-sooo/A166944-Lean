# Weighted gain-capped return sieve and localization from first selection

2026-11-25 JST. Continues 6829ba951c66d85071a441b5ac2c747d54cf05cf on the SAME research/min-cycle-forest-2026-11-24 branch. New paper proof extending the previous three-residue sieve from probability of ANY long return to expected total weighted long-return contribution. Also removes short first-selection-span returns down to the square-root scale. Finite common-CRT audits of the weighted injection. No external search, no Lean compilation. No proof of the entire signed repeat-bank limit or of the physical far-coalescence bound.

## 1. Count candidate return positions with their weights, not the union event

Use the common infinite CRT ghost, or any finite initial segment of odd primes, with the exact selected-label and quiet-tick history law as before. At relative time s the gain g is nonnegative, even, and increases by p-1 at an executed label p; its completed preceding wait w satisfies w<=2p. Signed attained height is 2s-g. We keep the gain cap on PRE-event gain, g<=2U, and only events executed by elapsed time U. A positive attained peak through U has its entire preceding gain bounded by 2U, so this cap covers the relevant prefixes. It is not an assumption about the later untruncated path.

Let p be a repeated label, g0 its pre-gain at its FIRST selection, g1 its pre-gain at the specified repeat. For p>=5 the two eligibility signs give the exact representation
    g1-g0=m p+a, a in {-2,0,2}, m>=1,
    m<=(2U+2)/p
when g1<=2U. The representation is unique since differences between two possible a are at most 4<p. The lower bound on m uses g1-g0>=p-1. The representation does NOT restart when the label is selected again, or at a time window boundary. If w>p/4, every odd prime ell<=p/8 is ineligible at g1, giving the two forbidden horizon residues as in the preceding note.

Define for z>=ceil(sqrt(2U)) the nonnegative random variable
    W_z(U)=sum p_i over repeated p_i>=z, s_i<=U, pre-gain<=2U, w_i>p_i/4.
This counts EVERY qualifying repeat with weight p_i. Similarly define W_loc(U,K) for p_i>=ceil(sqrt(2U)) and the extra first-selection stride constraint m_i<=K (K>=1 integer). A repeat may belong to both sums, which is harmless for union upper bounds.

At its first-selection tick, a label p with known pre-gain g0 may be assigned one candidate ticket (p,m,a) for each potential future position g0+mp+a satisfying the rough-neighbor necessary condition at the chosen sieve primes. Each ticket has weight p. Distinct actual long-wait repeats of this label have distinct pre-gains by strict horizon growth. They therefore inject into DISTINCT tickets assigned at the one first-selection tick, even if p repeats arbitrarily many times. We can use the same necessary-condition overcount for all candidate tickets, not just count whether at least one candidate exists. This is the key new weighted step.

The realized total weights W_z and W_loc are both <=4U deterministically, because every charged p<4w and the completed waiting intervals are disjoint. This gives a uniform integrable bound even on exceptional initial phase configurations. The realized sum of their waits is <=2 times the corresponding sum of p, by w<=2p. These bounds require no finite expected untruncated cumulative gain.

## 2. Uniform sieve for polynomially smaller labels and larger strides

Put L0=ceil((log U)^2), D=floor(U^(1/20)), R=U^kappa with sufficiently small fixed kappa as in the preceding note. Reveal all coordinates for primes ell<=R at time zero and common parity. In a finite initial segment lacking labels >=sqrt(2U), the claimed sums vanish; otherwise all these revealed primes are available. Define Good as in the previous note: for EVERY integer v in [-2,2U+2], at most ceil(log U) primes L0<ell<=R satisfy c_ell+v==+/-1 mod ell. The independent horizon coordinates, elementary exponential-moment estimate and union over v give
    Pr(Good^c)<=exp(-Omega(log U log log U)).
This is a statement about the initially revealed coordinates, not about path histories.

For a fixed v in this interval and 1<=m<=2U+2, count primes p in a dyadic band [Q,2Q), Q>=ceil(sqrt(2U)), with
    c_ell+v+mp != +/-1 (mod ell)
for every sieve prime ell in (L0,R]. Since R<Q/8 eventually, this condition is necessary at any long-wait repeat in the band, including a finite alphabet with the label present. When ell divides m, omit that sieve prime entirely for this upper bound. Unlike the preceding near-top proof, we do NOT require every stride to be less than L0. The omitted primes have
    sum_(ell|m, ell>L0) 1/ell <= log(2U+2)/(L0 log L0)=o(1).
At remaining primes the forbidden residues for p consist of 0 (primality) and the two roots of the neighbor conditions; there are three distinct roots except for a collision with zero, in which case there are two. On Good the latter exceptional primes have total reciprocal weight <=ceil(log U)/L0=o(1). The Mertens product of local survival fractions is therefore
    O((log L0/log R)^3) = O(lambda(U)),
    lambda(U)=(log log U)^3/(log U)^3.
Both omitting stride factors and collisions cost only a bounded multiplicative factor. Constants are independent of v,m,Q and the initial coordinates on Good.

Apply the self-contained Selberg quadratic majorant from section 3 of the preceding note to this reduced prime set: forbidden residue counts are multiplicative, remainder O(nu(d)), the level D yields error O(D^6) and the diagonal term is bounded by twice the local product. In detail, the unrestricted divisor-weight expectation of log d is at most 3 sum_(ell<=R) log ell/ell=O(log R), so the same kappa choice makes at least half its mass lie below D even after omitting primes. No change to the proof or its constants is required by the omissions. Since D^6<=U^0.3 and Q>=sqrt(2U), the remainder is o(Q lambda(U)). Thus for every fixed v,m, band,
    #candidate primes <= C Q lambda(U).
This extends the uniformity of the previous sieve to all polynomially bounded strides and square-root-scale candidate bands. The full candidate set can be larger than the set of actual repeated selections by an arbitrarily large factor; only its upper bound is used.

## 3. Expected weighted long-repeat bound

Use the history filtration with the initially revealed coordinates and the full selected-label/quiet-tick history before tick s<=U. For each unused p>=ceil(sqrt(2U)), the exact history law gives conditional selection probability <=2/p^2. The pre-gain g0 and Good are measurable. If g0>2U, it cannot initiate a relevant candidate. Otherwise for fixed m and a, use v=g0+a. We may overcount all choices with g0+mp+a outside the gain cap, or wrong parity; the valid ticket set is a subset.

In band [Q,2Q), each (m,a) gives at most C Q lambda(U) candidate labels. When a candidate label is selected fresh, its ticket contributes p to the potential weighted return count. Multiplying by its conditional probability gives at most 2/p<=2/Q per candidate label. Consequently at a single tick, conditional on Good and the actual past, the expected sum of new ticket weights in this band is
    O(lambda(U) M_Q)
where M_Q is the allowed number of stride values. Sum over ticks without conditioning on future returns, and use the pathwise injection from section 1.

For W_z use Q=z,2z,4z,... up to 2U+1, with M_Q=floor((2U+2)/Q); no actual repeat can have larger p. The geometric series sum M_Q=O(U/z) (for z<=2U+1; above this W_z=0). On Good^c use W_z<=4U. It follows that
    E W_z(U) <= O(U^2 lambda(U)/z) + 4U Pr(Good^c).
This is the main result. It is a weighted expectation, NOT an upper bound on the probability of any repeat. In contrast the earlier unweighted union argument lost a second factor U/z in the probability target. For
    z=ceil(U/(log U)^b), 0<b<3 fixed,
we now have
    E W_z(U)/U = O((log log U)^3/(log U)^(3-b))=o(1).
In particular b=5/2 gives the rate O((log log U)^3/sqrt(log U)) for the normalized EXPECTATION, hence convergence in probability by Markov. This removes a wider label range than b<3/2 in the prior zero-occurrence criterion. Long returns in this larger range are not claimed to be absent. One can take even z=ceil(U (log log U)^4/(log U)^3) for large U, obtaining O(1/log log U) for the normalized expected weight. These choices eventually exceed sqrt(2U).

For W_loc use Q=ceil(sqrt(2U)), 2Q, ... and M_Q<=K. There are O(log U) bands, so
    E W_loc(U,K) <= O(U K (log log U)^3/(log U)^2)
                    + 4U Pr(Good^c).
In particular K=floor((log U)^(3/2)) gives the same O((log log U)^3/sqrt(log U)) normalized upper bound. More generally K=o(log^2 U/(log log U)^3) suffices. The localized bound includes many repeats at polynomially smaller labels p>=sqrt(2U), provided the gain span from their FIRST selection is at most Kp+2 (equivalently the allowed representation has m<=K; a span <=Kp-2 certainly implies this). The proof does not treat a short span from an arbitrary previous repeat as short from the first selection. Known labels do not recover their fresh conditional probability after a restart, so the bound is not a blanket estimate for all short consecutive-return spans.

These estimates hold for the infinite process and uniformly for finite initial-segment cutoffs, with the same upper bounds. No conditional independence of later known-label selections has been assumed.

## 4. Effect on the signed-peak target

Use the previous fresh-wait theorem E F(U)=O(U/log U). For a slowly growing LOW cutoff A choose L_A=2 product_(3<=p<A)p<=U^(1/4). Partition into initial LOW run and high blocks with label p>=A followed by its LOW suffix. The initial signed peak <=5L_A, fresh blocks contribute <=2F(U)+O(L_A^2/log(2L_A)). For any repeated high block with p>=10L_A+2, if w<=p/4 its positive block surplus b_i=[2w-(p-1)+d_i]_+ is zero since d_i<=5L_A. Otherwise b_i<=2w<=4p. Both the z threshold and the sqrt(2U) threshold above eventually exceed 10L_A+2.

For a positive peak truncate at an attaining event; every entering block's pre-gain is <=2U. Its LOW prefix maximum is at most the full observed suffix maximum, so we can use actual observed blocks through U. With z as in section3 and K=floor(log^(3/2) U), define E_res(U) to be the sum of b_i for repeated high blocks with pre-gain<=2U, A<=p<z, and NOT (p>=ceil(sqrt(2U)) and m<=K). The m constraint is only used at p>=sqrt(2U); no stride convention for very small labels is needed. Then pathwise for large U,
    D_infty(U) <= 5L_A+2F(U)+O(L_A^2/log(2L_A))
                   +4 W_z(U)+4 W_loc(U,K)+E_res(U).
The same holds for finite cutoffs. The expected total of all terms except E_res is o(U). In particular
    E[(D_infty(U)-E_res(U))_+]=o(U).
This is a positive-surplus majorant, not an exact decomposition of the signed bank. It leaves the following repeated-block cases:
  (i) A<=p<ceil(sqrt(2U));
  (ii) ceil(sqrt(2U))<=p<z and m>K, i.e. the first-selection-to-return gain span exceeds Kp-2.
Their positive contribution is not shown sublinear. The equivalent signed repeat-bank limit from 36e95f2e13b1 may still benefit from cancellations among those residual blocks. The new result strictly strengthens the previous sufficient majorant in the near-top range and removes an additional class of smaller returns. It does not prove eta->0 or the global physical far-coalescence bound.

## 5. Finite audit and exact persistence

Saved research/min_ghost_weighted_repeat_sieve_audit.mjs and research/min_ghost_weighted_repeat_sieve_results.json, exact remote readback at 9873e1dcaa25cd540b9903dc24afb24534007611. Fixed pseudorandom seeds, common CRT phase simulations, finite prime alphabet <=4U; U=256,1024,4096,16384,65536; N=256 paths each except N=128 at U65536. The asymptotic coupling error O(1/log U) to the infinite model is not a calibrated finite-sample error. Diagnostic thresholds q0=max(11,floor(sqrt(U)/4)), root=ceil(sqrt(2U)), z=max(root,ceil(U/log^2.5 U)), K=max(2,floor(log^.8 U)). Note that z equals root in ALL these small windows; the q0 threshold is deliberately below the analytic range to exercise more returns. Diagnostic K is smaller than the analytic growing K, and the rough test only uses primes <=47 and <=p/8. No numerical test of the Selberg asymptotic constant or of the limiting rate is claimed.

At each gain-capped first selection of a label >=q0 enumerate all possible future rough pre-gains g0+mp+a up to 2U, with correct parity and minimum gain since first selection. Store the candidate positions and m. On each actual gain-capped long return, assert the unique stride and offset, roughness and candidate membership, and delete the ticket to test injection. Accumulate candidate p-weight, local candidate weight, realized p-weight and wait sums, separately at all three thresholds. Check for each path the weighted and localized injections, realized p-weight<=4U, completed wait sum<=2 times realized weight. For high blocks using A5 (L=6), and p>=62, verify b<=2w, short blocks have b=0, and summed block surplus<=2 times the corresponding long-return wait. Check small LOW peaks and every executed event wait. The finite q0-only rows are structural tests, not covered by the asymptotic hazard theorem.

Aggregates (sum over sampled paths, not means), for root threshold:
    U       root  K   long returns   sum p  sum w   local returns   local sum w
    256     23    3    7               187     91      0              0
    1024    46    4    5               297     306     2              158
    4096    91    5    4               540     429     2              69
    16384   182   6    1               211     53      0              0
    65536   363   6    0               0       0       0              0
At U65536 the lower diagnostic q0=64 has 22 long returns (5 local), sum p2622, sum w2801, local sum p455 and local sum w387, positive high-block surplus3168 (local386), 8168 executed event checks. All candidate injection and signed block tests pass. The conservative candidate weight at root there is 2689929, while no actual long returns occur; thus the diagnostic necessary conditions heavily overcount. No Lean compilation.

## 6. Next target

The weighted first-selection argument improves b<3/2 to b<3 for deletion of positive near-top repeat surplus, and extends to polynomially smaller labels when the first-to-return span is bounded in units of p. To go further, actual old-label return behavior (not a restarted fresh hazard) is needed: either control the long first-selection spans through signed gain credit, or bound positive blocks of smaller labels through low-cutoff termination/occupation. The physical far-coalescence upper bound is still a separate open requirement. No main edit, no new branch, no twin-prime proof.
