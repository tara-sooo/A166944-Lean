# Rough stride sieve in two-stock transitions and disjoint downward-pair credits

2026-11-25 JST. Continues 51c90c61c02d43629de2ac666cc5c0274ca1b5f0 on the SAME research/min-cycle-forest-2026-11-24 branch. New uniform two-residue sieve on the enumerated stride of the known label in the preceding two-stock divisor proof; four residues in one discovery-order case. Also a signed downward-pair erasure rule based on actual completed clock waits. The exact clock congruence has not yet yielded a polynomial improvement of the two-stock scale. Original paper proof, finite diagnostics, no external search or Lean compilation. Full signed peak and physical far-coalescence limits remain unresolved.

## 1. Setting and exact stride relation

Use the common independent CRT ghost, conditional on common initial time parity, with infinite odd-prime alphabet or a finite initial segment. At executed label p, even gain increases by p-1 and completed preceding wait w_p<=2p. At any tick through integer U, an unused label p>=z0=ceil(sqrt(2U)) has conditional first-selection hazard <=2/p^2. This remains true after initially revealing coordinates of a disjoint small prime set. The previous proof uses all quiet ticks and selected-label history, not an independence approximation for already-known labels.

Choose HIGH cutoff A>=5, LOW primorial L=2 product_(3<=ell<A)ell <=log^(1/8) U. Consecutive HIGH events q,p have intervening LOW gain d even, 0<=d<L. Use the prefix with POST-gain<=2U, containing every positive attained peak through U. Total selected prime weight in it is <=3U. In any bands p in [P,2P), q in [Q,2Q), P,Q>=z0, consecutive q=p is impossible eventually because p>L+3. As before p is repeated, q may be fresh or repeated. The two first pre-gains u_p,u_q and current pre-gains G_p,G_q satisfy
    G_p=u_p+m p+a, G_q=u_q+n q+b,
    m>=1, n>=0, a,b in {-2,0,2},
    m p-(n+1)q=u_q-u_p+b-a-1+d.               (1)
All relevant first gains are <=2U and m p,n q<=2U+2. Both strides are even, but we overcount every integer stride. The previous latest-first-selection argument assigned a p-weighted ticket at the later of the two first-selection ticks. The other label and its first gain are known then, and fixing one stride determines a positive integer O(U) divisible by the newly selected label. That positive integer has O(1) prime factors >=z0. A fixed ticket identifies the later G_p, so distinct realized pairs inject into distinct tickets.

We now count only pairs with w_p>p/4. The actual clock selection implies that every available odd prime ell<=p/8 is ineligible at G_p, because if eligible its next clock would occur within 2ell<=p/4 from the immediately preceding attained state. In particular for finite initial segments containing p all the necessary small primes are present. No assumption that the preceding HIGH event is the immediately preceding actual event is needed.

## 2. Uniform sieve on the stride of the known label

Fix 0<epsilon<1/4 and restrict the lower band endpoints z0<=P,Q<=U^(1-epsilon). For a known label r in one of these bands and the enumerated stride j, the possible current target pre-gain is V+j r for a fixed integer V determined by the known first pre-gain and the offsets (in the P-latest case replace j by j+1 or absorb the shift into V). We bound integers j in an interval of length N comparable to U/R_band, where R_band is the lower endpoint of r's band. Thus N>=c U^epsilon. A subset cut down by gain-cap or sign restrictions can only be smaller.

Initially reveal all coordinates at odd primes ell<=Y=U^kappa, with kappa>0 sufficiently small depending on epsilon, and D=floor(U^(epsilon/20)). For all large U, Y<min(P,Q)/8 and Y<min(P,Q). For every odd ell<=Y the slope r is invertible modulo ell because r is a prime >=z0. The target roughness condition
    c_ell+V+j r != +/-1 (mod ell)
therefore excludes EXACTLY TWO distinct residue classes of j. This holds for EVERY choice of initially revealed coordinates, V and r. There is no collision with an additional primality constraint on j: j is an integer, not a prime. In particular no initial exceptional-coordinate event or loglog loss is needed in the single-position sieve.

Use the self-contained Selberg quadratic majorant of research/2026-11-25-min-ghost-gain-capped-top-repeat-rough-sieve.md section 3, now for the variable j. For squarefree moduli over the sieve set, forbidden intersection density g(d)=product_(ell|d)(2/ell) and count N g(d)+O(nu(d)). Its diagonal divisor sum is G(D)=sum_(d<=D) product_(ell|d)(1/g(ell)-1)^(-1). The unrestricted sum is product_(ell<=Y, odd)(1-2/ell)^(-1), with independent divisor inclusions of probability 2/ell when normalized. The mean log divisor is O(log Y) by the elementary prime-count bound. Choose kappa sufficiently small that this is <=(1/2)log D. At least half the divisor weight then lies below D. The explicit quadratic weights give N/G(D)+O(D^6); D^6<=U^(.3epsilon)=o(N/log^2 U). The ordinary Mertens harmonic-prime estimate gives product_(ell<=Y, odd)(1-2/ell)=O((log Y)^(-2)). Hence
    #rough stride choices <= O_epsilon(N/log^2 U).          (2)
Uniformity holds even when V is an adaptive gain from the earlier path, because the upper bound is deterministic for arbitrary revealed coordinates.

If the discovery of p is later than q and also w_q>q/4, the pre-gain of the predecessor is G_q=G_p-B, B=q-1+d. In this case B is known when enumerating n, and at all odd ell<=Y both G_p,G_q must be rough (Y<=min(p,q)/8). Discard ell<=log^2 U and ell dividing the nonzero integer B(B-2)(B+2). Here B>2 and B=O(U); omitted factors above log^2 U have total reciprocal mass O(log U/(log^2 U log log U))=o(1). Every remaining ell has four distinct roots in j, since the two pairs can coincide only when B=0,+/-2 modulo ell. Apply the same quadratic sieve with four roots and smaller kappa if necessary. The local product is O_epsilon((log log U/log U)^4). Thus in this discovery-order case,
    #double-rough stride choices <= O_epsilon(N (log log U/log U)^4).  (3)
For the Q-latest case the unknown q occurs in B, so (3) is not asserted there. The single-position bound (2) still works.

## 3. Expected weighted transition bounds

For P-latest, at a tick with candidate first pre-gain u for p and known q, enumerate n, a,b,d. The target G_p=u_q+(n+1)q+b-1+d is fixed by these parameters independently of the fresh p. Apply (2) to the n interval before the divisor enumeration. There are now O_epsilon((L+1) U/(Q log^2 U)) choices per known q. For each, the positive divisor target M=G_p-u-a=m p has O(1) prime factors in the p band. Ticket weight p times hazard <=2/P. If K_Q(s) is the past distinct selected stock of q-band primes, the conditional new weight is at most
    O_epsilon((L+1) U K_Q(s)/(P Q log^2 U)).
For Q-latest enumerate m,a,b,d against known p. G_p=u_p+m p+a is fixed, so (2) gives O_epsilon((L+1) U/(P log^2 U)) choices per known p. The positive target M'=G_p-u-b+1-d=(n+1)q gives O(1) candidate q, each hazard <=2/Q^2, weighted by p<=2P. Conditional new weight at most
    O_epsilon((L+1) U K_P(s)/(Q^2 log^2 U)).
Here the initially revealed small primes are disjoint from both bands, so the exact conditional hazard still applies. There is no conditioning on the later selection success. E K_R(s)<=O(U/(R log R)) uniformly in s, by the fresh hazard and prime-count bound. Sum all U ticks and both discovery orders and use the ticket injection:
    E W_long,[P,Q] <= O_epsilon((L+1) U^3/(P Q^2 log^3 U)).    (4)
This holds for the weighted total of repeated targets with long w_p (whether or not q is repeated). In the P-latest double-long branch alone the same argument with (3) gives
    E W_double,P-latest,[P,Q] <= O_epsilon((L+1) U^3 (log log U)^4/(P Q^2 log^5 U)).
It does not improve the other discovery order to the same rate.

Summing (4) geometrically over bands with lower thresholds P0,Q0>=z0 and upper endpoints of the order U^(1-epsilon) gives the same bound with P0,Q0. For the equal threshold T=ceil(U^(2/3)/log^(7/8) U), choose epsilon=1/12. The band tails with P or Q>U^(1-epsilon) are bounded by the preceding unrestricted two-stock estimate O((L+1)U^3/(P Q^2 log U)); their normalized sum tends to zero by a fixed polynomial margin. Indeed (1-epsilon)+2(2/3)>2 and (2/3)+2(1-epsilon)>2. Thus for ALL p,q>=T in the capped prefix,
    E W_long(T,T;U)/U = O(log^(-1/4) U).
The tail terms are absorbed into this rate. More generally equal threshold U^(2/3)/log^b U works for fixed b with 3b+1/8<3. The polynomial exponent 2/3 has not been lowered by this argument.

A scale-uniform mixed-product result within the bands with P,Q<=U^(1-epsilon) follows by summing (4) over those meeting p q^2>=U^2/log^c U. Their lower endpoints satisfy P Q^2>=U^2/(8 log^c U). Sum over P first to bound sum 1/(P Q^2) by O(log^c U/U^2) for each Q; there are O(log U) Q bands. Consequently normalized expected weight is O_epsilon((L+1) log^(c-2) U). For c=3/2 it is O(log^(-3/8) U). This product estimate is stated only for the indicated middle-scale band region; the previous unrestricted product result remains available elsewhere.

## 4. Nonoverlapping downward-pair erasure using signed clock waits

For each HIGH poststate i define J_i=2s_i-g_post,i-6chi_i, and a_i=J_i-J_(i-1), where i-1 denotes the previous HIGH poststate (or initial sentinel). This incorporates the preceding LOW run. The established LOW bound gives
    a_i <=2w_i-(p_i-1)+5L+6.
Suppose consecutive HIGH labels q,p have p repeated and p>=10L+14, a_p>0, q>=16p, and w_q<=q/4. Then
    a_p<=4p,
    a_q<=-q/2+5L+7,
    a_q+a_p<=-q/4+5L+7<0.
The first inequality uses w_p<=2p, p>=5L+7. The second uses the short completed clock wait of q; the last uses q>=16p. Thus even if the repeated p produces a large positive corrected increment, the preceding q pays for it with a negative increment. This is valid whether q is fresh or known, with no gain cap or probability assumption. The constants are deliberately conservative. The criterion only concerns actual consecutive HIGH poststates, not deletion of events from the dynamic process.

Extend the earlier backward record-erasure scan on a prefix ending at the last HIGH state before the first attained maximum:
1. At a repeated positive step with the downward criterion above, jump from its HIGH index i to i-2 and record the two-step signed change as a single nonpositive interval.
2. Otherwise if it is a nonfresh nonrecord at its own label, jump to an earlier maximal corrected height of that label (as before).
3. Otherwise move one HIGH step backward.
The downward-pair rule is applied before the ordinary record-erasure rule. The index strictly decreases, so all intervals and ordinary steps are disjoint, cover the actual prefix once, and telescope. Every retained ordinary repeated event is still a strict same-label record in the ORIGINAL sequence. The interval change of a downward pair is not necessarily a multiple of 2p; only equal-label erasures retain that lattice property. No extra credit is added for the same events inside an already erased interval.

Let C_pair and C_record be the nonnegative magnitudes of net changes in the two kinds of disjoint erased intervals, Nminus the negative magnitudes of ordinary changes, and R the positive ordinary repeated increments. The earlier initial/final LOW correction and fresh-wait count give
    D(U) <=5L+12+2F_wait(U)+(5L+6)K_U
             +[R-C_pair-C_record-Nminus]_+.
The prior E F_wait=O(U/log U), E K_U=O(sqrt U/log U) make the additive/fresh part O(U/log U) in expectation. All previous probabilistic positive-step deletions apply to the remaining ordinary repeated steps because their classifications use the ORIGINAL trajectory, not the scan. In particular (4) controls all retained positive steps in its range, since a_p>0 implies w_p>p/4 and a_p<=4p. Delete those increments once along with the earlier classes and retain the new disjoint credits. The same expected positive-part residual reduction follows:
    E[(D(U)-[R_new-C_pair-C_record-Nminus]_+)_+]=o(U).
This does not compare the exact new residual numerically to the old residual on every path; the changed scan may choose different record intervals. But the new scan cannot retain a positive repeated ordinary step satisfying the downward-pair criterion. In particular a retained such step with p>=10L+14 and q>=16p must have w_q>q/4. If both labels exceed the middle-scale threshold and p is the later-discovered label, the four-residue bound (3) can be used on this long-long branch. The downward erasure works at ALL label scales satisfying its deterministic conditions, including below z0. It does not address positive upward or comparable transitions at small scales. No conclusion of full signed residual convergence is made.

## 5. Audit and persistence

Saved research/min_ghost_rough_stride_downward_credit_audit.mjs and research/min_ghost_rough_stride_downward_credit_results.json, exact remote readback at 0349200dc284e25c5c13082ea30e2f48e00e5af1. Run node research/min_ghost_rough_stride_downward_credit_audit.mjs 256 1024 4096 16384 65536. Executed the script logic in the tool's JavaScript runtime, not separate Node or Lean. Fixed pseudorandom common CRT phases, finite initial alphabet <=4U; 256 paths per U except128 at largest. A5,L6, diagnostic base=max(7,floor(ceil(sqrt(2U))/8)). Structural tests below the analytic root threshold are not applications of the fresh hazard.

For random fixed prime slopes, shifts, and even B enumerate all j residues at odd ell<=47. Verify exactly two roots for the single rough condition at invertible slopes; four roots for the double condition when ell>=5 and B,B-2,B+2 are nonzero mod ell. On actual capped long-target pairs check the two-stock divisor relation and reconstructed target roughness; in P-latest with long predecessor also check its roughness. Across the five windows 856 actual long-target checks (166 P-latest,690 Q-latest),121 P-latest double-long checks,8 above analytic root. At U65536 there are7924 executed events,12 diagnostic long-target pairs,2 P-latest double-long pairs,1 root pair. Local residue checks there:43005 single and32274 double, plus10734 omitted cases (overlapping counts are intentional). No numerical estimate of the Selberg asymptotic constant.

For each observed first attained peak apply the extended backward scan. Verify exact disjoint coverage, signed telescoping, strict record property of ordinary repeats, lattice divisibility of equal-label erasures, and the peak inequality including both credits. At U65536,128 scans,196 record erasures, total record credit38326. One actual short-wait downward pair was found at U16384 on the full observed trajectory, none encountered by the peak-prefix backward scans across all windows; therefore the new erasure branch is not exercised nonvacuously inside the actual scans. It is separately checked by 2064 synthetic extreme upper-bound cases spanning L=6,30,210 and p,q satisfying the inequalities, using integer wait extrema. These are algebraic tests, not legal-clock path examples. All assertions passed in the executed runtime. The previous finite-to-infinite coupling error is asymptotic, not a calibrated finite-sample error. No Lean compilation.

## 6. Remaining work

The new rough-stride sieve gives a logarithmic improvement of the two-stock bound, including all both-repeated transitions at p,q>=U^(2/3)/log^(7/8) U that can contribute positive height. The downward-pair credit handles one class without a lower bound of sqrt(U). A polynomial-scale improvement toward sqrt(U), or a global signed estimate for smaller/comparable known-only runs, is still needed. We did not derive a new polynomial saving by the exact clock congruence itself; the clock enters through its completed-wait restrictions and the signed cancellation. The independent physical far-coalescence bound is still open. No main edit, no new branch, no twin-prime proof.
