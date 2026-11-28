# Global top-relay capacity, an asymptotically equivalent pruned M85, and sharper stopped HIGH packing

2026-11-28 JST, Issue #10. Base f3a08290b4702261bde9b5b08d7cc64de957c23b. User requests continued research, using earlier deductions in further proofs rather than ending at isolated local tests. This checkpoint has two independent improvements and a composition: (i) a history-free upper for pairs of large actual events joined by short relays, used with the slow-event sieve to remove a negligible set of distinct first-H sinks and obtain an equivalent restricted M85; (ii) a source-roughness-weighted shell and near-anchor count that reaches the boundary delta+2t=a and allows logarithmic factors there; (iii) the earlier stopped gain-branch record ladder combined with (i) yields interleaving actual polynomial-scale labels. No M85 lower, upward height record, twin proof, new Lean compilation or independent specialist review.

Notation L=log R. All logarithms natural. Constants may depend on fixed exponents and prior source density constants, never on R. The M85 target is unchanged: H=floor(R^.4), at least c R/L² distinct canonical actual first-H sites with gain<=4H, for all sufficiently large R or an explicitly unbounded sequence. The arguments below preserve either quantifier when applied to such a lower.

## 1. Global large-to-large short-relay upper

Work on actual histories inside even positions x comparable to R, in an interval of length O(R), and heights 0<=h<=H, where H<=C R^theta, fixed theta<1/2. Let Y>=R^xi, xi>0 fixed, Y<=2H+3. Each actual moving label is at most 2H+3 by the height bound. At a moving arrival of prime p, sign s=+1 at even absolute clock and -1 at odd clock, define c_s=1-s and b_s=0 for s=+1, 3 for s=-1. The verified arrival pins are
    y=c_s mod p,   h=b_s mod p,   n=h-y/2.
Consider any actual pair of events p,q>=Y, with the first arrival at (y,h,n), followed by w>=1 ticks to the second firing (inclusive), with total intervening gain g BEFORE that second firing, excluding both p and q. It may contain arbitrarily many other moving events. Let s' be the second sign. Its pins are exactly
    q | F=2h+2w-g+1-2b_(s'),
    q | y-g+s'.                                             (1)
They follow by substituting the prestate y-g, clock n+w into the calendar; no probabilistic use of actual reachability.

Suppose 0<=g<=D<Y-3, w<=W, W=O(H). If p=q, then the two spatial pins force g=c_s+s' mod p, a residue represented by one of -1,1,3. No even g in [0,p-4] has these residues; thus p!=q. F is odd and nonzero, of magnitude O(H), so for each fixed p,h,g,w,s,s' it has O_xi(1) possible prime divisors q>=Y. The first height has O(H/p+1)=O(H/p) choices because p|h-b_s. For each of the possible distinct p,q the CRT for y has one class mod pq; there are O(R/(pq)) y in the allowed slab since pq=O(H²)=o(R). The absolute clock of the first arrival is already determined. Sum over g,w, signs and p, using sum_(p>=Y) p^-2 << 1/(Y log Y). This gives
    # possible distinct first-arrival states
       << R H (D+1)(W+1)/(Y² log Y).                       (2)
This is an upper for a superset of the actual first-arrival states admitting such a pair. It does NOT count all ancestor histories with multiplicity. It also applies to two successive top events with many intermediate subtop events. It requires no slow-wait condition, no special origin and no word enumeration. The upper uses only the already established local pins plus elementary prime counting.

Each actual first-arrival physical state determines ONE future first-H sink (or none), provided h<H and the witness had not already reached H. Thus (2) is also an upper on distinct first-H sinks that admit any budgeted history containing a pair satisfying the conditions. The same charge applies to a set of pairwise physically disjoint connectors: at most one connector contains any given first-arrival state. Neither statement bounds the number of original roots in a coalesced family.

## 2. Remove negligible exceptional sinks from M85

Use H=floor(R^.4), gain budget 4H, all positions in [R-4H,2R], h in [0,H]. Define
    Y=floor(H/L^(1/2)),  K=D=floor(H^(1/2)/L²).
A TOP event means p>=Y. A slow top event means its actual complete wait from birth or previous arrival is >=K. We first bound ALL distinct slow top keys, not only contacts or mergers.

For a slow source x with selected prime p, the next event time is <=2 qmin(x), hence both x-1,x+1 are K/2-rough. Write x+s=p v, where v has length interval O(R/p), and both v and pv-2s are K/2-rough (the source neighbor is positive and comparable to R). For fixed p,s, the two forms have distinct roots modulo odd primes not dividing p. Elementary two-form Selberg upper in v gives O(R/(p L²)), uniformly here: R/p>>R^.6 and K is of fixed positive polynomial exponent up to logarithms; choose a small fixed polynomial sieve support, omitting the prime p at uniformly bounded local cost. For each x,p,s the absolute clock has one residue mod 2p and a range of length O(H) from the height strip. Thus there are O(H/p) choices, and summing gives
    # distinct slow top keys << (R H/L²) sum_(p>=Y) 1/p²
                              << R H/(Y L³)
                              = O(R/L^(5/2)).              (3)
This is the earlier slow-source sieve applied without requiring a contact. It counts keys whose realization has a slow wait; the same physical key may be fast along another history. That distinction causes no issue in the following sink deletion.

Delete every first-H sink with ANY successful canonical witness containing a slow top key. Determinism from the landing of that key implies at most (3) deleted sinks, even if many roots share it. In all witnesses of the remaining sinks every top wait is <K.

Next consider two SUCCESSIVE top events, i.e. with no top event between them. If their intervening gain g<=D, all complete intermediate waits are <=3g in total since each individual full wait is <=2p<=3(p-1). The full wait of the second top event is <K, so w<=3D+K. The global bound (2) gives
    # sinks with any such pair and no slow top wait
        << R H (D+1)(3D+K+1)/(Y² log Y)
        = O(R/L^4).                                       (4)
Delete these sinks too. Combining (3),(4), at most O(R/L^(5/2)) distinct sinks are removed, which is o(R/L²). Every remaining sink has all its successful witnesses satisfying BOTH:
    (a) every top event is fast (full wait <K);
    (b) between every successive pair of top events the gain of subtop events exceeds D.
The restrictions are chronological path predicates; they are not a modified winner rule. If implementing them in a state graph one needs auxiliary history flags/relay gain, or exact witness tracking. The proof does not silently identify that enriched graph with the old minimum-ancestor graph.

Consequently M85 is asymptotically EQUIVALENT to the same target for actual paths satisfying (a),(b), with the original budget and first-H stopping. A lower on the restricted set implies the old M85 directly; any old M85 lower survives this deletion with a smaller positive constant. This is a reduction in admissible witness histories, not a new lower or a claim that the restricted problem is solved.

## 3. Separate the top and subtop height budgets

On the restricted witnesses of section 2 let G_top and G_low denote gains of top and other events, W_top,W_low the corresponding total full waits, and I the final incomplete idle. There are m<=4H/(Y-1)=O(L^(1/2)) top events, so W_top<m K=o(H). The earlier universal complete-wait inequality from the mod2310 finite-state potential (W<=17G/8+395/12 for contiguous blocks of complete waits, as used in the min-plus terminal alignment note) applies separately to the at most m+1 low-event blocks. Hence
    W_low <= (17/8) G_low + (395/12)(m+1).
This uses the earlier certified paper inequality; it is not claimed newly Lean-proved here.

For an intrinsically active sink with qmin(x)<=H/L^6, I<2qmin(x)=o(H). The exact height ledger therefore implies, uniformly over remaining such witnesses,
    H <= (13/8) G_low - (1/2) G_top + o(H),
    G_low >= (8/13) H + (4/13) G_top - o(H),
    G_total >= (8/13) H + (17/13) G_top - o(H).             (5)
In particular G_total<=4H entails G_top<=(44/17)H+o(H). If a witness has G_total<=(8/13+epsilon)H, then G_top<=(13/17)epsilon H+o(H). Thus for near-minimum-gain active witnesses, nearly all gain must be carried by subtop events, rather than merely requiring that the total gain exceeds 8H/13. These bounds are for actual paths after negligible sink deletion; no existence of active sinks or near-minimum witnesses is inferred. They do not replace the original M85 (which permits rough terminal centers). Section 2 itself does not require this earlier finite-state potential.

## 4. Reuse (2) on the previous stretched-exponential stopped HIGH alternative

Take the prior density-scale HIGH source of e66355d, with r prime in [R^.300,R^.3128], or the corresponding conditional dynamic side of the phase-split dichotomy. Apply f3a08290b's separated stopped connectors for T=floor(exp(sqrt L)), total gain threshold D0=floor(R^.28). The hypotheses hold since .28<.300. They contain the earlier common quadratic-log suffix. All heights lie in [0,2R^.3128] for large R. Set
    Y0=R^.27,  D1=R^.22,  W=T.
Use (2) with H'=ceil(2R^.3128), Y0 rounded down and D1 rounded down. Its upper is R^(1-.0072+o(1)), since .3128+.22-2*.27=-.0072 and T=R^o(1). The stopped connectors are already physically disjoint. Delete those containing such a short relay; loss o(R/L²). This deduction is independent of any claim about the fraction of the two stopping branches.

For every remaining connector any two successive winners >=R^.27 must be separated by intervening gain >R^.22. There are at most T intermediate events, so at least one intervening label is >=R^( .22-o(1) ); it is <R^.27 by the successive-pair definition. The earlier record-ladder theorem gives, on the gain-stopping branch, max label >=R^.28/T and exponent gaps at most (2+o(1))/sqrt L, starting o(1). Hence it has at least (.005-o(1))sqrt L strict record winners >=R^.27. Between successive >=R^.27 winners there are disjoint intervening event intervals, giving at least (.005-o(1))sqrt L occurrences of labels in [R^(.22-o(1)), R^.27). These labels are DISTINCT: for each such p the two possible clock residues 0 and p+2 modulo 2p have minimum gap p-2, which is greater than T for large R, so the same label can fire at most once throughout the stopped suffix. The large labels are likewise distinct. Thus the gain branch has interleaved polynomial-scale labels, a stronger structural constraint than just monotone strict records of increasing scale. It does not prove that the branch is rare or force positive net height growth.

## 5. Source-weighted shell: sharpen M=T L^6 to order T for polynomial time

Reopen f3a08290b's HIGH anchors. Same-sign family, fixed 0<a<c<1/2, x0=r(u-1)+c0,h0=r+b0,n0=h0-x0/2, r prime in [R^a,R^c], canonical root A=x0+r-1, source density >=c_* R/L², u and ru+shift both R^a-rough, with (c0,b0,shift)=(0,0,-2) or (2,3,2). This is the input used in the earlier phase-split and adaptive HIGH notes; the roughness of BOTH source forms is necessary for the improvement here.

Fix polynomial time T with R^t0<=T<=R^a for fixed t0>0, a displacement threshold D>=1 and TD<=R^(a-eps) with eps>0 fixed. Let M=ceil(C0 T) for a sufficiently large fixed C0 to be chosen. For g even in [0,D), 1<=w<=T, the exact two pins from the earlier shell theorem are
    q | 2(r+b0)+2w-g+1-2b_s,   q | r(u-1)+c0-g+s.          (6)
The first expression is positive O(r) because T,D=o(R^a); q=r is impossible by the even-g argument. In a dyadic shell S<=g+1<2S, call an anchor bad if there exists such a candidate q>=M S, with either sign. This deliberately counts all hypothetical offsets, not only reached states.

Split q at Q0=R^(a-eps/2). For q<=Q0 and fixed g,w,s,q, the pins fix at most one pair (r mod q,u mod q) with r nonzero. Cover the r range by O(L) dyadic boxes r~P, u in interval length O(R/P). The elementary prime upper in a reduced class mod q is O(P/(q L)), since P/q>=R^(eps/2) and only prime q is omitted in that progression sieve. For fixed r the source forms u,ru+shift in a class mod q give O(R/(P q L²)) by the elementary two-form upper: the parameter length is polynomial and omitted primes r,q have bounded cost; outside them and 2 the roots are distinct. If a required residue is not source-admissible it can simply be discarded; the upper is valid in all cases. The total per q,g,w,s,box is O(R/(q² L³)). Summing over primes q>=MS gives O(R/(L³ MS log(2MS))), then summing g in shell, w, signs, boxes gives
    # moderate-q bad anchors in shell
          << (R/L²) T/(M log(2MS)).
Since T>=R^t0 and D<=R^a, sum_{S dyadic<=D+1} 1/log(2MS)=O_{a,t0}(1). The total moderate exception count is <=C1 R/(C0 L²) for a constant C1 independent of C0>=1.

For q>Q0, at fixed r,g,w,s, the first positive integer in (6) has only O_{a,eps,c}(1) distinct prime factors above Q0, with reciprocal sum O(1/Q0). Each fixes one u residue; the same two-form upper O(R/(r q L²)) is uniform even for q=O(r), because R/(r q)>>R^(1-2c). Sum over r prime using sum 1/r=O_{a,c}(1), over all g<D,w<=T and signs. The tail is
    O((R/L²) TD/Q0)=o(R/L²).
Choose C0 large enough relative to c_* and C1, so total deleted <=c_* R/(4L²) for large R (or any prescribed positive fraction by taking larger C0). No exact asymptotic coefficient of a lower sieve is presumed. This strengthens the earlier crude shell with M=T L^6, whose advantage was not requiring the source roughness.

For all remaining anchors every actual winner satisfies q<M(g+1) before first gain>=D or T. As before include the stop landing, and put E=(M+1)(D+1). The entire connector lies in x0-E<=x<=x0, time 0..T, and h=r+b0+w-g/2=(1+o(1))r uniformly because E=o(R^a). For fixed C0 the gain overshoot bound is now O(T(D+1)), without the old L^6 factor. This still does not determine which stopping branch has positive density.

## 6. Four-form sieve for the sharpened near-anchor packing

Under the assumptions of section 5 (or any separated-candidate HIGH connectors with E,T=o(R^a) and polynomial T), the meeting condition from f3a08290b is
    |d|<=E,  |r'-r-d/2|<=T,  d=x0'-x0 even.               (7)
Equal r forces d=0 and identical root, so consider distinct primes r,r'. They are comparable to r. Fix r,r',d. The anchor pins x0=c0 mod r and x0+d=c0 mod r' prescribe one CRT class; requiring x0 even makes the step 2rr'. Parameter length X comparable to R/(rr') is polynomial in R since 2c<1.

The FOUR rough forms u,ru+shift,u',r'u'+shift in this parameter have undivided shifts as affine forms in x0
    r-c0, r-c0+shift, d+r'-c0, d+r'-c0+shift.
They are distinct except when d+r'-r belongs to {0,2,-2}. For the nondegenerate case, outside primes dividing rr', 2 and their six nonzero pairwise differences, each odd prime ell>=11 has precisely four excluded classes. The product of these bad determinants and coefficients is a nonzero integer of size R^O(1). Its omitted local Euler factor is O((log L)^4): for prime divisors <=L² use the full product of (1-4/ell)^(-1) over ell>=11 there, and for larger ones the sum of reciprocals is O(1/(L log L)) since the log of the integer is O(L). The elementary four-form upper (same Selberg diagonalization and small polynomial support as the earlier reverse-depth/rough packing notes) now gives at most
    O(R/(rr') * (log L)^4/L^4)
source anchor pairs for fixed r,r',d. For completeness, choose support D_sieve=R^kappa small relative to a and 1-2c, ignore the finitely many primes <=7, sieve with four distinct residues at all other good primes; CRT remainder O(D_sieve^6) is negligible for X and the omitted-prime factor above. The main denominator is bounded below by a constant times L^4/(log L)^4 using the restricted Euler product with a sufficiently small fixed power of D_sieve and Markov on the log modulus, as in the prior elementary upper. No distribution of primes in polynomial moduli beyond this elementary progression upper is invoked.

For each fixed r,d the allowed r' interval has length O(T+1), and contains O(T/log T) primes by the same ordinary elementary one-dimensional interval upper, uniformly because T>=R^t0. Also sum_{r prime>=R^a} 1/r²<<R^-a/L. Summing all even d and r,r' yields
    # nondegenerate near pairs
          << R^(1-a) (E+1) T (log L)^4 / L^6.              (8)
For the degenerate case d+r'-r in {0,±2}, (7) forces |r'-r|=O(T+1), and for each r,r' at most three d choices. Ignore roughness, use O(R/r²) CRT count. Even summing r,r' over integers gives O(R^(1-a)(T+1)), power-saving under the fixed TD margin of section 5. This treats the actual degeneracy, not a transfer of a nondegenerate determinant estimate to equal forms.

It follows that if
    (E+1)T <= C R^a L^(4-epsilon1)                         (9)
for any fixed epsilon1>0, near-pair deletions cost o(R/L²), since (log L)^4/L^epsilon1 ->0. In contrast the old bound required (E+1)(T+1)=o(R^a/L²). After both deletions we retain >=c' R/L² pairwise physically disjoint actual stopped HIGH connectors, with c'>0 fixed. No root is assigned a fictitious continuation.

Examples for the [.300,.3128] HIGH minus family:
  - T=floor(R^.09), D=floor(R^.12 L³), M=ceil(C0 T). The power boundary .12+2*.09=.300 is attained, with ET=O(R^.300 L³), E=O(R^.21 L³), satisfying (9) and TD power margin. This extends the old strict delta+2t<a region to its boundary including a log factor. The gain branch has max label >=R^.03 L³(1+o(1)).
  - T=floor(R^(a/3) L), D=floor(T L^(1/2)). Here ET=O(R^a L^3.5), so the boundary exponent a/3 is attainable for the time cap even with a factor L; gain target exceeds T by a growing factor. Its guaranteed largest gain-branch label is only of order at least L^(1/2), so do NOT apply the polynomial-large-label distinct-cut bound from the previous note to this example. The original age and height remain those of stopped HIGH connectors, not first-H height growth.
Both examples inherit the prior source lower review obligations and the static-vs-dynamic dichotomy where relevant. Neither guarantees the TIME branch, which was the original obstacle.

## 7. Status, exact implications, remaining gap

The strongest new structural result for M85 is section 2, which removes a negligible class of DISTINCT first-height sinks and proves equivalence with a chronologically restricted target. Section 3 identifies the subtop budget that must support active height growth. Section 4 turns the previous record ladder into an interleaving of actual distinct labels, and sections 5-6 improve the permitted polynomial stopped envelope at source density scale. These are connected deductions and not a solution of the stopping branch lower, or a density lower on M85. The next unresolved issue is whether the large intermediate-label relays mandated by section 4 can be controlled on actual reachable paths; counting all possible candidate offsets and times still loses powers. For M85 the remaining task is a lower on restricted transport or an alternative arithmetic breakthrough. In particular the new pruned equivalence must not be interpreted as proving that any such sink exists at the target density.

## 8. Verification and source ledger

- Reopened f3a08290b4702261bde9b5b08d7cc64de957c23b, research/2026-11-28-min-negative-polynomial-stopped-high-and-record-ladders.md (prior shell, exact meeting relation, record ladder), and e66355d7718f684f05a780d9213603f8ddf46133 (phase split source). Source lower inherited, not independently verified.
- Reopened at pinned base: research/2026-11-28-min-negative-height-section-minplus-and-terminal-defect.md §§6-8, research/2026-11-28-min-negative-common-clock-slow-contact-capacity.md, research/2026-11-28-min-negative-first-use-complexity-and-diversity-growth.md (elementary sieve), research/2026-11-28-min-negative-high-height-shell-growth-and-second-quiet.md, and research/2026-11-26-min-local-negative-height-local-scan-and-enhanced-wall-budget.md. The universal W<=17G/8+395/12 block inequality is the previous mod2310 paper certificate, not an independent rerun. Section 1 generalizes the local short-relay idea using the full height pin and counting distinct physical first arrivals rather than clock-free spatial pairs. No claim of literature priority and no new external theorem.
- Audit research/lean/negative_min_global_top_relay_and_rough_packing_audit.mjs @c51b80ef66470bb87343c5c8809b05d0eb0657a7 blob 94f7b03730e6478ccde12f11e0a4f31fee19fd03. Executed twice in ECMAScript; exact commit and branch readback verified. Three finite actual slabs R=12000,48000,192000 with proxy Y=H/3,K=D=floor(sqrt H) (not the asymptotic log parameters): 42003 roots,416082 completed events within budget,32482 top events,26289 slow top incidences,12520 successive top pairs,587 short fast relay incidences,424 repeated-label controls,39904 successful first-height paths,4896 distinct sinks and sink-union controls. All passed. These include nonvacuous short/slow exceptions; finite bad sink proportions are not evidence of asymptotic negligibility. Synthetic CRT:7380 fixed r,r',d cases,540 degenerate,6840 nondegenerate,20520 local four-root counts,2000 near-clock controls. Exact integer exponent checks for boundary example and interleaving. The audit verifies algebra, physical calendar, sink charging and local densities; it does not test asymptotic sieve errors or imply any lower.
- No new Lean compile, no independent specialist review, no changes to core b0e26798535b2c997f1383c1dc37bbe560aac938 or main/sibling branches. M85 remains open.
