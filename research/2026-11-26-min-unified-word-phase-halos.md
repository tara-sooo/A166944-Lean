# Compressed intermediate words with low-index exit-slot halos and adaptive canonical age

2026-11-26 JST. Continues [f97bec51c33](https://github.com/tara-sooo/A166944-Lean/blob/f97bec51c33aaf44773761927f57835c2d18ab97/research/2026-11-26-min-unified-paired-reset-ancestry.md), [e25fb0b8f7a](https://github.com/tara-sooo/A166944-Lean/blob/e25fb0b8f7a37771d04ef5593eae0ffd08478153/research/2026-11-26-min-unified-low-phase-slot-halos.md), and [0fadbb6a053](https://github.com/tara-sooo/A166944-Lean/blob/0fadbb6a0539454d77f9fa51e31d942951724bfc/research/2026-11-26-min-unified-multi-intermediate-clock.md). Independent branch heads checked unchanged, prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. Integrates the compressed-word sieve and exact adjusted arrival phase with deterministic completed exit slots. Both RESET and nonRESET successors are covered; one summable index weight rather than two independent time factors. New all-event halo cap for a growing number of intermediate events, including polynomial-size gains, with a larger cap for smaller radicals. An independent adaptive canonical-age bound improves the former uniform B sqrt(u) cutoff. No full contraction, no Lean compilation.

## 1. Original ensemble and two radical scales

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN gain-stopped completed prefixes and terminal snapshots unchanged. Natural HIGH means p>=Q, r(C)>p/sqrt(log p). Actual event gain p-1, wait 1<=w<=2r<=3(p-1), total gain <H, elapsed <=3H. All deficits d=2t-C nonnegative. Set P0 to the largest even primorial <=ell, LOW labels its odd prime factors. As before any contiguous LOW chain has gain <P0. Set
    kmax=floor(log u/[8 log(2 ell)]),
    D1=sqrt(B), D2=B exp(-u^.75),
    kappa=max(2,floor(u^.25)).
For large X, D1<D2<Q and kmax D2+(kmax+1)P0=o(Q).

For two CONSECUTIVE original natural HIGH completed events at C and A with selected primes p,q, compress the intervening completed events into h<=kmax nonLOW labels q_i and h+1 even LOW-gain offsets e_i in [0,P0). Let D be the radical of the q_i, i.e. product of DISTINCT labels, D=1 for an empty word. Their intermediate gain E=A-(C+p-1) is fixed by the word and <=h D+(h+1)P0=o(Q) if D<=D2. In particular the intermediate gains may far exceed any fixed power of log B. This statement is an upper bound, not an assertion of a large realized example. All intermediate events are nonHIGH by consecutive natural HIGH definition. Their own labels need not be smaller than a fixed polylog scale. The endpoints p,q are distinct, since if p=q the two divisibility signs imply p divides p-1+E+tau-sigma, which is p plus a nonzero odd integer of magnitude <p. All q_i are distinct from p since D<Q.

## 2. Spatial support, two uniform bounds

For fixed p, initial sign sigma, word, LOW offsets and intermediate side choices, write C=p a-sigma with a odd. For each distinct intermediate label q_i, its recorded divisibility condition restricts a to one residue modulo q_i. Repeats are either consistent or impossible; never count the product with multiplicity. Thus candidate C lie in one progression modulo 2pD or there are none. Initial and final natural HIGH imply all four forms
    a, p a-2 sigma, p a+p+E-sigma-2, p a+p+E-sigma
avoid all odd primes below B^(1/8). Offset differences are nonzero for large X. Excluding pD and their product of differences, along with 2,3,5, leaves exactly four forbidden classes at good sieve primes. The logarithm of the excluded product is O(u). The explicit Selberg bound of the cited parent notes gives, uniformly,
    # C << X ell^4/(p D u^4) for D<=D1,
    # C << X ell^4/(p D u^3) for D<=D2.                      (1)
Use z=floor(B^(1/40)) in the first range and z=floor(exp(u^.75/40)) in the second, as in the earlier notes. The errors O(z^8) are absorbed by the respective progression lengths >=c sqrt(B) and >=c exp(u^.75), with the logarithmic factors. The second bound need only be used on D1<D<=D2.

The sum of 1/D over all words of h<=kmax, all signs and LOW offsets is <=u^(1/3), by the parent combinatorial estimate (new label reciprocal cost O(ell), old repeated label at most h choices, LOW offsets at most P0+1 each). There are at most four possible final HIGH labels q at any fixed A, since each of A±1 is O(X) and Q³>>X. Sum (1) over p>=Q using sum 1/p=O(ell/u), and include this final factor. The counts of relaxed spatial keys (C,p,word,q), including intermediate sign and offset data, are bounded by
    S1 << X u^(1/3) ell^5/u^5,
    S2 << X u^(1/3) ell^5/u^4.                               (2)
These are counts with multiplicity of words, not merely distinct C. Crucially they are independent of time and mass. Neither the final adjusted phase nor actual path realizability is used in (2).

## 3. Deterministic phase slots and summable mass caps

For the initial high event with posthorizon C+p-1 and exit parity s, write
    2v-(C+p-1)-6s=2p j,  j>=0 integer.
Parity s is fixed by the eligibility sign of p at C. Thus for each spatial key and j there is at most one initial exit time v. Its actual completed exit slot consists of all original tags executing that jump, including distinct recorded arrivals. Once the initial jump is executed, the physical future MIN path is deterministic until each original tag's own stop. If two tags execute the initial jump and both complete a next natural HIGH event, their intermediate completed lists and that next event, including its exit time and adjusted phase, agree exactly. The existence of a shorter prefix ending earlier does not change the completed continuation of the longer tag. Hence an actual initial exit slot has at most one cohort of tags completing the next HIGH in the admitted word classes. The cohort is a subset of the full initial and final slot masses; some initial members may stop before the second event. No multiplication by the number of possible final phase indices is needed. Do not use the cohort size as an upper bound on all initial visitors.

Use summable weights
    f(j)=1/[(j+1)(1+log(j+1))²], j>=0.
In particular f(0)=1, and the sum over all nonnegative j is bounded by an absolute constant by the integral test. No upper cutoff on j is required. For the two disjoint radical classes put
    m1(p,q,j)=H u^(11/3) f(j)/[kappa (p+q) ell^6],
    m2(p,q,j)=H u^(8/3)  f(j)/[kappa (p+q) ell^6].          (3)
For each actual cohort with 0<n_pair<=its cap, mark on every original tag of that cohort every completed event with its full gain interval contained in
    [C-kappa p, A+q-1+kappa q].
The entire sequence including all intermediate waits is marked, since E=o(Q). The halo length is O(kappa(p+q)). On each tag the union of marked gain intervals has length no greater than the sum of the halo lengths. Since w<=3(p-1), the sum of original actual clock in the union is bounded by the sum of O(kappa(p+q)n_pair) over eligible cohort keys. Combining (2), (3), and the summable f gives
    W1 << S1 * H u^(11/3)/ell^6 = O(NT/ell),
    W2 << S2 * H u^(8/3)/ell^6 = O(NT/ell).                 (4)
In particular their union is o(NT). No cap on the total original mass per horizon, no stable-strand assumption for payment, and no pair energy condition. Count overlapping halos and older masks by priority; never recompute paths or masses on a reduced ensemble. This generalizes the short two-RESET halo to compressed words and permits either endpoint to be nonRESET.

## 4. Surviving ancestry thresholds

If an original incidence at either endpoint of an admitted pair survives the halo mask, the exact paired cohort exceeds the corresponding cap (3). For an initial RESET j=0, uniformly in high p,q, this implies
    D<=D1:        n_pair >> B u^(19/6)/ell^6,
    D1<D<=D2:     n_pair >> B u^(13/6)/ell^6.                (5)
Indeed H=Theta(B²/u^.25) and kappa=Theta(u^.25). For p,q comparable to B these are the cap scales themselves. For a smaller p+q the threshold increases. The first threshold exceeds the previous short paired-RESET threshold B u^(11/4)/ell^6 by u^(5/12), and applies to a larger word class including LOW chains and some medium-scale intermediate primes and a nonRESET final event. This is not a strict set inclusion of all previous short arbitrary-background patterns (their nonLOW count or radical could exceed the word restriction). Apply both masks by union. The second threshold is smaller than the previous short-pair threshold but reaches radicals B^(1-o(1)); tradeoff from the shorter sieve quotient. For fixed positive j both scales are multiplied by f(j)>0; for growing j the exact weight matters.

As in f97bec51, a prime-root interval of horizon length z contains O(z/log z) possible source tags. For initial RESET and D<=D1 take z=c B u^(25/6)/ell^6 with sufficiently small fixed c. Then at most half the minimum paired mass in (5) can originate within z of the initial C. The old original entropy-window and endpoint masks give much more: on a retained focal tag at either endpoint, choose an actual recorded vertex in [C-z-B,C-z], which exists since z=o(T/(u ell²)) and E,p,q=O(B). The full actual true-tick segment from this vertex through the final poststate lies in that focal window. Applying the existing intersection lemma to the full group at the initial last occupied tick (mass >=n_pair) shows that at least (1-exp(eps)eps)n_pair, eps=1/ell, members of the actual paired cohort share the earlier physical state and the entire segment. Inclusion of both poststates ensures they execute both jumps. This is actual inherited ancestry, not an independence assumption on root positions. It extends the earlier z=Theta(B u^(15/4)/ell^6) for short RESET-to-RESET. No bound on how many such persistent heavy groups or on their total clock follows solely from their mass and span. An analogous statement with z=c u times the minimum cap applies at fixed j in the second class; no uniform statement with growing j is needed.

## 5. Adaptive canonical age

The previous note removed all high RESET waits ending at canonical age a=v-t_c>B sqrt(u), with t_c the last actual canonical point strictly before v. For any original tag these half-open intervals [t_c,v) of successive high RESETs are disjoint, by the exact even-RESET bridge (<=7 ticks and <=8 gain, only selected 3 or 5 before the next canonical point) or immediate odd RESET. The original root is canonical. The bridge can be truncated by a stop, but if a later high RESET exists the bridge has been completed. This is the same proof as in f97bec51, including virtual canonical points inside waits.

At the RESET itself, d_post=6s<=6 and d_pre>=0 imply the stronger actual whole-wait bound
    2w=p-1+d_post-d_pre<=p+5, hence w<=p for p>=5.
It holds even if the last canonical point occurs inside the wait. For any lambda>0, remove the whole original high RESET wait if a>lambda p. Its cost w<=p<a/lambda. By disjoint ages, the sum over all original tags is
    W_adaptive <=3NH/lambda.
Taking lambda=sqrt(u) gives O(NT/sqrt(u))=o(NT), with no mass cap. The new age threshold p sqrt(u) is never larger than B sqrt(u) and improves by B/p near the bottom Q. Any surviving high RESET now has an actual preceding canonical point at age <=p sqrt(u) and horizon distance from its posthorizon <=2p sqrt(u)+6. The age rule is not a proof of small total canonical-arc clock and does not cover every nonRESET event. This adaptive extension is a paper deduction from the already audited disjoint-age identity, not implemented by the new standalone audit.

## 6. Residual target and limitations

Apply (4) and the adaptive-age payment to the preceding exact original-clock ledger by priority. No-twin lower bound W_all>=N(T-6)/2 and the sufficient condition liminf (A_rem+L_rem)/(NT)<1/2 remain valid on the smaller residual. The new result permits much heavier inherited groups than the moderate mass cap used in the initial word sieve, and removes both high endpoints and nonhigh background clock. It does not eliminate all old RESET groups: high-mass cohorts above (3), words with h>kmax or D>D2, absent next high events, and the remaining nonHIGH and other HIGH clock are open. In particular the new arithmetic support estimates are not a global upper bound on occupation of an already formed giant cohort. No claim that the conjecture is proved, no external novelty claim, no Lean verification. Main and independent branches unchanged.

## 7. Diagnostic audit

Source [min_unified_word_phase_halo_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/5ba502f0591c6ec77f0a52aa84068f3468d90887/research/min_unified_word_phase_halo_audit.mjs), commit 5ba502f0591c6ec77f0a52aa84068f3468d90887, exact remote readback. The audit function ran in available ECMAScript tool runtime, not a separate Node process.
    node research/min_unified_word_phase_halo_audit.mjs 256 1024 4096 16384 65536

Finite parameters T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), high r>3 and 2r>p, P0=6, D1=floor(sqrt B), D2=floor(B^.8), h<=2, kappa2, cap12B/[(p+q)(j+1)] times2 in the first radical class. Stress h<=3,kappa3, multiplier32. Restrict initial p>D2 and p>kmax(D2+P0)+P0 for finite geometry; this is deliberately strong and makes the first three tests vacuous for the new cohort mask, and stress has FEWER eligible initial centres due to the stronger geometry restriction. This is not a comparison of stress as a superset. All six runs passed. Diagnostic cap uses harmonic weights, not the analytic summable f; the finite tests do not verify the infinite-index sum or analytic sieve constants. Verify actual MIN by literal gcd at X256/1024 (431 and1239 comparisons), exact phase of every completed event, actual compressed LOW offsets and intermediate congruences, four-form roughness on actual pairs, deterministic common suffix keyed by initial exit slot, endpoint mass inclusion, unique departure formula, halo coverage and union accounting. No relaxed arithmetic support census, no cumulative previous masks, no entropy or adaptive-age implementation.

| X/mode | actual pair groups | eligible | heavy | marked full clock | marked HIGH |
|---:|---:|---:|---:|---:|---:|
|256|0|0|0|0|0|
|1024|0|0|0|0|0|
|4096|0|0|0|0|0|
|16384|4|4|0|6973|3991|
|65536|27|23|4|85986|64476|
|65536 stress|2|2|0|7221|6246|

Largest normal: 5709 roots,140255 completed events,2395330 raw clock,1380549 high. 221 actual qualifying paired tag incidences,71 nonempty words,53 extended radical incidences,85 nonzero initial phases,144 nonRESET successors. 118 word congruence,5892 small-prime roughness and339 LOW offset checks. 27 groups, 23 eligible (21 RESET start,2 positive start,6 extended radical,10 nonempty word,9 nonRESET successor). 109 eligible pair incidences,38 in the extended radical class,47 with nonRESET successors. 4 heavy groups,112 tag incidences, maximum mass43. Whole halo union85986 including64476 HIGH and21510 nonHIGH, of which29245 RESET-ending HIGH; 2888 marked events. All 109 eligible intervals completely covered. Remaining high1316073 in this isolated diagnostic. The actual spatial keys happened to have only one observed phase variant in each group; no nonvacuous multiple-initial-phase example in this test. Stress checks 9 actual pair incidences and marks7221 clock, but does not exercise extended radicals or positive initial phase. Finite results are not asymptotic rates.
