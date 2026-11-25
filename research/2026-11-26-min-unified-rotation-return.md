# Rational-rotation time CRT and all-mass same-high-label return deletion

2026-11-26 JST. Continues [0fadbb6a0539](https://github.com/tara-sooo/A166944-Lean/blob/0fadbb6a0539454d77f9fa51e31d942951724bfc/research/2026-11-26-min-unified-multi-intermediate-clock.md) and [d0cdbdadf663](https://github.com/tara-sooo/A166944-Lean/blob/d0cdbdadf6634e25fa9329d01ece2a68f9a877bc/research/2026-11-25-min-unified-intermediate-word-crt.md). Current independent prime-root head [1a4005f2f336](https://github.com/tara-sooo/A166944-Lean/blob/1a4005f2f336ede61cca1a9656c158a559338b72/research/2026-11-26-min-prime-root-small-phase-diamond.md) read, including shifted two-prime CRT and translated-prefix lemma. Stable-heavy head e1ad9e2b434c unchanged, previously read. Two new linear deductions on the unified branch. First remove the +1 CRT boundary loss at large products pq using Dirichlet rational approximation, paying exceptional rational rotations by a separate spatial CRT. This raises the cheap-successor threshold enough to force the first nonLOW successor with q>=Q to be natural HIGH on retained moderate-mass strands. Second, for any original mass, pay entire intervals of consecutive equal HIGH labels with a single dominant intervening event and polylogarithmically small other gain. No general twin-prime proof or Lean compilation.

## 1. Ensemble and candidate transitions

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN gain-stopped prefixes and terminal snapshots unchanged. Natural HIGH: selected p>=Q, least eligible r(C)>p/sqrt(log p). Every completed gain p-1, actual wait w<=2r<=3(p-1). Actual tick mass b(C,j) counts original tags with completed waits occupying (j,C), excluding terminal snapshots. At fixed C all occupied times and all completed exit times lie in an interval of length O(H), from 0<=2j-C<=6+5H and w<=2B. High horizon support O(X ell/u^3), and at most four high p per C, by the prior least-factor and divisor bounds. Original tag multiplicity at any completed C is O(H/u) by prime-origin locality and the uniform prime interval upper bound.

Use P0 the largest even primorial <=ell, with LOW labels its odd prime factors; every contiguous LOW chain has gain <P0 and elapsed time <3P0. The original moderate stable strands n_g<=u^(7/3)/ell^2 have original b(C,j)<=Mstar=2u^(7/3)/ell^2 at each retained focal tick after entropy trim.

A high hit (C,p,v) has departure v in alpha(p,sigma) mod 2p, where alpha(a,-1)=0 and alpha(a,+1)=a+2, with sign sigma unique from p|(C+sigma). Its first following nonLOW event, if present, has prehorizon A=C+p-1+e, even 0<=e<P0, selected q and sign tau. We count relaxed keys (C,p,sigma,e,q,tau) with both spatial divisibilities, C,A in the original horizon domain and initial high least-factor predicate. Restrict q>=B^(1/8). There are O(P0) keys per C because p has at most four choices and each A±1=O(X) has O(1) prime divisors >=B^(1/8). The labels p and q are distinct: otherwise p divides p-1+e+tau-sigma, which is p plus a nonzero odd integer of magnitude <p for large X.

For theta=4/sqrt(u), a cumulative-cheap transition through q means 1<=v'-v<=theta q, where v' is the actual departure of q. Its necessary residue constraint is
    v=alpha(p,sigma) mod 2p,
    v+t=alpha(q,tau) mod 2q for some integer 1<=t<=theta q.      (1)
The mask may use relaxed arithmetic candidates rather than actual future transitions. The associated initial occupied ticks lie in [v-2p,v).

## 2. Small-q time CRT

When q<Q, pq<=B Q=O(B²/u)=o(H). For each t in (1), ordinary CRT gives at most O(H/(pq)+1) possible v in the full original time slab. Thus there are O(theta q (H/(pq)+1)) possible exits, and at most
    O(p theta q (H/(pq)+1))=O(theta H)                        (2)
candidate occupied ticks for a fixed key. This is the old counting argument with the +1 term harmless on this range, but now using the larger theta.

## 3. Large-q rational rotations

For q>=Q choose K=floor(u^4), A0=ceil(sqrt(u)). Dirichlet approximation gives coprime integers a,b with 1<=a<=K and
    |a p/q - b| <= 1/K.
If a nonreduced pair is obtained, reduce it, preserving the inequality. Call a prime pair exceptional if ANY such approximation has a<A0. Otherwise choose any approximation; then a>=A0. In the list of v satisfying the first congruence in (1), write v=alpha(p,sigma)+2p n for n in a consecutive interval of length L_v=O(H/p+1). The second condition restricts (p n/q + constant) modulo 1 to a circular interval of length at most theta/2. For any a consecutive n, relative to the first n of that block, the rotation p/q differs from the rotation b/a by at most 1/K at each of the a terms. Since (a,b)=1, the latter points form an exactly equally spaced grid. Consequently at most
    a(theta/2+2/K)+2
of these a terms can satisfy (1), including an interval crossing 0. This bound also covers a final shorter block by enlarging it to a full block. Partitioning the whole consecutive list into blocks of length a gives
    # candidate exits << (L_v+a)(theta+1/K+1/a)
                      << (H/p)/sqrt(u),                    (3)
since H/p>>K uniformly and a>=sqrt(u). Multiplying by 2p to overcover every occupied tick of every candidate exit gives O(H/sqrt(u)) possible ticks, the same as (2). There is no +1 loss of order pq/H on this nonexceptional range, no equidistribution assumption on actual paths, and no average over time origins. The arbitrary phase of the initial block is included in the constant shift of the circular interval.

## 4. Absolute spatial CRT payment for exceptional rotations

For fixed p in [Q,B], an exceptional q in [Q,B] satisfies |a p-b q|<=q/K for some 1<=a<A0 and positive integer b<=a B/Q+1=O(a u+1). Positivity follows from p/q>=Q/B>=1/u and 1/K<<1/u. For each fixed a,b the allowed q lie in [ap/(b+1/K), ap/(b-1/K)], intersected with [Q,B]. The sum of 1/q over all integers in this interval is
    O(1/(b K)+1/Q).
This follows from relative interval length O(1/(bK)) and an endpoint error at most 1/Q, without requiring the q integers to be prime in the upper bound. Summing over b and a gives
    sum_(exceptional q>=Q) 1/q
      << A0 ell/K + u A0²/Q
       = O(ell/u^(7/2)).                                    (4)
All constants are uniform in p. Since p!=q for the candidate transitions, their spatial congruences C+sigma=0 mod p and C+p-1+e+tau=0 mod q give one residue mod pq, hence O(X/(pq)+1)=O(X/(pq)) possible C. Count all integer C, even dropping roughness, then sum over p prime, signs and e. The elementary reciprocal-prime bound sum_(p>=Q)1/p=O(ell/u) yields
    # exceptional spatial keys << X P0 ell²/u^(9/2).        (5)
This also bounds their distinct initial horizons. Pay ALL actual high ticks at a matching (C,p) with b<=Mstar, independently of their exit phase. With O(H) possible ticks per C their cost is
    W_exc << Mstar H X P0 ell²/u^(9/2)
           = O(NT ell/u^(7/6))=o(NT).                       (6)
Use P0<=ell and N=Theta(X/u). The coarse all-horizon bound is more than enough; no prime-pair lower bound or simultaneous sieve in p,q is assumed.

For all nonexceptional large-q and small-q keys, pay the actual HIGH ticks with b<=Mstar in the relaxed residue overcover (1). Count O(H/sqrt(u)) ticks per key by (2),(3). Using high support and O(P0) keys per C,
    W_rot << Mstar (X ell/u³) P0 H/sqrt(u)
           = O(NT/u^(1/6))=o(NT).                           (7)
The union of (6),(7) is a linear deletion, applied by priority, not a quadratic bound. Both masks could use the larger original tick-mass cap u^(5/2)/ell³, for which the ratio in (7) is O(1/ell) and (6) remains little-o. The stated moderate-strand implications use Mstar; the larger cap does not by itself guarantee stable cohort structure at that scale.

## 5. Forced HIGH successor and improved one-intermediary gap

After the new masks, every surviving moderate HIGH tick whose actual first subsequent nonLOW label q>=B^(1/8) exists satisfies
    v'-v > 4q/sqrt(u).
The elapsed LOW prefix is <3P0=o(q/sqrt(u)), so its actual q-event wait w_q>3q/sqrt(u) eventually. If q>=Q, then log q=u-O(log u); w_q<=2r(A) now implies r(A)>q/sqrt(log q). Hence the first nonLOW successor is itself natural HIGH. Equivalently, if there is at least one nonLOW intermediate event before the next actual natural HIGH hit, its FIRST nonLOW label must be <Q. This statement includes q<B^(1/8) automatically since B^(1/8)<Q. It concerns the original natural high predicate, not whether that successor survives any mask.

In particular in the one-nonLOW-intermediary sector, combine the near-linear radical deletion of 0fadbb6 with this forced-high rule. If the later actual natural HIGH hit exists, the sole nonLOW q satisfies
    B exp(-u^.75) < q < B/u + 1,    (indeed q<Q)
    W_gap >= w_q > 3q/sqrt(u) > 3 B exp(-u^.75)/sqrt(u).    (8)
The first inequality is the previous radical cutoff. This sharpens the prior q/u^.75 actual-wait lower bound and removes ALL q>=Q in this sector, not merely q with product pq below H. The gap still may have q/p tending to zero and (8) does not imply a constant fraction of the initial high clock. For multiple intermediaries only the first nonLOW label is forced below Q; the preceding cumulative multi-intermediate bound applies to the first label above its word-dependent threshold. No claim that subsequent nonHIGH labels all lie below Q.

## 6. An independent all-mass same-label return estimate

Let J0=max(1,floor(u^(1/8))), unrelated to P0 or the rational-rotation block length. Consider two CONSECUTIVE original natural HIGH events on one tag, both selected p>=Q, at prehorizons C,V. Between them suppose there is a distinguished completed nonHIGH event of selected q, and the total selected gain of all OTHER intervening events is <=J0. Allow arbitrary small background labels and number of events; do not require LOW. Write their total gains before and after q as e0,e1, nonnegative even with E=e0+e1<=J0. Thus q occurs at U=C+p-1+e0 and V=U+q-1+e1.

For large X natural HIGH implies r>3 and the prehorizons are divisible by 6. For the same selected p at two distinct rough prehorizons the difference is 0 or +/-2 mod 2p. A positive difference below 2(p-1) could only be 2, excluded by divisibility by 6. This is the global spacing lemma of the independent projected-diamond note, now applied within one actual path. Hence V-C>=2(p-1), q-1+E>=p-1, and q>=p-J0>=p/2. Also q!=p, since the initial and q divisibilities would imply p | p-1+e0+tau-sigma=p+nonzero odd integer with magnitude <p. If sigma,sigma' are the initial and final signs of p, then
    q = m p+2-E+sigma-sigma',   1<=m<=B/p+O(1).             (9)
Indeed p divides V-C+sigma'-sigma, and m=(q-2+E+sigma'-sigma)/p is a positive integer (q grows, E>=0). Thus q is within O(J0) of an integer multiple of p, and q is comparable to mp. The spatial congruences at C and U fix C mod pq, giving O(X/(pq)) possible C for each fixed p,m,e0,e1 and the three signs, since pq<=B²=O(X). We can count even nonprime q as candidates in the summation provided the CRT estimate is invoked ONLY for distinct actual primes p,q. The actual candidate q is determined by (9). Overcounting all signs and offsets costs O((J0+1)²).

For every actual source realizing such a pattern, mark the ENTIRE completed sublist from the first high event through the second high event, inclusive. This pays the intermediate nonHIGH clock too. Its total actual cost is O(p+q/sqrt(u)): the two high waits <=4p, the background waits <=3J0=o(p), and if q<Q its wait <=2q<=2p; if q>=Q it is nonHIGH so w_q<=2q/sqrt(log q)=O(q/sqrt(u)). This use of actual cheap nonHIGH time is crucial when q is much larger than p. A gain or proxy bound by O(p+q) would not give the same saving.

For each C there are O(H/u) original prime tags that could realize the pattern. Summing the above actual-clock cost, and allowing all patterns even if no original path realizes them, bounds the clock of the union of marked sublists by
    W_ret << (H/u) X (J0+1)²
             sum_(Q<=p<=B, prime) sum_(1<=m<=B/p+O(1))
                  [1/(mp)+1/(p sqrt(u))]
          << NT (J0+1)² [ell²/u + 1/sqrt(u)]
           = o(NT).                                        (10)
For the first sum use sum_(m<=B/p+O(1))1/m=O(ell) and sum_p1/p=O(ell/u). For the second use B sum_(p>=Q)1/p²=O(B/(Q log Q))=O(1) by partial summation of the elementary prime-count upper bound. The O(1) extra m terms also obey the same bound since B/p>=1. All interval union overlaps only reduce the actual paid cost; the proof does not pay a pair energy, and is valid for arbitrary original synchronous masses, including the previous very thick sector. In particular every residual high incidence which is either endpoint of such a complete return on its own original path can be removed. It covers a single nonLOW intervening event with total LOW background <2P0, because 2P0<=2ell=o(J0). Unlike close-label diamond halos, the two high events here have the SAME p at distant horizons of one path, and q need not be high or close to p (it may be near a larger multiple). No two-path divergence hypothesis.

A further deterministic observation: if the background consists of arbitrary selected labels with total gain <=J0 and all other intermediary events have the same q repeated h times, with 1<=h<=k=floor(log u/[8 log(2ell)]), then high spacing forces h(q-1)+J0>=p-1 and hence q>>J0. Two consecutive q occurrences in this compressed list have prehorizon difference q-1+e, 0<=e<=J0; this is between 2 and 2q-2 strictly for large X. For ANY even prehorizons of the same odd label q, a positive difference below 2q-2 can only equal 2, whether rough or not. Thus h>=2 is impossible. The case h=1 is exactly the paid pattern (10). This is a repeated-single-label restriction, not a proof that arbitrary mixed-label intermediate words are rare.

## 7. Remaining sufficient condition

Add (6),(7),(10) to the previous actual-clock ledger by priority. The previous sufficient condition liminf_(dyadic X -> infinity) (A_rem+L_rem)/(NT)<1/2 still implies twin-prime infinitude by the exact no-twin gain/deficit lower bound. The new condition uses smaller exact residuals and no new async energy premise. Moderate surviving high gaps now have first nonLOW intermediate below Q, when a next natural high exists and there is a nonLOW intermediary. In the one-intermediary sector this yields (8); and regardless of mass, a same-p return with a single dominant intermediate and small background is paid by (10). Large-mass gaps with different labels, mixed intermediate words, gaps with many events and the full non-HIGH clock remain unresolved. The new estimates do not bound the complete sufficient condition. No Lean execution or external novelty claim. Main and independent branches untouched.

## 8. Diagnostic audit

Source [min_unified_rotation_return_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/401dfa711d19707bfe3d27ca73d17ff7065347f1/research/min_unified_rotation_return_audit.mjs), commit 401dfa711d19707bfe3d27ca73d17ff7065347f1, exact remote readback. Executed the audit function in the available ECMAScript runtime, not a separate Node process.
    node research/min_unified_rotation_return_audit.mjs 256 1024 4096 16384 65536

Six tests pass: five normal diagnostics and a stress at X65536. Finite T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), high r>3 and r>p/2, R=max(5,ceil(sqrt B)), P0=6, K=16,A0=3, theta=.4, mass cap8, J0=16. Stress uses theta=.8,J0=32, same paths. Restrict time candidates to p>P0+2, return patterns to p>2J0+8 for finite geometry. The diagnostics are not analytic parameters and do not test the forced-HIGH implication (8) at the asymptotic threshold. Tests actual prime-root MIN, literal per-tick gcd at X256/1024 (431 and1239 checks), deterministic tick mass, all relaxed first-nonLOW candidates at ACTUAL high centres, least-denominator Dirichlet approximation, exact grid block count with arbitrary actual slab phase, all actual cheap successors, retained time inequalities, relaxed spatial support and actual equal-p return patterns, same-p spacing, exact whole-sublist union cost partition. No asymptotic sieve or prime-interval constant tested. No cumulative prior stable-strand or entropy mask; the two new finite masks are measured separately, not added as though disjoint.

| X / mode | raw HIGH | exceptional rotation paid | other time paid | actual small-background equal-p returns | full return actual clock |
|---:|---:|---:|---:|---:|---:|
|256|1753|66|441|0|0|
|1024|3908|292|1576|0|0|
|4096|37458|9014|10510|0|0|
|16384|195474|26465|42344|0|0|
|65536|1380549|161064|215306|0|0|
|65536 stress|1380549|161064|362368|16|5638|

Largest normal: 5709 tags, 140255 completed events, 2395330 full actual clock, 1396 distinct high centres. 3477 Dirichlet checks (2983 good,494 exceptional candidate occurrences), 1848 small-q candidates, 34365 grid blocks and210098 explicit exit-rotation checks. 598 actual cheap successor incidences, of which206 good,56 exceptional and336 small-q;386 retained low-mass actual cumulative time checks. Normal return support48 relaxed patterns, no actual qualifying return. Stress return support128,16 actual return occurrences, minimum observed q/p=.6853932584, exact marked union5638 actual clock including3206 HIGH and2432 intermediate. Stress actual cheap successors1225, retained checks65. The all-mass return theorem is exercised in stress, not normal. Finite counts establish geometry and accounting, not asymptotic frequency.
