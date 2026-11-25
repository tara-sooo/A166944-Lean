# Sparse predecessor quotas and physical first-merger transfer for medium clock cost

2026-11-25 JST. Continues 9780b569b7292099a88af73dd50d68d756a6d31e on research/min-prime-root-repeat-energy-2026-11-25. Instead of estimating every same-cell repeat pair by Cauchy, assign each noninitial medium hit's actual clock and LOW cost equally to a bounded number of preceding hits. This gives a linear clock criterion and cancels the arithmetic recurrence capacity in the previous endpoint transfer. A restricted physical first-merger potential then pays small first-merger contributions to the medium obstruction. Neither the full remaining medium cost nor the high energy has been bounded. Paper proof and finite audit; no Lean compilation or external novelty claim.

## 1. Setup and sparse quota

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts in [X,2X), Q=ceil(B/u). Original MIN prefixes stop at gain >=T, original terminal or cutoff. The sum of selected weights and r costs is <=1.5NH. Freeze the medium set I_m of actual selections y<p<Q (or any subset after already-paid accounting marks). At each hit with least eligible prime r attach the original subsequent LOW block as before. Denote its actual clock+attached LOW cost by a(e), so 0<a(e)<=w_r=r+1.5L, and sum a(e)<=1.5NH. Initial and high-attached LOW are negligible. The earlier relative-cheap deletion and high-energy definitions are unchanged.

Use the aligned horizon cells A_r=ceil(w_r² u^1.5) of 711a0db. For P<=r<2P, P dyadic, l_P=log(2P), define the integer quota
    k_P=ceil(u^1.5/ell^1.25
             + u^1.5 l_P (1+L/P) (P/Q)^.25/ell).
For each M,r,cell discard the first min(k_P,n) medium hits (this pays their costs; no dynamics rerun). For each remaining hit E, choose exactly its last k_P preceding hits C in the same frozen list and cell. Assign the directed incidence (M,r,C,E) cost a(E)/k_P. Each later hit's cost is exactly partitioned into its quota edges. No diagonal and no repeated use of a fixed (M,r,C,E). All selected pairs remain in the original arithmetic pair support. This is an accounting scheme, not a claim that all such repeats are consecutive MIN events or that all n(n-1) pairs are needed.

The first-use budget follows from
    sum_{r in band} w_r (ceil(H/A_r)+2)
       << H/u^1.5 * P/(l_P(P+L)).
Indeed w_r²=O(Q²)=o(H/u^1.5) uniformly. Using the baseline term of k_P, the reciprocal log sum over dyadic bands O(ell), and the geometric sum for its second term, the total first-use cost is
    R_first << NH(ell^(-.25) + ell^(-1) + ell/u^1.5)=o(NT).
No assumption on actual repetition frequency; this first-use cutoff can grow much faster than the previous u^.25.

## 2. Short edges and enlarged caps paid directly

Use the old distance D_r=max(1,floor(r u^1.5 log²(2+min(r,u))/ell^1.5)). The uniform two-form interval sieve in 40d101b bounds the number of arithmetic r-horizons in either direction in distance D_r by O(u^1.5/ell^1.5). The proof for the backward interval is identical: fixed r, sign, quotient interval of the same length. Thus at most this many of each later hit's chosen predecessors are short. Since k_P>=u^1.5/ell^1.25,
    R_short <= O(ell^(-.25)) sum a(e)=o(NT).
This uses the actual allocated cost and does not assert a negligible raw short moment.

For a long key (r,C,E), let V^q_r(C,E) be the number of actual selected quota edges there. This is a subset of the previous full common-source intersection. Each of its tags has cost <=w_r/k_P. Use the enlarged band cap b_P of 9780b569: b_P=max(1,floor(b_P^*)), where
    b_P^*=(B/P)^2 u^(-1.5) sqrt(P/Q) f_P,
    f_P=l_P^6/(1+log l_P)^4 for P>=u²,
        l_P²/(1+L/P)^2 otherwise.
From the previous arithmetic support count K_P,
    b_P K_P << X B² sqrt(P/Q) l_P/P.
The quota's second term implies
    w_r/k_P << ell P/(u^1.5 l_P) (Q/P)^.25.
Consequently the entire allocated cost on long keys with V^q<=b_P is
    sum_P O((P+L)/k_P * b_P K_P)
       << X B² ell/u^1.5 sum_P (P/Q)^.25
       = O(NT ell/u^.25)=o(NT).
The cap is now on the SPARSE common-source set, not on the full intersection. It can cover keys whose full intersection is much larger. One may independently use the previous c'_r cap: w_r/k_P << (B ell/u^3.5) lambda_P for lambda_P=sqrt(P/Q) log Q/l_P, so its known negligible weighted moment gives negligible direct clock cost. We do not need that cap for the new criterion.

For the same growing family d_j=ceil(H/2^j), j<=floor(log_2(u)/4), every key occupies <=J_d=ceil(H/(2d))+2 source cells. Let m_{P,d}=max(1,floor(b_P/J_d)). For a key, pay all tags in each original sparse source cell with <=m_{P,d} tags; its total covered tag count <=b_P eventually. Union over O(ell) scales costs O(NT ell²/u^.25)=o(NT). These are fractional allocations of later-hit costs; an event can have edges in several classes. No claim that deleting all their endpoints would be cheap. No iterative recomputation of the sparse lists.

Let R_q denote the sum of the remaining allocated long-edge costs. We obtain
    R_med <= o(NT) + R_q.
The earlier weighted residual condition on the full list suffices for R_q=o(NT) too (if desired include its old cap), since sparse subsets and the old cell caps only reduce the weighted counts, and w_r/k_P<<B ell/u^3.5 lambda_P. In particular O(NBu³) weighted residual implies O(NB² ell/u^.5)=o(NT). The quota criterion, however, only counts chosen edges and uses their direct cost.

## 3. Exact normalized phase ledger and improved later-endpoint transfer

Fix the finest scale d. For each remaining key and source cell, let A be the original sparse common-source set of size n, S its surviving focal tags. If S nonempty n>m=m_{P,d}. For each M in S distribute its allocated cost a(E)/k_P equally among the n-1 OTHER tags in A (not just S). Thus the directed contribution for M,M' is
    a(E)/(k_P(n-1)).
It sums to precisely the original allocated cost of M. For a pair, equality of physical times at C implies equality at E, by determinism and both original paths reaching E. Classify early sync (equal at C), new sync (different at C but equal at E), or async (different at E). This gives R_q=R_early+R_new+R_async exactly. No assumption that a partner's own quota cost equals the focal's; no use of independence.

Crucial difference from 9780b569: for a fixed directed source pair M,M' at later horizon E, the focal M has only k_P chosen predecessors in its cell. Every repeat contribution involving this M,M',E comes from one of those choices. Also n-1>=m, hence its sum over all keys with later endpoint E is at most
    sum_C a(E)/(k_P(n-1)) <= a(E)/m <= w_r/m.         (1)
No factor U_r for the total number of arithmetic predecessor horizons appears. BOTH synchronous classes can be transferred to the LATER endpoint, not separately to C and E. The condition that both tags have selected quota edges is used to define A, but relaxing it after transfer gives a valid upper bound.

In particular R_early+R_new is bounded by the ordered equal-physical-time medium endpoint energy with weight w_r/m, within the fixed source cells, and R_async by the analogous different-time energy. These are clock-scale energies, not the previous unweighted or lambda-weighted repeat moment. One may use exact transferred charges rather than the relaxed energies, and this is what we do below. For a fixed focal tag at E, if its entire current projected cell mass (or its current physical-time group mass, for sync only) is <=a_*, then that part of its transferred charge is <=a_* a(E)/m. This gives an absolute o(NT) exclusion for thin endpoint groups with a_*/min_P m=o(1), by sum of actual medium costs. This last inequality is not separately audited; follows directly from (1).

## 4. Unconditional restricted first physical merger exclusion

Let
    m_* = u^6.25/ell^4.
Uniformly for all nonempty P and the finest scale of section 2,
    m_{P,d}/(1+L/P) >> m_*.
Proof: for P>=sqrt Q, l_P~u, 1+log l_P~ell, and b_P^* >= c u^6.5/ell^4 from its explicit P^-1.5 dependence. J_d=O(u^.25). For P<sqrt Q, the positive power of B in (B/P)^2 sqrt(P/Q) dominates all fixed powers of u, including the factors from L and the small-band formula. Floors and min1 are harmless for large X. Thus for every medium hit, w_r/m_{P,d} << r/m_*.

For any source pair that meets physically, charge all its directed synchronous later-endpoint contributions to its FIRST physical meeting v. Along the subsequent common original path until either stops, the sum of natural medium weights w_r/m_{P,d} is O(H/m_*), by the original total r-cost. A given ordered pair's assigned cost is no more than this sum, by (1); the unordered pair's two directions are bounded by twice it. This bound holds also for arbitrary frozen source-specific medium subsets, by relaxing to all natural medium events. It does not claim equality of independently thinned tails. The first merger may precede C or lie in (C,E]; both classes are covered.

Restrict the original physical forest to each of the fixed source cells at scale d, with all original vertices including terminal. The cells form a disjoint partition of sources, so the sum of their root counts is N, not NK_d as in the earlier two-cell potential. Every transferred pair belongs to one such cell. At each physical vertex let n be the number of that cell's original visiting tags and a_i incoming predecessor masses. Use f_m(n)=n² for n<=m, 2mn-m² otherwise. As in ae921f73, D=f_m(n)-sum f_m(a_i)>=0 and sum D<=2m N over all restricted forests with source starts and expiry losses. Thus at first meetings with cell-local total mass n<=m, the number of unordered first pairs is <=mN. Take m_a=max(1,floor(u^6/ell^4)). The total allocated synchronous medium cost for these pairs is
    R_sync,small << m_a N H/m_* = O(NT/u^.25)=o(NT).  (2)
This excludes even pairs that later belong to enormous synchronized groups. The first physical meeting is the same in the restricted forest and the original trajectories; only its counted mass is restricted. Global first-merger mass need not be small.

The prior hierarchical same-incoming-label potential gives the same bound for same-label first-meeting pairs with label aggregate <=m_a in that cell even if n>m_a (charge both cases to the same D). Also the existing light-branch admission lemma can pay O(m_a N) ordered first pairs in each fixed cell, hence O(NT/u^.25) allocated cost by the same transfer. These are paper extensions of (2) using the previously established general potential; the audit below tests raw total mass only.

A tail-adaptive refinement is available: give each original state the natural outgoing weight w_r/m_{P,d} if it is a medium hit, otherwise zero. The remaining natural tail is nonincreasing and <=H_0=C H/m_* for a sufficiently large absolute constant C. For a meeting pair, common weight along its natural suffix equals the minimum of the two natural tails. Each transferred contribution can be embedded as a fractional subinterval of its corresponding natural later-hit interval by (1). Apply the earlier tail-layer potential to the cell-restricted forests at each x with cap max(1,floor(m_a sqrt(H_0/x))). The small-total plus hierarchical small-label natural layers cost O(N m_a H_0)=o(NT), upper bounding corresponding transferred slices even when raw first-merger mass exceeds m_a. This refinement is not separately audited in this turn; it is the general ae921f73 proof with these new nonnegative state weights. The natural (not source-specifically thinned) tail is needed for the common-suffix equality.

## 5. Joint residual criterion

At the exact direct quota level, after the above exclusions let R_sync,bad be the residual of both physical sync classes and R_async,bad the residual different-time class. In the basic version of (2) the first merger of a residual synchronized pair must have cell-local mass >m_a. In the optional tail/hierarchy/admission versions it must evade those additional criteria. These conditions concern formation of the actual original physical group, not merely current projected multiplicity. The synchronous proof does NOT control all heavy first meetings, and the asynchronous class does not have a common deterministic suffix.

With the earlier high residual (using F=T²Bu), the new joint OPEN sufficient conditions are
    R_sync,bad + R_async,bad = o(NT),
    E_phys,admitbad + E_async,bad = o(F).
They imply total R=o(NT) on the same unbounded dyadic windows, and thus the earlier gain-prefix contradiction without twin terminals. The medium target is now a direct fraction of the actual medium clock, instead of a full square-moment target. The new absolute exclusions are proven using the previous sieve estimates, quota budgets and first-meeting potential, not finite frequencies. No proof of either residual estimate or of twin-prime infinitude. Next: exploit the sparse predecessor relation and bounded transfer multiplicity for asynchronous pairs, and control the remaining thick cell-local physical formation using actual arithmetic.

## 6. Reproducible finite checks

Standalone ECMAScript research/min_prime_root_quota_transfer_audit.mjs, exact remote readback at 1a4b6b1715900b0d862e2ac396bf89fc6cf8f97a, blob ef23a6c5e2950b5bccac911bbf6269ab97747527 (first audit commit 6863ef15187a19a24ba18632eb5cf1c72eef0e29). Run:
    node research/min_prime_root_quota_transfer_audit.mjs 256 1024 4096 16384 65536 262144
Executed its function in available ECMAScript runtime, not a separate Node process. Initial attempt had a potential helper name collision with the audit function, corrected before successful execution or commit. Final 24 runs (four modes x six windows) passed. Original SPF MIN, literal parity-GCD checks in smallest two windows (short1183, wide1707, analytic1719, phase1707), LOW assignment, exact sparse quota costs, cell cap union, normalized focal ledger, phase coarsening, multiplicity <=k_P at later endpoint, direct transfer bound (1). For each synchronous transferred pair independently scans two original paths to find first physical meeting and compares total pair charge to min of weighted tails (an upper bound here). Exact global and restricted single-cell potential telescopes and small first-pair counts including all original roots and expirations. Floating-point cost partitions use tolerances; integer potentials exact. Does not test asymptotic constants, growing ladder, cumulative previous marks, or optional hierarchy/tail-layer extensions.

Analytic T=X/u^.25,Qm=ceil(B/u) min5, quota k_P as stated, A_r=ceil((r+9)^2u^1.5), fixed finite LOW y3,L6, b_P as previous. Three source widths ceil(H),ceil(H/u^.125),ceil(H/u^.25) approximate the ladder. Diagnostic short T=B,Qm=max(7,ceil(B/8)), k1; wide T=4B,Qm=max(7,ceil(B/4)),k2; phase T=4B,Qm=max(7,ceil(B/8)),k3, width ceil((r+9)^2/2) vs other diagnostics ceil((r+9)^2/8); D_r=3r for short/phase,6r wide; inherited diagnostic enlarged b_P and source widths H,H/2,H/4; mass cap4 short,8 wide/phase. Diagnostic parameters deliberately exercise branches; they do not satisfy the limiting first-use budget. Analytic finite first-use removes almost all clock and all remaining long edges pass band cap, hence residual transfer vacuous there.

Largest X262144 analytic: 728901 possible unordered local repeat incidences ->32958 chosen quota edges (max k40), 1844 short, 31114 long. Medium clock+LOW 6754565, first-use6740954, short748.1667, long12862.8333 (all band-covered), residual0. No inference that this fraction persists at infinity.

Largest short X262144: 18168 full pairs ->18150 quota edges; medium4846011, first4663132, short123439, long59440; band53427, thin cells127, residual5886. 64 focal edges at5 keys, 722 directed partner edges; early2528.6444, new2721.1778, async636.1778, max endpoint multiplicity1. Of sync5250 approximately, raw-small first merger692.1111, cell-small770.0667 (extra77.9556), cell-large4479.7556. Exact total sync=5249.8222, residual after cell-small=5115.9333 including async. 293 synchronous source-pair tail checks; global potential81207=101597-20390, cell potential71443=91833-20390; small-first unordered pairs13986 global,14327 restricted,48 actual transferred pairs cell-small. Relaxed endpoint envelope35333.3333, much larger than actual5886.

Largest phase X262144: 105618 possible local pairs ->11784 chosen edges, medium6414220, first6385246, short4864, long24110, band23783.3333, cells32.6667, residual294 all early-sync. 126 focal edges at2 keys,7812 partner edges, max endpoint multiplicity2 (k3),1953 synchronous tail checks; restricted small15.6559, residual278.3441. At phase X16384 residual656.6667 includes async263.9494, cell-small241.1744 (extra80.6966), cell-large151.5429, maximum multiplicity3. Wide largest only38 chosen edges all short. These checks establish finite identities and inequalities, not asymptotic suppression of the residual. Main and other branches unchanged.
