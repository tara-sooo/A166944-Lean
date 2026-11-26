# Hypothetical infinite MIN worlds III: exact local clock capacity and phase-coupled bypass runs

2026-11-26 JST. Independent continuation of [af04238](https://github.com/tara-sooo/A166944-Lean/commit/af04238f36bd2c18be5b0f0bedf90a8c85d5475f). Sources: previous [scale and tomography](https://github.com/tara-sooo/A166944-Lean/blob/af04238f36bd2c18be5b0f0bedf90a8c85d5475f/research/infinite-orbit/scale_and_tomography.md), direct [2a47be1](https://github.com/tara-sooo/A166944-Lean/blob/2a47be177db12d7fdcdc99daf9dfe7be0403da34/research/2026-11-26-min-direct-grouped-cut-sieve-and-all-label-corridors.md). Paper deductions and finite computational diagnostics, not Lean-verified or an external novelty claim. Goal: impose the missing standard-integer neighbor factors and full earliest-clock rule on the high-label, long-wait, safe-endpoint scalar survivor. No source-density or global finite-twin conclusion is assumed in the finite experiments.

## 1. Exact phase-free local maximum waiting time

Let H>=4 be an even standard integer horizon and let F_0,F_1 be the sets of distinct odd prime factors of H-1,H+1, respectively, restricted to p^2<=H+1. They are disjoint because gcd(H-1,H+1)=1. Define residues a_0(q)=0 and a_1(q)=q+2 modulo 2q. Each eligible factor q on side s has precisely one clock in each period 2q, at n=a_s(q) mod 2q. Side s fixes n mod2. On any actual adaptive MIN plateau, the earliest future clock wins, with least prime breaking ties.

For selected p in F_s, define
    W(H,p)=min( {2p} union
       {2q-2: q in F_s, q<p} union
       {2q: q in F_s, q>p} union
       {2q-1: q in F_(1-s)} ).                         (1)
Then W is the EXACT maximum wait at this horizon for which p can be selected, when the starting time t is allowed to vary over integers. In fact every integer 1<=w<=W is realizable, even with t arbitrarily large.

Proof: let arrival n=t+w be a p clock. The previous strict clock of q is n-d_q, where d_q is the positive representative of n-a_i(q) modulo 2q (use 2q for zero). If q<p ties at n, p cannot be selected. Otherwise no prior q clock may lie in (t,n), equivalently w<=d_q. For q on the opposite side, d_q is odd and at most 2q-1; same side, d_q is even and at most 2q, but for smaller q a tie is forbidden so d_q<=2q-2. The selected p itself has d_p=2p. This proves necessity. For sufficiency assign n parity s; impose n=a_s(p) mod p, n=a_s(q)-2 mod q for every smaller same-side q, n=a_s(q) mod q for every larger same-side q, and n=a_(1-s)(q)-1 mod q for every opposite-side q. CRT is compatible because all factors are distinct and odd. These congruences with the parity attain every corresponding maximum d_q simultaneously and avoid all smaller ties. Choose n arbitrarily large in that progression, t=n-w. No clock occurs between t and n; p wins at n. This shows exact local feasibility, not feasibility from a fixed canonical root or a bounded time interval.

Formula (1) simplifies to 2p, 2 times the smallest smaller same-side factor minus 2, and 2 times the least opposite-side factor minus 1, taking the minimum over available terms. In particular if w>=p-2 as in checkpoint II's scalar later-clock construction, every competing eligible q satisfies q>=(p-1)/2 (and same-side smaller q>=p/2). This imposes arithmetic roughness independently of the starting phase. For nonnegative deficit change only, w>=ceil((p-1)/2) is necessary and sufficient locally with (1); the corresponding lower bounds on q are weaker.

## 2. Long high edges force roughness and sparse starting horizons

Fix lambda>1, eta>0, H in [X,lambda X], p>=eta sqrt X, w>=p-2. Every prime factor q<(p-1)/2 of either neighbor would be eligible and would contradict (1). For sufficiently large X both neighbors are therefore either primes or products of two primes (count multiplicity), since three factors >=(eta sqrt X-1)/2 have product >lambda X+1. In a semiprime neighbor at most one DISTINCT factor is eligible: if a<b are odd factors and b^2<=H+1, then b^2-ab>=2b>2, impossible for either neighbor. Thus the local long high graph eventually has at most two distinct possible labels at a horizon, one from each side. This is not a claim that both neighbors are semiprime; one may be prime. Under finite twins they cannot both be prime past the last center.

Also the set of POSSIBLE prehorizons of such long high events has density o(1), uniformly over all t. For any fixed y, for large X every odd prime q<=y must avoid H=+-1 mod q. Write P_y=prod_{3<=q<=y} q. In any interval of even horizons of length O(X), the count is bounded by
    O(X) prod_{3<=q<=y}(1-2/q) + O(P_y).
Indeed H=2h, and there are exactly prod(q-2) allowed residue classes mod P_y. First let X tend to infinity at fixed y, then y to infinity; divergence of sum 1/q makes the product tend to zero. With y=c log X, 0<c<1, the prime number theorem and Mertens product as used in the direct source give O(X/(loglog X)^2), with the CRT remainder X^(c+o(1)) absorbed. The fixed-y proof needs no quantitative prime estimate. On the canonical initial root lattice H=2M-2, M odd, the same density bound holds (4 invertible mod odd q). Consequently a dense ensemble of actual canonical odd roots cannot have the checkpoint-II pure long/high pattern starting at all, or even a fixed positive fraction, of its initial horizons. This is an initial-horizon obstruction, not a bound on source-weighted mass later in the trajectory: many sources may share a rare physical horizon.

## 3. Exact fixed-horizon transcript cylinder, with time as the free variable

Given a candidate finite word (H_i,p_i,s_i,w_i), require H_(i+1)=H_i+p_i-1, eligible p_i in the corresponding factor set, and w_i>=1. Let A_i=sum_{j<=i} w_j, initial time t0, arrival n_i=t0+A_i. Then each side requires t0 parity s_i-A_i mod2. If these parities conflict there is no time realization.

Fix the common parity. For each odd prime q in the finite union of factor sets, store the allowed residues of t0 mod q. At each step i with q on side a:
* if q=p_i, impose n_i=a_a(q) mod 2q;
* for q<p_i, exclude a tie at n_i;
* for every eligible q require w_i<=positive representative of n_i-a_a(q) mod 2q.
For the chosen p_i the last condition simply says w_i<=2p_i. Since the parity of n_i is fixed, these tests depend only on t0 mod q; intersect the allowed sets at all steps. This gives an EXACT cylinder for the entire finite word: the necessary conditions are also sufficient by induction using the previous-clock characterization from section 1. CRT on distinct q shows unconstrained time feasibility iff every residue set is nonempty. For a bounded time interval, intersect the resulting residue classes modulo 2 prod q with that interval. This is exact, not merely a positive-event congruence screen. The number of allowed classes can be large; the finite audit below uses a simpler exhaustive arrival enumeration rather than expanding the entire product.

Note the distinction from checkpoint I's common-root lift: here the H_i are fixed standard integers, and only the initial clock phase varies. In particular there is no way to enlarge the horizons via CRT to evade absolute scale. A canonical root fixes t0=(H0+6)/2, so that special case is one point of the cylinder. An arbitrary intermediate state need not have canonical ancestry.

## 4. Bounded-scale DAG and exact phase search

In a fixed window [X,16X) use the checkpoint-II label band T=ceil(sqrt X/2)<=p<=B=floor sqrt X. Define four nested horizon-only DAGs on even H in the window, with H'=H+p-1; a jump crossing the upper endpoint contributes its full gain and is a terminal edge.
1. factor: actual adaptive eligible p from H+-1 in the band.
2. nondecrease: factor plus W(H,p)>=ceil((p-1)/2).
3. long: factor plus W(H,p)>=p-2.
4. longSafe: long plus both endpoints at distance >V from K Z, for the pinned lattice of II.
All are overapproximations: different edges in one path may require incompatible phases. The nondecrease/long inclusion holds for p>=3. All horizons strictly increase. The maximum remaining gain L(H) is exactly the backward recurrence
    L(H)=max(0,max_edges [(p-1)+L(H')])
with L outside the upper window equal to 0. Maximum event count has a separate analogous recurrence, and need not be attained by a gain maximizer. A block entering at X<=H<=X+B-1 cannot be covered entirely by these edges if max L on that entry strip is less than 15X-B+1. The entry-strip condition is for a previous overshoot bounded by B, as in II; the global maximum run gain also bounds runs beginning anywhere inside the window.

For exact phases, any actual canonical adaptive MIN state satisfies
    H/2 <= t <= 3H+3.
The lower bound is the ordinary nonnegative deficit envelope; the upper follows from initial t0=(H0+6)/2 and w<=2p<=3(p-1) for each event, hence t<=3H+3. This is a necessary envelope, not a sufficient ancestry condition.

For each eligible first edge (H,p,s), enumerate possible arrival n=a_s(p) mod2p with H/2+p-2<=n<=3H+3+2p. Compute all previous-clock gaps d_q and reject smaller ties. There is a starting time in the envelope with w>=p-2 iff
    max(p-2,n-(3H+3)) <= min(min_q d_q,n-H/2).
This follows exactly by writing t=n-w. Choose any such t (all choices share the same post-state). The actual deterministic future after (H+p-1,n) is then checked by earliest eligible clocks and the longSafe rule. Thus every possible run of length >=2 is covered by enumerating only the first edges whose projected successor has a possible outgoing edge. For length 1, separately search possible starts for the maximum label and validate a feasible arrival. This computes the exact max gain and event count of longSafe runs beginning at ANY standard state inside the canonical envelope; no claim that maximizers descend from a canonical root. Stopped states and first bad event terminate a run. No independent choices of phases between events.

## 5. Consequence for hypothetical global survival: necessary interruption supply

Let G be total gain of an actual complete block, L the max gain of a good run (all labels in band, long, safe), U the gain of all bad events, b their count. The good events break into at most b+1 consecutive runs, so
    G-U <= L(b+1),   b<=U/2,
    U >= max(0,2(G-L)/(L+2)).                        (2)
If all bad events also have label >=T, then b<=U/(T-1), giving the stronger
    U >= max(0,(T-1)(G-L)/(L+T-1)).                  (3)
More generally split bad events into small labels p<T (count b_lo) and other bad events (gain U_hi), so
    G_good <= L(1+b_lo+U_hi/(T-1)).                  (4)
No independence or recurrence-state distribution assumption enters this bound.

In particular an actual infinite trajectory cannot be the pure model II if a sequence of arbitrarily large windows has projected L=o(X) and the entry condition holds. If one could prove L=O(sqrt X) uniformly and G_good=Omega(X), (4) would require either Omega(sqrt X) small-label interruptions or Omega(X) bad high-label gain. These implications are conditional on the still-unproved uniform run bound. Finite computations are not an asymptotic proof. This supplies a concrete target relating deep bypass/large variation to the original small-label and high-event supply alternatives. It allows both resources, rather than assuming a single band dominates.

## 6. A narrower analytic test: affine clock tubes

As an independent restriction, suppose post-event states stay in a fixed bounded tube t=mH+c, |c|<=D, for an integer m>=1, along consecutive sufficiently large labels p>D+2m+2. On an even-side arrival H'=0 mod p and n=0 mod p, hence c'=0 mod p and c'=0. On an odd-side arrival H'=-2 mod p, n=2 mod p, hence c'=2m+2 mod p and c'=2m+2; but then n=mH'+c' is even, contradiction. Thus every such post-event in the tube lies exactly on t=mH, with even-side event. Consecutive events in the tube have w=m(p-1), so for large p the bound w<=2p implies m=1 or 2.

At t=mH with m=1,2, let p be the least eligible factor of H-1 and q the least eligible factor of H+1, allowing either to be absent. The earliest even clock has wait m(p-1), or infinity if absent. For m=1 every odd-side clock arrives at wait 3; for m=2 the earliest odd clock is at 1 if q=3, else q+4 (infinity if absent). These follow from H=1 mod p and H=-1 mod q, with required arrival parity. The line continues exactly iff the even wait is smaller than the odd wait. An odd arrival cannot lie on the integer line. For m=1 and p>=5 this requires H+1 prime, i.e. no eligible opposite factor. For m=2 with p>(sqrt(H+1)+6)/2, an eligible opposite factor would arrive earlier, so again H+1 prime. In either case the finite-twins hypothesis beyond its threshold makes H-1 composite. Such a run is therefore constrained to the one-sided chain
    H+1 prime, H-1 composite,
    H' = H+least eligible prime factor(H-1)-1.
For m=1 high-only p>=5, H≡0 mod6 (since H±1 cannot be divisible by 3), and consecutive such steps require p≡1 mod6. This exact affine-line analysis does not cover the entire variable-slope scalar model II, nor prove that the one-sided chain terminates. It gives another precise residual path class.

## 7. Finite audit and results

Final standalone source [a4b6b93](https://github.com/tara-sooo/A166944-Lean/blob/a4b6b9368cd1c14479bb65115c6ec11653d0e401/research/infinite-orbit/phase_graph_audit.mjs), run:
    node research/infinite-orbit/phase_graph_audit.mjs
The exact ECMAScript function executed in the available runtime, not a separate Node process. Sieve to 4,196,362. All assertions pass.

Local checks even H=4..10000: 6,943,556 observed first-event upper bounds; 8,893 label-maxima checked by exhaustive full phase periods when period <=20000; 11,991 exact CRT constructions attaining W (one per eligible label); 7,197 strict upper bounds W<2p, 3,559 smaller-same-side cap and 3,638 opposite-side cap incidences. 9,588 affine first-step equivalence tests, 4,442 line-preserving cases; independent literal integer gcd controls at all these affine states plus 9 representative run events, total 9,597.

DAG windows X=4096,16384,65536,262144, fixed finite diagnostic K=210,V=12 (not asymptotic growing lattice), band [ceil(sqrt X/2),floor sqrt X]. Each cell below is maximum gain / separately optimized maximum event count:

| X | factor | nondecrease | long | longSafe | exact longSafe phases |
|---:|---:|---:|---:|---:|---:|
|4096|310 / 7|142 / 3|118 / 2|102 / 2|102 / 2|
|16384|754 / 8|276 / 3|238 / 2|208 / 2|208 / 2|
|65536|1736 / 9|552 / 3|490 / 2|472 / 2|472 / 2|
|262144|3446 / 10|1276 / 3|1258 / 3|1258 / 3|1258 / 3|

Exact projected longSafe entry-strip max gain 40,0,210,276. None reaches 15X-B+1; even the factor-only global maximum is much smaller than the whole window. These are finite window exclusions only. The largest X graph has 1,966,080 even vertices, 460,152 factor edges, 17,899 nondecrease edges, 15,234 long edges, 10,617 longSafe edges. Count of all four windows' candidate arrival scans for potential multi-event paths is 937,832, including 813,966 feasible first arrivals; 351,905 continue for >=2 events. The counts are arrival incidences, not distinct canonical sources. Singleton maximum scan additional 26 arrivals. Projected and exact maximum gain/count coincide in these four cases; this does not imply all projected paths phase-realizable.

Largest exact run (pre-H, start t, p, w):
    (3970452,2074269,421,419)
    (3970872,2074688,457,551)
    (3971328,2075239,383,621)
Post H=3971710, total gain1258. Each step checked with independent literal gcd and eligibility cutoff. This is a real adaptive MIN segment from a specified intermediate state with the envelope; canonical ancestry not checked. It is a positive control against a blanket assertion that two or three high, long, safe events are impossible.

Finite graph computations do not establish a uniform bound as X grows, a full scale-specific theorem registry, or the dense-source transport conditions. No Lean executable or kernel check. Next: analytic upper bound on maximum gain of a long high projected run, or construct arbitrarily long feasible standard segments. In parallel, optimize mixed runs with low/short interruptions using (4), including actual source multiplicity before invoking unified constraints. Keep finite-twin conditional arguments separate from actual finite data containing twin centers.
