# Hypothetical infinite MIN worlds XXII: horizon-exact bridges, inverse clock reachability and terminal obstructions

2026-11-26 JST. Continuation of [XXI stitched survivor](https://github.com/tara-sooo/A166944-Lean/blob/a7293193b5dacf27bff7ded2d525ed6b4e86e76a/research/infinite-orbit/stitched_survivor.md). Sibling preflight direct [14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae), unified [9280871](https://github.com/tara-sooo/A166944-Lean/commit/928087104ac710306919017f46a92cdd874e03a5) XLIII adjacent endpoint odd-rational obstruction. New: exact horizon-factor paths with parity-respecting scalar clocks; exact finite reachability for the stronger relaxation that retains BOTH divisibility laws and the per-label next clock but drops earliest/minimum competition; a positive-density terminal obstruction for the prescribed short-wait irrational anchors; adaptive finite chain. No full infinite model with macroscopic exact anchors yet, no Lean or external novelty claim.

## 1. Three nested connector problems

Let source poststate (H0,t0), target prestate (J,t1), H0,J even, E=J-H0>0, low cap R. A horizon edge H->H+p-1 is allowed for an odd prime p<=R, p²<=H+1, with side s in {0,1} such that p divides H-1+2s. The side is unique for p>=3. Retain all edges with end <=J. This is an acyclic graph on the E/2+1 even horizons. No fake prime-gain edges remain. Three levels:
* Horizon and arrival parity: choose a wait 1<=w<=2p with t+w parity s, without clock divisibility.
* Horizon and exact label clock: for each allowed edge choose its unique next arrival f_(p,s)(t)=t+1+((A_s(p)-t-1) mod 2p), with A_0=0,A_1=p+2. This is exactly the least tick strictly after t having parity s and p dividing n-2s. We allow any eligible label rather than the earliest clock across all labels; hence competition is still relaxed.
* Actual MIN: minimize the next arrival, then the prime label on ties, over ALL eligible labels, including those above R. If that selected label exceeds R, a prescribed low-only connector fails.

These relaxations are nested; failure at a weaker one rules out all stronger ones for the fixed source, target and cap. No claim that a fixed target is forced on an actual infinite ray.

## 2. Exact horizon paths with balanced parity clocks

Assume t1-t0=W in [E,2E] as in XXI. Let H0=H_(0)<...<H_(m)=J be any exact horizon path with edges labelled p_j, sides s_j and gains g_j=p_j-1. Require the last side s_m=t1 mod2. Write T(H)=t0+(W/E)(H-H0). At each internal vertex H_j set t_j to the nearest integer of parity s_j to T(H_j), resolving ties consistently upward. At the endpoints use t0,t1. Rounding errors lie in (-1,1] (endpoints zero). Thus
    (W/E)g_j-2 < t_j-t_(j-1) < (W/E)g_j+2.
Since g_j>=2 and 1<=W/E<=2, the difference is a positive integer <=2g_j+1<=2p_j. Arrival parity and all horizon factors are exact. If the endpoint margins to both scalar envelope boundaries H/2 and 3H+3 are >=1, linear interpolation and the rounding error preserve the entire envelope. This holds for the deep irrational anchors of XXI. If W/E is exactly an endpoint, the same strict error difference bound holds. Therefore, for these endpoint geometries, existence of a horizon path whose final side agrees with t1 is sufficient and necessary for a connector retaining horizon divisibility, parity, gain and scalar waits/envelope. Clock divisibility may fail. This provides an explicit way to repair XXI's scalar connectors wherever the parity-sensitive DAG is reachable.

A separate conditional infinite relaxation: assume finitely many twins, choose even H0 divisible by 4 above the last twin center, t0=H0/2+3. At every H there is an eligible factor of at least one composite neighbor, so choose any such prime and its side. Horizons increase unboundedly. For theta=sqrt2, let desired posttime be the nearest integer of the required side parity to theta(H+p-1). Select the closest allowed time of that parity in [t+1,t+2p]. Starting below the target (H0 sufficiently large), if the desired time cannot yet be reached, choose the largest permitted time, increasing t by >=2p-1 and hence decreasing the tracking shortfall by >=(2-theta)(p-1)+1. Since gains diverge, eventually the desired time is attained. More explicitly when a step first permits the desired time from below, it cannot be earlier than the first allowable parity time: from t<=theta H+1, the rounded desired time differs from t by >theta g-2>0. After tracking is attained, the same estimate and theta<2 ensure the rounded next target is within 1..2p. Throughout the catch-up stage waits are >=g and t<=theta H+1; during tracking t=theta H+O(1). The envelope holds, and eventually t/H->theta. Labels unbounded by the fixed-cap cut barrier. This model restores every horizon factor and arrival parity and starts canonically under the finite-twin hypothesis, but does NOT assert clock congruences, macro square-root anchor gain, exact MIN selection, or satisfaction of all previous constraints. Its existence alone is far weaker than the original research goal; the finite bridge construction below probes the additional conditions.

## 3. A terminal obstruction before any forward search

At a target state (J,t1), let s=t1 mod2. If a nonempty exact-clock connector reaches it, its last label ell must satisfy
    ell | gcd(J+2s,t1-2s),                           (1)
    ell<=R, Hprev=J-ell+1>=H0, ell²<=Hprev+1.
This follows from Hprev-1+2s=J-ell+2s and the arrival clock law. Conversely the divisibility and eligibility describe the possible final edges at the level of coordinates; the pretime must belong to the length-2ell interval immediately before t1, and must be reachable. Thus (1) is an exact filter for possible last labels, not sufficient for a whole path.

At an XXI anchor with p in [T/2,T], q odd, k=floor(q/sqrt2), gcd(q,k)=1, H=pq+1, n=2pk even, target pretime t1=n-u, the filter becomes
    ell | gcd(pq+1+2s, 2pk-u-2s), s=u mod2.         (2)
For u=1, the prime 3 cannot be a last connector label (p>3): both residues would require 3|q and 3|k, contradicting the anchor gcd. This is a new obstruction arising precisely when the clock condition is restored, even if horizon-only paths abound. If the gcd is 1, no exact clock predecessor of any odd prime label exists, independent of cap or earlier path. More generally filter all ell with cap and size.

## 4. Positive-density two-tick terminal obstruction at growing cap

This strengthens the finite negative evidence. Put alpha=1/sqrt2, fix a proportional cap R<=T/8. Let p in [T/2,T] be prime and q range over any interval within [c0 T,C0 T] of length Q with Q>>T/sqrt(log T) (it is enough that Q>=c T/sqrt(log T) for fixed c>0). Only odd q are counted. For fixed u=1 or 2, each odd prime ell<=R is distinct from p, and (2) forces one residue q mod ell and one residue k mod ell. Similarly a common factor of q,k forces both residues zero.

For fixed ell, the count for any such residue pair is Q/(2ell²)+o_ell(Q) uniformly in the translated interval and residue choices. Indeed write q=q0+ell m with the required odd parity, and k mod ell is fixed exactly when fractional(alpha m+alpha q0/ell) lies in a corresponding interval of length 1/ell. Irrational rotation on the odd/even subsequence gives uniform equidistribution by the finite geometric sum argument in XXI. For varying ell, bad approximation ||alpha d||>=c/d shows that fractional parts of alpha m on this interval are spaced by >=c'/(Q/ell+1), so the count is O(Q/ell²+1) uniformly, including the residue shift. For ell>D up to R, sum over primes to get
    O(Q/D+pi(R))=O(Q/D)+o(Q).
The ordinary prime number theorem (or Chebyshev upper bound) gives pi(R)=O(T/log T)=o(Q). For gcd(q,k) common factors beyond R (or D), use XXI's large-divisor bound O(Q/D+sqrt T), which is also o(Q) after taking D large. No random-independence assumption.

Let sigma=sum over odd primes ell of 1/ell²<.22. By union bound, among odd q, the excluded fraction from gcd(q,k)>1 or a possible low last label at either u=1 or u=2 is at most
    3 sigma -1/9 + o(1).
The subtraction is valid because the ell=3 condition at u=1 is EXACTLY the same residue pair as 3|q,k, so count that event only once; no other overlap is required. Consequently at least
    1-3 sigma+1/9-o(1) > .45-o(1)                 (3)
of odd q are admissible anchors with NO low predecessor at either of the two specified pretimes. The limiting lower bound follows by first fixing D, then letting D grow; uniformity in p follows from the finite residue possibilities at fixed ell and the uniform tail. It is an asymptotic lower bound, not a distribution law for selected greedy anchors.

In particular modify XXI's track construction to S=floor(sqrt(log T)) growing tracks instead of T^(1/4). The q intervals then have length Theta(T/sqrt(log T)); each contains Omega(T/S) good anchors satisfying this obstruction. Retaining anchors with >=16T spacing still gives Theta(T) exact local anchors and Theta(X) anchor gain, now with S growing distinct labels. These endpoints cannot be connected by exact-clock low paths if the next anchor wait is restricted to 1 or 2, even with arbitrary horizon choices and competition removed. This is a counterexample to an unrestricted stitching lemma with small target-wait flexibility, not a contradiction to finite twins or a proof that all anchor families fail. The long interval condition is material: the elementary sum of +1 errors does not yield this uniform bound on the original T^(3/4)-length tracks at cap T/8.

## 5. Exact backward interval algorithm and flexible anchor waits

For a given exact horizon edge write f(t)=next label clock as above. It is nondecreasing. The preimage of an integer interval [a,b] is either empty if it contains no permitted clock, or
    f^(-1)([a,b])=[a_* - 2p,b_* - 1],              (4)
where a_* is the first clock >=a and b_* the last clock <=b. Proof: preimage of one clock n is [n-2p,n-1]; successive clocks are 2p apart, so these intervals exactly concatenate. For an arbitrary finite union, take the union of the preimages; merge overlapping or adjacent integer intervals. No approximation to reachable tick sets.

Fix target interval I of permitted pretimes at J. Define R(J)=I (intersect the scalar envelope). In decreasing horizon order, define
    R(H)= [H/2,3H+3] intersect union_(H->K) f_(p,s)^(-1)(R(K)).
By induction on the finite acyclic graph, R(H) is EXACTLY the set of scalar-envelope times at H from which a relaxed exact-clock path to J at a time in I exists. In the implementation additionally clip to t0<=t<=max I and t>=min I-3(J-H), necessary because each wait<=2p<=3g. Drop horizons not reachable from H0 by horizon-only paths. These restrictions preserve membership of the given source t0. Witness reconstruction chooses any edge whose next time lies in the successor set; the recurrence guarantees it exists until J. No assumption that R(H) is a single interval; union representation handles holes. Forward min/max possible clocks can also be computed by the same DAG with f monotone, ignoring intermediate envelope; these provide a necessary outer bracket, not a sufficient condition.

For an anchor with prescribed even arrival n and p, let wmax be its maximum feasible incoming wait at that arrival, computed against every eligible competitor by the earlier phase graph: for another label r with clock A_s(r), let z=(n-A_s(r)) mod 2r. If z=0 and r<p the anchor is impossible; otherwise bound wait by z if z>0, or 2r if z=0. Include bound 2p and incoming envelope n-w>=H/2, n-w<=3H+3. In XXI anchors the gcd guarantees no smaller tie; their deep slope makes the upper envelope automatic. The set of allowable pretime ticks is the whole interval [n-wmax,n-1] after envelope intersection. Thus the target can be widened from the singleton {n-1} to this interval without changing the poststate (J_anchor,n) of the exact anchor. This is the exact flexibility used by the finite adaptive graph. The actual anchor still satisfies earliest/minimum competition over all labels; the connecting path does not necessarily.

A directed graph of ordered anchors can use an edge precisely when the relaxed exact-clock bridge from the fixed source poststate to the target allowable interval exists. Because target poststate is independent of the particular feasible wait, edges concatenate without extra consistency of clocks. A longest path in a finite anchor DAG gives an actual finite trajectory for this relaxation with all selected anchors exact MIN. This is stronger than testing isolated pairs, but even arbitrarily long finite paths at changing roots would not establish one infinite path from a fixed root without an additional compactness/compatibility argument.

## 6. Finite diagnostics

[Audit 5e11ac1](https://github.com/tara-sooo/A166944-Lean/blob/5e11ac166e62e8fea5fe75f58b1c8b2549ca4eb4/research/infinite-orbit/horizon_clock_bridge_audit.mjs), blob c01f6b849e6618cd7edd3d5a4f85782298fe3b3d. Run node research/infinite-orbit/horizon_clock_bridge_audit.mjs. Actual ECMAScript execution in tool runtime, final assertions pass and remote readback exact. No independent Node invocation. Reuse XXI's original track and alternating anchors, not the new asymptotic two-tick obstruction family. The finite audit examines 1239 anchors: 1123 lack any eligible low last label at u=1, 852 at BOTH u=1,2, and 675 throughout the entire feasible wait interval. This latter test is only a necessary last-edge filter; it is not a reachability test. Counts use cap floor(T/8) in each respective physical block. Example H=6180,n=8732 has target pretime8731, gcd(6182,8729)=1, so no exact-clock predecessor at that pretime of any label.

Prescribed pair tests are within each block, first 24 consecutive track pairs at each of X4096,65536,1048576, and first four alternating pairs at X65536,1048576; 80 in total. They differ slightly from XXI's cross-scale sample. The following are exact finite graph counts.
| X | model | tested | horizon | correct final parity | fixed pretime exact clock | flexible pretime exact clock |
|---:|---|---:|---:|---:|---:|---:|
|4096|track|24|0|0|0|0|
|65536|track|24|3|2|1|2|
|65536|alternating|4|0|0|0|0|
|1048576|track|24|23|16|0|8|
|1048576|alternating|4|4|4|0|1|
|total||80|30|22|1|11|

Every one of the 22 parity-reachable paths has its exact scalar-clock assignment constructed and checked, 34298 event incidences, 31570 clock-divisibility failures in those particular balanced assignments. For fixed target wait 1, 8 of 80 pass last-edge existence (not all horizon reachable); 37 pass flexible last-edge existence. All 30 horizon-reachable examples have both targets intersecting the forward min/max outer bracket, but many still fail exact clock. Backward DP yields the counts in table. Prescribed witness paths for one fixed and 11 flexible successful pairs: 538 and 29307 connector event incidences respectively (may overlap); 12145 events fail earliest/minimum competition. Every connector event in those witnesses satisfies BOTH divisibility laws, correct side and next clock for its own label, numerical eligibility and time envelope. Actual deterministic MIN with cap is checked separately on all 80, zero fixed or flexible successes.

Example fixed pretime exact-clock bridge H0=113446,t0=160082 to J=117508,t1=166107, cap32. 538 connector events all exact neighbor and clock congruences; 215 fail actual competition. Its first event p=3,w=4,s=0 at H0,t0; then p=7,w=13,s=1 at H=113448,t=160086. This is an explicit finite bridge between exact local anchors, not canonical ancestry. Example flexible bridge H0=109254,t0=154318 to J=113316, target arrival n=160082, chosen pretime160080 instead of160081; 531 events,234 competition failures. The final anchor is an actual MIN event with wait2.

Adaptive experiment at X=1048576: first16 track anchors, permit target up to three indices later, test all42 candidate pairs using flexible pretime. 13 feasible exact-clock bridges, none deterministic. Longest chain in this finite graph has 4 anchors (zero-based indices 2,5,8,10):
| anchor H | arrival n | p |
|---:|---:|---:|
|1099832|1554664|521|
|1150890|1626562|521|
|1201948|1699502|521|
|1235292|1746392|521|
All three bridges have exact-clock witness reconstructions; the shared exact anchor poststates ensure concatenation. This chain stays within one prime track (not the wide-gap alternating variant), and does not extend to infinity or canonical ancestry. The exact-clock connectors in the successful adaptive pair census have 30261 event incidences, 12415 competition failures (including overlapping edges). Source anchor itself can be started at n-1. To reproduce, run the audit and inspect adaptive.records and chainAnchors.

Independent controls: seven literal forward (H,t) reachable-state censuses versus backward intervals, including one nonempty case; 403998 time-state incidences; all equalities pass. 770 single-edge preimage interval tests across five primes, both sides, 123970 literal tick membership checks. Across prescribed+adaptive searches the backward union DP visits 360130 nonempty horizon-set incidences and the same number of intervals, maximum one per vertex in this sample, 939131 preimage applications. The algorithm allows multiple intervals; empirical single-interval behavior is not asserted as a theorem. No analytic density constant tested, no asymptotic conclusion from the finite success rates.

## 7. Remaining work

Restored horizon factors, side parity and exact per-label clocks on actual finite stitched bridges, with anchor competition exact. The last-edge obstruction shows why fixing short anchor waits is too restrictive, even at growing cap, and the flexible interval restores a number of finite bridges. The infinite construction of XXI remains only scalar with exact anchors; the conditional horizon-exact infinite relaxation of section 2 has no macro high-anchor guarantee. Next investigate an adaptive infinite horizon/clock-exact anchor family or a density bottleneck for the flexible target intervals; compare exact competition on the successful witness paths to identify unavoidable earlier clocks rather than artificial horizon jumps. Need a uniform extension result for a fixed initial path to justify an infinite stitched model. Full all-constraint model, general uncapped bound, Lean proof and finite-twin contradiction remain open. Main and siblings unchanged.
