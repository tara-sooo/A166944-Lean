# Recent-large clock coincidences and source-preserving merge charges

2026-11-25 JST. Continues 9450ea5e3ebd0909bffb775093330e2d37cd968e (source-preserving merge ledger) and the full-horizon pair budget at 73458de887def94d00eeaf2d2d3b9c59a44b8137. New paper bounds for two subclasses of representative demotion, and a finite independent clock audit. The full late weighted energy and twin-prime conjecture remain OPEN. No new Lean compilation.

## 1. Setup

Use original odd sources M in [X,2X), X dyadic divisible by four, t0=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). All states lie in an O(X)-sided rectangle with even 2X<=C<7X, 0<t<7X/2. Each MIN event with label p advances C by p-1 and its time by a positive wait at most 2r(C)<=2p<=3(p-1), where r is the least eligible odd prime. Thus between any two visited states of one source, elapsed time is at most three times horizon gain. A source's full R contribution, sum r(C) over actual pre-event horizons, is O(X), since r(C)<=p<=3(p-1)/2 and gain telescopes.

At a post-event state (u,H) created by prime q, the exact clocks give either u=0 mod 2q, H=0 mod q (even side), or u=q+2 mod 2q, H+2=0 mod q (odd side). For Q<=B and nonnegative integer A, call a state (t,D) recent-large if its actual source history has a post-event state (u,H) of label q>=Q with 0<=D-H<=A. Then 0<=t-u<=3A. This definition includes arbitrary intervening labels; no LOW cutoff is needed. If A<Q-1, at most one such large event can occur in that gain interval.

## 2. Near-time physical pairs

Let z>=1 be an integer and suppose Q>2z+3A+2. Count distinct ordered pairs of different physical states (t,D),(t',D) with |t-t'|<2z, both recent-large for some actual source history. Write their witnessing post-event states as (u,H),(u',H'), with labels q,q', offsets e=D-H and e'=D-H', each between 0 and A. Their time difference has absolute value <2z+3A.

Necessarily q!=q'. Indeed if q=q' and the sides differ, the circular clock-residue distance mod 2q is q-2, larger than 2z+3A, impossible. If their sides agree, u,u' are congruent mod 2q and hence equal; H,H' are congruent mod q and their difference has magnitude <=A<q, hence equal. From the same post-event physical state the MIN dynamics is deterministic until the earlier original cutoff. Both histories reach D, and strictly increasing horizon implies that they reach it at the same time, contradiction. This argument works for physical states with arbitrary source weights.

For distinct fixed q,q', e,e' and two sides, the congruences on H=D-e and H'=D-e' fix a single residue of D mod qq'. Hence O(1+X/(qq'))=O(X/(qq')) possible horizons (qq'<=B^2=O(X)). For each integer lag h=u'-u with |h|<2z+3A, the two clock congruences on u,u+h fix at most one residue of u mod qq' (we may drop parity), so O(X/(qq')) possible times. There are O(z+A+1) possible h. Each tuple determines both physical predecessors at horizon D uniquely, if they exist: replay from (u,D-e) and (u+h,D-e') until D; actual cutoffs can only remove candidates. Counting every tuple overcounts, which is valid. The number of distinct ordered physical pairs is at most

    O((A+1)^2 (z+A+1) X^2 (sum_{Q<=q<=B, prime} q^-2)^2)
    = O((A+1)^2 (z+A+1) X^2/(Q^2 log^2 Q)).                 (1)

The last estimate is Chebyshev prime counting and partial summation, uniform for growing Q. In particular choose Q=ceil(B/log^(1/3) B), A=floor(log^(1/3) B), z=max(1,floor(sqrt(log B))). The scale gate holds eventually, and (1) is O(X/log^(1/6) B)=o(X). Alternatively use a fixed A=210 (LOW7): for the same Q,z it is O(X/log^(5/6) B). A LOW-only block after a high event has gain <L (L=210 for LOW7); thus the fixed-radius variant applies whenever the latest high label was >=Q, even if the predecessor was created by a low label.

## 3. SAME demotion theorem

Use exactly the original-source representative ledger of 9450ea5: at each target vertex, among incoming predecessor classes with the same incoming selected label p, retain the maximal-cutoff representative and demote each other representative, pairing it with the winner. These are distinct original tags; each tag demoted at most once. Their predecessor horizons D are equal, and predecessor times are distinct. Call a SAME demotion marked if this pair has |t-t'|<2z and both representative histories are recent-large. In particular the lag hypothesis is automatic if r(D)<=z because both predecessor times lie in the last-clock interval of length <=2r(D).

Each marked demotion yields an ordered physical pair counted in (1), and no pair can be used at two target vertices because the next MIN clock and label are deterministic. At a target, each demoted predecessor class occurs only once. Therefore there are o(X) marked SAME demotions at the specified growing scale. Each tag has full source cost O(X), so the sum of their post-demotion costs is o(X^2). This bounds the actual original-source budget contribution, not just the number of physical vertices. It does NOT bound the cost of all previously demoted tags in an incoming class or the product of their source masses.

## 4. ROOT demotion theorem

At an injected root (t,C)=(M+2,2M-2), any incoming representative is an earlier source, since time strictly increases. Hence the root has larger cutoff and the old maximal representative is demoted as ROOT. Mark the ROOT demotion if the old representative history at this vertex is recent-large. Then for some q>=Q and 0<=e<=A, q divides C-e or C-e+2. For each fixed q,e,side this fixes one residue class of M mod q because q is odd. There is at most one ROOT demotion per injected root. Summing gives

    #marked ROOT <= O((A+1)(X sum_{Q<=q<=B}1/q + pi(B))).
    
For Q=B/log^(1/3) B up to rounding, Chebyshev prime counting in dyadic bands gives sum 1/q=O(loglog B/log B); pi(B)=O(B/log B). At A=floor(log^(1/3) B) the count is O(X loglog B/log^(2/3) B)=o(X). The same holds for any fixed A or A=O(log^(1-epsilon) B) for fixed epsilon>0. Thus marked ROOT post-demotion costs are o(X^2). In particular this covers a last large event followed by an arbitrary bounded-gain low-only suffix before the root, rather than only direct high entries.

The SAME and ROOT results are disjoint ledger subtypes. Combining with the parent BIG and representative-high estimates, one may remove their post-demotion costs from R at o(X^2) expense. Let W_rem count the remaining source-event incidences after these disjoint removals, and E_rem=sum_C r(C)W_rem(C)^2. By the full-horizon sieve bound S0=O(XB/log^2 B) and Cauchy, E_rem=O(X^2 B log B) on unbounded dyadic windows still suffices for twin infinitude. This does not establish the remaining energy bound. In particular small-label histories, long lag, and previously accumulated incoming tags remain uncontrolled. The new result cannot be multiplied by a presumed uniform ancestor mass.

## 5. Finite audit and limitations

Standalone ECMAScript research/min_recent_large_merge_audit.mjs, exact source readback at 8ea11ea3bf34e17040aa1f066e6448a631cfe879, blob c93d9b8865b246e23bf30069370cfa72a263a5ce. Run from repo root:

    node research/min_recent_large_merge_audit.mjs 256 1024 4096 16384 65536

Executed the actual audit function in the available JS runtime for X=256,1024,4096,16384 with y=7 (default Q,z,A) and for X=4096,16384,65536 with y=3,Q=29,z=3,A=6. This is not a separate local Node run. For X<=1024 it independently checks literal per-tick parity GCD and least eligible factor (6140 clock checks for y=7). Keeps original cutoff, all sources, physical predecessor classes and maximal-M representative. Verifies no tag demoted twice, same predecessor horizon, correct root ordering, gain/time radii, distinct large labels under the scale gate, and injection to candidate tuples. SAME and ROOT total counts match the parent audit. Reports full source costs of marked demoted tags, an upper bound on their suffix costs, not exact suffix costs.

| X | Q,z,A | SAME | ROOT | marked SAME | marked ROOT | marked SAME full cost | marked ROOT full cost |
|--:|:--|--:|--:|--:|--:|--:|--:|
|256|28,1,1|54|31|0|0|0|0|
|1024|52,2,1|233|129|0|6|0|552|
|4096|99,2,1|1052|532|0|4|0|720|
|16384|189,2,1|4392|2167|0|20|0|8495|
|4096|29,3,6|1052|532|1|50|868|9892|
|16384|29,3,6|4392|2167|0|236|0|74055|
|65536|29,3,6|18223|8726|1|980|138|535836|

The diagnostic fixed Q=29 is deliberately not the asymptotic choice; it exercises the distinct-label lemma nonvacuously. Both default and diagnostic cases satisfy the gain-radius gate. Counts in the tested windows are small, and the new classes do not explain the dominant SAME/ROOT mass. No statistical extrapolation or proof of E_rem is claimed.

## 6. Follow-on

The difficult part is the number of original tags per incoming state, not the number of rare large-large physical configurations. In the full ledger, ROOT and SAME suffix costs dominate the finite R. Target the residual SAME demotions with at least one predecessor whose recent history uses only smaller labels, and the residual ROOT demotions where the last large event lies outside the gain radius. One possible approach is to group the source-tagged histories by their last large post-event state and exact smaller-label intervening segment, keeping the cutoff-tagged suffix survival count; a bound on the weighted ancestor mass for long smaller-label segments is required. The finite pair estimate above does not imply that bound. Main untouched, no new Lean proof, twin-prime conjecture OPEN.
