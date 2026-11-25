# Long stable strands by linear entropy trimming; elimination of a separate asynchronous high-energy condition

2026-11-25 JST. Continuation of unified record-Hall-tail 9a60c91099af and below-exit db56fd72b184. Incorporates the latest independent [persistent-block theorem, 51740a88e00b](https://github.com/tara-sooo/A166944-Lean/blob/51740a88e00bf1cc236ed7d7ecc2ffc2ee72a0c7/research/2026-11-25-min-prime-root-persistent-blocks.md) and [record merge-tree entropy, 5fb058bf40f4](https://github.com/tara-sooo/A166944-Lean/blob/5fb058bf40f4648215a05cb6764497094b112d96/research/2026-11-25-min-clock-record-below-excursion-tree.md). Use entropy on the full true-tick forest, not the short-prefix level-specific pair ledger. The new use of entropy is a LINEAR actual-clock deletion, so the surviving physical cohorts are stable over much longer spans than the earlier absolute pair-energy deletion allows. A disjoint occupation packing bound treats all asynchronous interactions without any quadratic asynchronous condition. Paper theorem; the remaining thick slow strand estimate and medium/other clock are open. No twin-prime proof or Lean compilation.

## 1. Actual true-tick forest and total variation of mass

Keep the original long prime-root ensemble: dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Root (M+2,2M-2) for prime M in [X,2X), original cutoff floor((7M-1)/4), first completed gain crossing T or earlier original stop. The completed gain a=p-1<=B, actual wait 1<=w<=2r<=3a, total gain <H and total completed time <=3H. All state deficits d=2t-C satisfy 0<=d<=6+5H. No original dynamics are rerun.

Use the full original tick-state paths. If a recorded edge runs from (t,C) to (v,C+p-1), its tag occupies (j,C) for integer t<=j<v. The final original recorded state is a single terminal snapshot and the tag then expires. At every actual state V=(j,C) let G_V be its full original set of tags before expiry, n_V=|G_V|, and b_V the number that continue to the next tick. The continuing tags move intact to their unique deterministic next state U; at U they form one incoming branch of mass b_V. New root injections are singleton branches. At a node U with incoming branch masses a_i (including injections) summing to n_U, its merge entropy is
    D_U = sum_i a_i log(n_U/a_i).
It is nonnegative. Using f(n)=n log n, f(0)=0, and telescoping along the finite time-directed forest gives
    sum_U D_U = sum_V [f(n_V)-f(b_V)]
              <= N(1+log N).
This includes terminal expiry and root injection (f(1)=0). It is the usual entropy identity, not a claim that active mass never decreases.

NEW: For each continuing tag M in V define its one-tick variation token
    e_M(j)=log(n_V/b_V)+log(n_U/b_V),
located at its pre-transition horizon C. Both terms are nonnegative; b_V>=1. First term measures other tags expiring, second term measures other branches joining. Sum over tags:
    sum_(M,j) e_M(j) <= N(2+log N).                 (1)
Indeed b log(n/b)<=n-b, so the first term totals at most N; the second sums over actual continuing incoming branches and is at most the full merge entropy above. Injection tokens are not needed. Stationary ticks without changes contribute zero. This controls BOTH directions of change of full original visiting mass on each actual source path.

For any segment of one focal tag's true path with total variation <=epsilon, all its visiting group sizes on that segment differ multiplicatively by at most exp(epsilon), since |log(n_next/n)|<=e_M(j). More strongly, for a fixed group G of size n on that segment, at least
    (1-exp(epsilon) epsilon)n                       (2)
of its tags belong to EVERY group throughout the segment. To prove (2), at a transition V->U the shared continuing set has size b_V; all other losses and gains count n_V-b_V and n_U-b_V. Their sum is <=n_V log(n_V/b_V)+n_U log(n_U/b_V)<=exp(epsilon)n e_M(j). Every tag of G missing somewhere on the segment must occur in one of these symmetric differences. Sum over transitions in both directions from G. No assumption of nested tag sets, independent births, or absence of expiry.

## 2. NEW unconditional linear entropy-window deletion

Let D=floor(T/(u ell^2)), epsilon=1/ell. Eventually D>>B, epsilon<log 2, and exp(epsilon) epsilon=o(1). Other choices with D>>B, epsilon->0 and uD/(epsilon T)->0 work. For a completed event of original source M at prehorizon C, set
    V_M(C)=sum_(j: |C_j-C|<=D) e_M(j),
using ALL original actual transitions of M (including transitions in deleted events). Delete the event for linear actual-clock accounting if V_M(C)>epsilon. Also delete first and last D gain units, i.e. events with C-C_origin<D or C_end-C<D. These are accounting masks only.

For a fixed token at horizon J, the total actual wait of M's completed events with prehorizons in [J-D,J+D] is <=3(2D+B): their gain intervals are disjoint, contained in [J-D,J+D+B], and w<=3a. Consequently Markov's inequality followed by exchanging the finite sums gives
    W_entropy <= (3(2D+B)/epsilon) sum_(M,j) e_M(j)
              = O(NuD/epsilon)=O(NT/ell)=o(NT).     (3)
The two endpoint trims cost O(N(D+B))=o(NT). If previous linear masks exist, remove only the remaining actual waits. Unlike a pair-energy trim, this removes the corresponding source incidences themselves and requires NO upper bound on their squared partner counts. It applies to MED as well as HIGH.

A further exact geometric consequence: if two distinct retained focal tags have a true first meeting whose two incoming predecessor horizons lie within D of their respective retained event prehorizons, then one of those events would have been deleted. The two tags belong to different incoming branches at their first meeting, at least one of which has size <=n/2. Its token has log(n/b)>=log2>epsilon. If one endpoint is an injected root at the meeting, the first-gain trim handles that endpoint whenever the meeting is within its event's D-neighborhood. The conclusion is about actual retained tag incidences, not pair masks or merely projected contacts.

## 3. Superblocks and almost unchanged long actual cohorts

Take P the largest even primorial <=B u^1.5, as in 51740a88. Its largest prime factor z=Theta(u), and P>B eventually (indeed P>>B sqrt(u) up to a fixed constant), by Chebyshev theta bounds and Bertrand. Let S=P floor(D/(4P)); S~D/4 and S/P grows at least on the order of B/(u^(11/4) ell^2), much faster than u. For each high or other retained completed event at C, its unique central superblock is (K,K+S], K=S floor((C-1)/S).

On each focal retained path take the ACTUAL strict crossing of K-S and of K+2S, where crossing means prehorizon A<=boundary<posthorizon A+p-1. The endpoint gain trims guarantee both exist: C_origin<=C-D, C_end>=C+D, and 2S+B<D eventually. Index the earlier crossing by its TRUE TICK JUMP e=(v,A,p) (exit tick v, prehorizon A, selected label p), NOT its recorded input time. Tags can enter the waiting interval at A at different times and still execute the same jump. The entire focal tick segment from (v-1,A) to the later crossing's poststate has prehorizons within [C-D,C+D], so its variation <=epsilon. For each (K,e) let A_(K,e) be the original set of tags executing that earlier jump and also actually completing a strict crossing of K+2S. Call a group active only if it contains at least one retained focal event in the central block. Write n_(K,e)=|A_(K,e)|.

By deterministic tick evolution every member shares the entire tick segment between the two jumps, and after the earlier jump all central recorded event times, labels and waits agree exactly. For ANY retained focal event in the group, with full original true-tick group mass n at its prestate,
    (1-exp(epsilon) epsilon)n <= n_(K,e) <= n.       (4)
The upper bound follows from the common path. The lower follows from (2): tags present at all states between the two actual jumps execute both jumps. Since the first jump's posthorizon is below K, no member's recorded entry at a central event can differ. The statement is valid for arbitrary prior linear masks; the cohort uses FULL original tags while the focal event must survive those masks.

Every actual cohort shares strict crossings of all multiples of P from K-S through K+2S, at least 3S/P+1 DISTINCT completed jumps because p-1<P. At each crossing the selected prime p>z by the primorial barrier (if p|P and p divides A±1, the positive even distance to the multiple of P is at least p-1; landing exactly is not a strict crossing). The resulting inherited span has length Theta(T/(u ell²)), rather than the earlier Theta(B u^2.5) pair-age span. Crucially (4) controls the FULL active mass, not only the number of retained partner tags.

NEW noncollision: any two DISTINCT active groups at the SAME central K have disjoint true-tick states throughout their extended spans from the earlier pre-jump state to the later post-jump state. Otherwise choose one retained focal tag from each group. The two share a state in those spans. Their first true meeting cannot precede their distinct earlier strict jumps of K-S: if it did, both would have the same next strict crossing there. Thus the first meeting lies within the extended horizon interval [K-S-B,K+2S+B], with incoming predecessor horizons in [K-S-2B,K+2S+B]. All these horizons are within D of BOTH focal central events for large X (2S+2B<D). Both tags already started before K-S, so neither is an injected root at that meeting. They enter from different branches, and the smaller branch token exceeds epsilon, contradiction to (3). The claim includes two different active groups whose focal events are at different horizons or different times. Equality of projected horizon alone is allowed. For every central horizon C, distinct active groups' actual completed waiting intervals at C are therefore disjoint. No assumption of synchronous arrival for all projected pairs.

Adjacent active blocks admit a partial one-to-one link by equality of the actual strict jump crossing their common boundary: in each block two different active groups cannot have that jump by noncollision. On linked groups, the full visiting group at the shared post-jump state is the same; applying (2) to each focal segment gives both memberships within a factor 1-O(epsilon) of this common mass, and their intersection contains at least (1-2 exp(epsilon)epsilon) times that mass. This is a stable chain relation, not a bound on chain lengths or on the number of beginnings.

## 4. NEW absolute thin-strand clock bound, including asynchronous high

Define natural HIGH exactly as in the prime-root parent: p>=ceil(B/u), r>p/sqrt(log p), completed actual events only. Thus every such horizon has r>=c B/u^1.5. The least-factor quotient sieve of [feed8962 continuation](https://github.com/tara-sooo/A166944-Lean/blob/1ccfb6af1957dcada4ee3286d01206288664e135/research/2026-11-25-min-prime-root-minfactor-support.md), section 1, gives # {C:r(C)=p} << X/(p log² p) uniformly. Summing p between c B/u^1.5 and B using the elementary reciprocal-prime upper bound gives
    # possible natural HIGH horizons << X ell/u³. (5)
This counts only positive finite r, no twin terminals.

For an active group g=(K,e) let V_g be its common natural HIGH actual wait sum in (K,K+S] (before any source-specific masks). It is exactly identical on every member and <=3(S+B). At any fixed C, the distinct active groups visiting C have disjoint actual wait intervals by section 3. All those intervals lie in one interval of length O(H), because 0<=2t-C<=6+5H and w<=2B. Therefore
    sum_active g V_g << X H ell/u³.                 (6)
This is the unweighted sum of actual HIGH clocks of distinct long strands, including groups with enormous membership. It does not use the asynchronous projected quadratic energy at all.

Set m=floor(u^(7/4)/ell). The actual retained high clock in active groups with n_g<=m is at most
    sum_(n_g<=m) n_g V_g
      << m X H ell/u³ = O(NT/u^.25)=o(NT).          (7)
This is a LINEAR bound even if many thin groups visit the same horizon at different times and their projected total tag count is large. It does not assert that their projected pair energy is small. One can use any m=o(u²/ell).

Generalization, useful for MED: for ANY family of completed events whose least factor is >=R growing with X, the same quotient buckets imply # supported horizons << X/log² R (sum 1/(p log²p) over primes p>=R, by partial summation of the elementary prime-count bound). Applying the same stable groups and packing proves
    W_(r>=R, n_g<=m) << m X H/log² R.
In particular for R=exp(u^.75), m=floor(u^.25), this is O(NT/u^.25). These parameters are independent alternatives to (7); apply both by priority if desired. For any fixed delta>0, R=B^delta allows m=floor(u^.75), likewise o(NT). This pays actual medium events in those least-factor ranges even if their prior repeat quota history is complicated. No assertion for r below R. To apply to a family not restricted to HIGH, form active groups using that family and run the identical noncollision proof (the entropy mask is independent of label).

## 5. Actual occupation instead of pair excess

For all active groups g, each original tag occurs in at most one group per central superblock, and its gain range is <H. Thus
    sum_g n_g S <= N(H+S).
For rho=u^(-1/4), the total actual retained high clock in groups with V_g<=rho S is <=rho N(H+S)=o(NT), regardless of group size. Use priority thin first, then low occupation. These are not Hall payments and cannot be used as claims of small quadratic energy.

Define the remaining EXACT linear clock L_strand as the sum of actual waits of retained focal high incidences in active groups satisfying BOTH
    n_g>m,   V_g>rho S.                              (8)
The common natural V_g is used only as a filter; L_strand counts actual focal incidences after masks, not all original members artificially charged to the full natural block. All such groups have the stable membership property (4), and share Theta(S/P) true strict primorial crossings, each label >z. Distinct active groups never share true tick states within the extended span. By (6), the number of slow active groups is at most O(XH ell/(rho S u³)), though this alone does not bound their weighted sum.

Let A_other be the exact remaining actual clock not in the natural HIGH family, after disjoint earlier linear deletions (and optionally the new MED thin-strand generalization). Account earlier LOW attachments at their actual waits; do not count them twice. Combining (3), endpoint trim, (7), low-occupation bound, and any previous proved o(NT) linear masks gives
    W_all <= A_other + L_strand + o(NT).             (9)
No high quadratic estimate, separate async Hall target, or cumulative pair masks are needed in this route. It suffices along unbounded dyadic windows that
    liminf (A_other + L_strand)/(NT) < 1/2.         (10)
Alternatively prove both little-o on the same unbounded sequence. On windows without twins every original root crosses T eventually and the telescoping deficit identity gives W_all>=N(T-6)/2, contradiction to (9)-(10). The old energy bound on the same retained event family implies its actual high clock is o(NT) by Cauchy, so it implies the new high tail bound; the new route need not bound the projected quadratic moment at all. MED can use its old actual focal-clock estimates or a direct actual bound. Prior Hall/first-record/below-exit pair conditions are optional for further investigation, not additional assumptions here. The earlier joint Hall linear-tail condition also implies small actual high time (when its absolute budgets hold), hence this exact tail condition. No strictness claim between the two linear criteria on canonical MIN.

The remaining research target is the linear occupation of thick slow stable strands (8), or enough of their occupation to reach the constant threshold (10). The entropy trimming and thin-strand estimates are unconditional; a large group could in principle carry nearly all its members through many slow blocks. The stable chain relation and the long sequence of forced primes >Theta(log B) supply actual structural constraints for that next step. None of (1)-(8) establishes that thick slow occupation is negligible. No asymptotic proof of (10), no Lean kernel verification, no external novelty claim. Independent input branches and main unchanged.


## 6. Finite actual-path audit and further local label restriction

Standalone [min_unified_stable_strand_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/3e15466dbc538bc86041cfcde4402124ffdc3e6d/research/min_unified_stable_strand_audit.mjs), commit 3e15466dbc538bc86041cfcde4402124ffdc3e6d, exact source remote readback verified. Executed the audit function in the available ECMAScript tool runtime (not an independent Node invocation). Reproduce:
    node research/min_unified_stable_strand_audit.mjs diagnostic .5 256 1024 4096 16384
    node research/min_unified_stable_strand_audit.mjs wide .5 16384

Original prime tags, factorized exact parity-clock MIN, cutoff and first gain crossing, terminal snapshot, all original integer tick states. Independent literal per-tick gcd oracle at X256/1024 (431 and 1239 clock comparisons). Checks include deterministic successor, intact continuing branch, total expiry N, exact entropy telescope including root singleton injection, both merge/expiry token bounds (1), linear entropy deletion (3), endpoint cost, actual cohort membership and (4), full shared tick span of every member, pairwise noncollision of distinct active spans, disjoint actual waiting intervals and global slab sum, actual strict primorial crossing q>3, complete retained-clock partition and adjacent link intersection.

Finite parameters deliberately differ from analytic scaling: T=min(8B,floor(X/2)), P=6, S=max(6,6 floor(B/24)), epsilon=.5, diagnostic D=4S+1 or wide D=2S+2B+1. Natural diagnostic high p>=max(5,ceil(B/10)), r>p/2. Thin cap 8, low occupation V<=S/4. The diagnostic allows P<B and multiple grid boundaries on one jump: checks the strict label barrier but NOT the analytic distinct-crossing count. It explicitly skips any event lacking the actual geometric span condition; 33 clock units skipped at X256, none at the other runs. The wider finite mode checks that no geometric skip occurs. Thus no claim that the diagnostic geometry-skip cost is analytically negligible, or that its raw high support or trim fractions are asymptotic estimates. The wider mode has nonzero but small retained high occupation.

| X / mode | original clock | entropy paid | endpoint paid (disjoint) | retained HIGH after geometric checks | active groups | max group mass | thick slow HIGH clock |
|---:|---:|---:|---:|---:|---:|---:|---:|
|256 diagnostic|2426|1569|506|261|13|7|0|
|1024 diagnostic|7377|5391|1986|0|0|0|0|
|4096 diagnostic|67027|46142|12681|5900|26|8|0|
|16384 diagnostic|385422|294190|64733|17362|35|15|7137|
|16384 wide|385422|346327|38545|160|1|5|0|

At X16384 diagnostic: B339,T2712,S84,D337, 1612 prime roots, 32866 completed events, 114139 true-tick vertices, max gain1996, total entropy tokens2407.872 (within (1)). Original natural high clock195474, all retained clock26499. Actual cohort checks178, 7903 active span state checks, 36 common high events and 10 adjacent links. Minimum observed membership ratio n_g/n=.888889. Unweighted active-group high clock2971, natural weighted18164, exact retained17362 = thin10060 + low occupation165 + thick slow7137. Wider D847: one active group with five tags, common natural high clock32, all retained high160, 263 span states, no geometry skips. All five runs passed. No inference that the observed reduction fraction persists asymptotically, no independent Lean verification.

Further paper restriction using the earlier relative-expensive [quotient capacity](https://github.com/tara-sooo/A166944-Lean/blob/1ccfb6af1957dcada4ee3286d01206288664e135/research/2026-11-25-min-prime-root-gain-prefix.md), section 4: in an analytic superblock of length S, for any fixed selected p>=B/u, the number of completed natural high hits of that label on a single original trajectory is O(S/(p log²p)). The p-quotient interval has length O(S/p+1), and the sieve error O(p^.75) is uniformly absorbed because S=Theta(X/(u^(5/4) ell²)) and p<=B. Since each such wait <=2p, its entire block clock is O(S/u²), with an absolute uniform constant. Therefore a slow strand with V_g>rho S must use Omega(rho u²) distinct actual high selected primes in its central block; for rho=u^(-1/4), Omega(u^(7/4)) distinct labels. This is on the common natural block, not a source-specific rank-deleted list. It applies even to a very thick stable group and needs no random distribution of labels. It is an additional necessary condition on (8), not a bound on the number or mass of such strands. This last analytic restriction was not tested by the finite diagnostic.

Independent direct thin-group variant (does not require entropy): at any horizon C, group all original completed events by their scheduled exit tick v (the selected label is uniquely determined by that tick and horizon). Within one exit group the waiting intervals are nested; different exit groups have disjoint intervals, since an overlap is a common true tick state and forces the same next event. Hence the total actual clock of all events in exit groups of original mass <=m is <=m O(H) at C. Summing (5) proves the same O(m XH ell/u³) absolute high-clock bound even BEFORE the entropy trim, and the general R variant holds likewise. This does not bound a large exit group. The stable-strand version is more structured because it supplies a long common path and near-constant mass; both thin tests may be used by disjoint priority. No claim that these two masks coincide.
