# Persistent larger-source ancestry, long common physical histories, and adaptive two-sided shared-clock trimming

2026-11-25 JST. Continuation of 431f242362e394132a6eec9d5825c8ba86a695fb on the user-selected branch. The preceding compressed reverse frontiers bound the number of boundary classes, not their ancestor masses. Here a logarithmic growth budget gives a new negligible LINEAR deletion: for every surviving focal event, the actual persistent larger-source ancestor population is almost unchanged back through a long gain window, simultaneously in all relevant fixed source cells. A density gate then absorbs recent synchronous high-pair energy relative to the energy of the actual retained incidence set, even with arbitrary prior accounting holes. An independent source-distance-adaptive pair budget trims short shared natural high histories at BOTH ends, including asynchronous histories. No proof of the general residual or twin-prime conjecture; no Lean compilation.

## 1. Persistent companion counts on the original physical paths

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u), F=T²Bu. Original roots are primes M in [X,2X), with initial physical state (M+2,2M-2), original time cutoff floor((7M-1)/4), and original gain stop at the first postgain >=T. Include the actual final vertex; do not extend a stopped trajectory. All completed gains are p-1, with p<=B, total gain <H, and actual waits <=2r<=3(p-1).

We use the ordered persistence lemma of 0f74d826: once two roots M<M' meet at a physical vertex, every subsequent vertex of the smaller root, including its terminal vertex, also belongs to the larger root's original path. The actual successor is deterministic while both continue; the larger root has larger gain-stop horizon and no smaller time cutoff. A twin terminal is common when reached. Thus the larger root cannot expire first after a meeting. This applies to the FULL original trajectories, not to arbitrary subsets of retained incidences.

For a root M at its actual vertex v=(t,C), let
    n_M(v)=1+# {M'>M: M' visits the same physical vertex v}.
The 1 counts the focal root. For each fixed original aligned source cell c of width d comparable to H/u^.25, let
    n_(M,c)(v)=1+# {M'>M in c: M' visits v}.
Use the same fixed finest source cells as in the medium ledger; for high this is an additional accounting partition, not a change in the high natural list. The sentinel 1 is used in every cell, whether or not M is in that cell. Both kinds of counts are nondecreasing along M's full path, and their differences count newly joined larger companions exactly. A noninitial visit to M's own initial state by another original root would require an incoming odd prime q<=B dividing t-2=M (t odd), impossible for large X. No other root has the same initial state. Thus all counts at the original start equal 1.

Every meeting partner has |M-M'|<H/2, since both roots reach the common horizon with gain <H. Hence for each M only O(1+H/d)=O(u^.25) fixed cells can have a companion at any time. This is a count of possible source cells, not of physical arrival times.

At each noninitial vertex v on M's original path, with predecessor v-, assign a nonnegative logarithmic mass increment
    delta_M(v)=log(n_M(v)/n_M(v-))
             + sum_c log(n_(M,c)(v)/n_(M,c)(v-)).
The sums telescope despite expirations of smaller roots. For a fixed M their total is at most
    (1+O(1+H/d)) log(N+1) = O(u^1.25).
Summed over M,
    L_growth := sum_(M,v) delta_M(v) = O(Nu^1.25).    (1)
For the global count alone the stronger O(Nu) holds. We do not assume the total active mass of a physical state is monotone or count an expired smaller companion as present.

## 2. Long-window stable ancestry at negligible linear cost

Put
    D=floor(H/u²), epsilon=u^(-1/4),
with min1 as necessary. D>>B asymptotically. For a focal original pre-event vertex v=(t,C), let a_M(v) be the last original vertex of M with horizon <=C-D, or its own initial vertex if no such vertex exists. In the first case its horizon lies in [C-D-B,C-D], since every gain <=B. Define the event unstable if ANY of the global or fixed-cell counts has logarithmic growth from a_M(v) to v greater than epsilon. The rule is on full original histories, including all earlier paid events.

If a pre-event at C is unstable, the sum of delta_M over actual vertices with horizons in (C(a_M(v)),C] is >epsilon. Every such contributing vertex J has 0<=C-J<=D+B, including when a_M is the initial fallback. Let [C,C+p-1) be the original completed gain interval of the marked event. For a fixed contributing J, the marked intervals that can charge its increment are disjoint and contained in [J,J+D+2B). Multiplying the instability test by p-1, then reversing the finite sums, gives
    sum_unstable (p-1)
       <= (D+2B) L_growth/epsilon
       = O(NT/u^.5)=o(NT).                            (2)
Thus all actual waits and proxy r-cost on the marked events are negligible, by the original pointwise gain bounds. If only the global companion test is used the bound is O(NT/u^.75).

For a medium event E use its original completed E-plus-LOW block ending at F_E, with gain length <=B+L and actual clock b_M(E)<=3(F_E-E), where the inherited LOW threshold has L<=ell^.25. The blocks of distinct original medium events on a root are disjoint. The same Fubini proof with [E,F_E) instead of [E,E+p-1) gives
    sum_unstable medium blocks b_M(E)
       <= 3(D+2B+L) L_growth/epsilon
       = O(NT/u^.5).                                 (3)
In the existing frozen quota/phase ledger, the total of all directed allocations at a focal medium E is at most its original b_M(E). Pay EVERY remaining charge whose FOCAL event is unstable using (3). In particular the partner can be arbitrary, including one that never physically meets the focal root. No inference from the partner's own instability to the focal cost. The existing actual-time and gain-axis ledgers, partner normalization and all paths remain unchanged.

For every surviving original focal event and each tested cell, the count at ANY earlier original vertex w between a_M(v) and v satisfies
    exp(-epsilon) n_M(v) <= n_M(w) <= n_M(v),
and the same for n_(M,c). This follows from monotonicity, not from multiplying per-cut error factors. Thus any finite sequence of actual reverse cuts contained in this interval has total multiplicative shrinkage at most exp(epsilon), independent of the number of cuts. For a large companion group, nearly all larger members already shared the actual earlier physical state a_M(v). They then share the entire original path from it to v. This is a structural restriction on the large residual groups, not a bound on their starting masses. If the initial fallback is used, the stable counts must all be 1 once epsilon<log 2.

The restricted reverse-frontier code of 431f2423 can be evaluated on these common histories; all reverse cuts whose inspected predecessor events lie within the shared suffix are identical for those companions. The bound (2) pays large recent mass contraction rather than assuming an unrestricted contraction toward the original prime roots. The latter remains open.

## 3. Relative absorption of recent synchronous high-pair energy

Freeze the full natural high incidence set I: actual p>=Q and r(C)>p/sqrt(log p), before all accounting holes. At a physical prestate v with natural high events let n_I(v) count its original natural high tags. For any M in this group, its n_M(v) from section 1 equals one plus the number of larger tags of I at v. Indeed a larger companion visiting v cannot stop before a continuing smaller M, and its next event is the same natural high selection. Terminal tags smaller than M are irrelevant to this equality.

Let J0 be ANY retained subset of I after the earlier linear deletions and the unstable-event deletion. In addition discard all remaining tags at a physical prestate v if
    n_J0(v)<zeta n_I(v), zeta=u^(-1/8).
Its linear r-cost summed over the discarded groups is <=zeta sum_v r(C)n_I(v)=zeta R_I=O(NT/u^.125). This is a density gate on actual retained tags, not a claim of small removed quadratic energy. Call the final set J. If later linear thinning is required, put the gate last or include it among the monotone group tests of the existing joint peel: the physical reference count n_I is frozen, a removed group stays empty, and each group is charged at most once. Whole-horizon deletions cannot break the gate at a remaining horizon. We do not assert the gate persists under arbitrary subsequent holes without this provision.

For a retained smaller focal M at v, the number of larger companions which did NOT already visit a_M(v) is exactly n_M(v)-n_M(a_M(v)), at most (1-exp(-epsilon)) n_M(v). For a retained physical group of mass k=n_J(v)>0, the number of ordered pairs lacking that common earlier cut is at most
    2(1-exp(-epsilon)) k n_I(v)
       <= [2(1-exp(-epsilon))/zeta] k².
The factor two counts both directions; the stability test is applied to the smaller source. A tag with the initial fallback has no older companions, so every surviving older pair shares a cut at horizon at most C-D. Summing r(C) times these counts gives an exact relative upper bound
    E_sync,recent(J) <= beta E_J,
    beta=2(1-exp(-epsilon))/zeta = O(u^(-1/8)),        (4)
where E_J=sum_C r(C) W_J(C)² includes asynchronous and diagonal terms. In fact the same bound holds with the synchronous including-diagonal energy. This is NOT an absolute o(F) claim without a prior bound on E_J. The proof works for arbitrary initial holes in J0 because of the new linear density gate.

All other retained synchronous ordered products are between roots that have shared the entire physical suffix back to a vertex at least D earlier in gain, even if their first meeting and prior branching were much earlier. This is substantially longer than a polylogarithmic number of large jumps: D/B tends to infinity faster than any fixed power of u. There may be arbitrarily large ancestor mass at that shared cut.

The relative exit-imbalance estimate (6) of 4e8c7db is valid on the actual final J and gives O(E_J/u). It combines with (4) by adding the two nonnegative relative terms, not by treating either as an absolute energy deletion. The older first-meeting tail masks and all previous absolute pair masks still apply to J. Thus if E_oldrest denotes the actual retained ordered residual after all absolute masks and both relative classes, then
    E_J <= E_oldrest + o(F) + O(u^(-1/8)) E_J,
    E_J <= (1+O(u^(-1/8))) E_oldrest + o(F).           (5)
This only changes the sufficient target; it does not prove E_oldrest=o(F).

## 4. Source-distance-adaptive two-sided natural shared-clock exclusion

A separate absolute bound does not use physical meeting or the growth tests. For each unordered root pair M<M' with a shared natural I hit, order ALL its shared natural high horizons by increasing C. At a shared horizon C let
    A_-(M,M';C)=sum_{shared natural high D<C} r(D),
    A_+(M,M';C)=sum_{shared natural high D>C} r(D).
Use the frozen original I, not the final J (so accounting holes cannot create artificial short histories). The total shared natural clock along either path is <=1.5H. The pair can be asynchronous, synchronous, or change from asynchronous to synchronous along this list.

The candidate root separation h=M'-M is <H/2. For dyadic separation bands h in (d_j/2,d_j] with d_j=H/2^j, j>=0, and d_j>=1 when nonempty, choose
    K_j=max(1,floor(B u^1.5 H log(2+d_j)/(d_j (j+1)²))).
The uniform prime interval upper bound, as used in the earlier projected first-contact and band-birth papers, gives at most O(N d_j/log(2+d_j)) unordered candidate pairs in each nonempty band. It applies to short integer intervals as well with an absolute constant (for bounded d_j use the trivial bound). The total count over ALL bands is also O(NH/u) by the full source-localization interval and log H~u. No correlation of the two root primalities is assumed.

Pay a shared high product if A_-<K_j OR A_+<K_j. Each end contributes at most K_j+B in unordered natural clock, by monotone accumulation and r<=B; intersections are counted once. Thus for all retained pair products, including arbitrary subsets of their original hits,
    E_two-sided <= sum_j 4(K_j+B) O(N d_j/log(2+d_j))
                << N B H u^1.5 sum_j (j+1)^(-2)
                    + B O(NH/u)
                = O(F/u^.25)=o(F).                   (6)
When using the additive B term, use the total count of candidate pairs rather than paying B times an upper bound on the number of bands. The displayed estimate is also valid if a cap is larger than an entire pair's shared natural clock: then the whole pair is paid. There is no assumption about the number of shared visits, selected labels, ancestor groups or physical meeting.

Uniformly over bands with d_j>=B, K_j is at least a constant multiple of B u^2.5: log d_j>=u and 2^j/(j+1)^2 has a positive absolute lower bound. Bands d_j<B also have this lower bound eventually, since 2^j>=H/B and j=O(u), or can be handled by the already established near-source exclusion. Hence every remaining pair product has at least c u^2.5 shared NATURAL high hits strictly BEFORE and strictly AFTER its current horizon, and at least c B u^2.5 natural shared clock in each direction. These earlier and later hits need not themselves be retained. For an asynchronous current pair, every earlier shared natural high hit is necessarily asynchronous, since a prior physical synchronization would force their current vertices to agree. Thus the remaining asynchronous pairs require long actual shared histories without a prior physical merger, even when the frozen band-chain birth ranks are small. This trims entire short-lived pairs and both ends of long-lived pairs, not merely early young-chain births.

One can combine (6) with (5), since (6) is absolute on all retained J. The order of the absolute masks does not matter for the bound on their union. In finite diagnostics use much smaller cap parameters to exercise both paid and unpaid classes, not to model the asymptotic cap's prevalence.

## 5. Reproducible finite audit

Derived standalone ECMAScript research/min_prime_root_ancestry_growth_audit.mjs. Latest source commit 8efc9e242fa35534ae374ebe651551d835417f25, blob 1b6865bd26cfa8a4032cba45d570c4180a901fd9, exact remote readback. Commands:
    node research/min_prime_root_ancestry_growth_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_ancestry_growth_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress 256 1024 4096 16384 65536 262144

Executed actual audit function in the available ECMAScript runtime, not a separate Node invocation. Initial 14 successful runs (analytic/concurrent four X256..16384, analytic/concurrent/combined five stress X65536,262144). Final independent age-list oracle and arbitrary-hole density control added; all 18 final runs (three configurations across six X) passed. Other final-version modes not rerun. Original canonical MIN and previous ledger checks retained. All physical vertex lists include terminal vertices; full larger counts and per-cell counts checked monotone at every vertex; exact log telescopes; actual previous-cut overshoot; exact recent larger companion counts by independent membership in earlier physical state on the natural high groups; Fubini gain budget and actual E-plus-LOW budget; density and relative high energy bound; shared pair prefix/suffix weights accumulated on full natural I and independently recomputed by two-list intersection on every shared pair at X<=1024 and 128 largest shared-weight pairs per larger window. Independent fixed artificial holes before a fresh density gate verify (4); these control holes are NOT asserted to have negligible cost. Energy products are exact safe integers at tested scales, log and fractional medium weights checked with tolerances. No full asymptotic sieve verification or Lean compilation.

Diagnostic normal D=floor(B/8), epsilon=.125, zeta=.5; combined stress D=floor(B/2), epsilon=.25, zeta=.5. Adaptive cap uses B/16 (B/4 in stress) as base at d_j=H, and the same separation/log factors. Analytic D=H/u² and caps as above with finite diagnostic LOW/previous settings; its inherited medium and high prior pair residuals are empty, although ancestry and age controls nonzero. The finite analytic beta can exceed 1; the contraction is asymptotic. In normal finite runs stability deletion may be a substantial linear loss, not a numerically small one; its o(NT) estimate uses the asymptotic D,B,N,u scaling.

| X | preceding normal never cost | new never cost | total medium residual |
|---:|---:|---:|---:|
|4096|1.166667|1.166667|1.166667|
|16384|43.401515|42.553030|42.553030|
|65536|9.5|2.333333|55.266667|
|262144|62.518519|25.314815|67.714339|

Largest normal concurrent X262144, N20390, D169: total medium previous114.315830555, new focal instability pays46.601491931 (never37.203703704), remains67.714338624. 633075 original vertices checked, global/cell log totals27177.243531/30842.622602, marked events283419 (9677 cell-only), marked gain8990976, actual time6640735, marked full medium attached cost2781865. Combined stress largest prior medium62.625248545, additional25.445936375 (never11.148148148), remains37.179312169, never12.222222222 ->1.074074074. No claim that the finite large linear losses equal the much smaller fractional residual charge.

High isolated natural ledger after prior DIRECT rank, global and exact-factor window, and reverse frontier pair masks ONLY (not complete cumulative hybrid):
- Largest normal original natural I total proxy R_I=9700710; unstable marks remove4590841 linearly, density gate another722988, retained R=4386881. Natural retained E_J=66408501 including diagonal, recent synchronous ordered energy266722, old synchronous44544710, relative beta .4700123897. 1481 nonempty groups discarded by density,10895 exact retained focal earlier-companion checks. This linear deletion changes the ensemble of incidences; do NOT count its removed quadratic energy as an absolute o(F) mask.
- Largest normal 129690 actual unordered pairs with shared natural high hits, two-sided mask total154077026 ordered energy on full I offdiag, with all previous direct/window/reverse masks already applied its ADDITIONAL energy is60843738 (async31783565; front priority39741734, back-only21102004). Prior isolated residual80860571 ->20016833 after this absolute mask. Then linear stability/density deletion removes pair products11192907 (not an absolute energy estimate), recent relative class5376 more, leaving8818550 =8607043 synchronous older+211507 asynchronous. This is a finite diagnostic of the isolated ledger, not the actual full retained hybrid residual. Independent largest 128 pair oracle checked1210 shared hits. Arbitrary-hole control: retained E36291635, recent152464, density cost609291.
- Combined stress largest prior isolated residual57834193, age44692494, energy of linear-deleted products9501699, recent relative28298, residual3611702 (3610165 old sync,1537 async). Normal X65536 prior6155956 -> after age4473225 and linear products1074043, final608688 (601436 old sync). All partitions verified without double subtraction. Stress/normal changes in actual caps and linear deletions are not monotone comparisons of limiting estimates.

## 6. Next proof target

The new medium mark removes focal events near large relative physical ancestry growth, not all never-meeting pairs. The remaining medium pairs still evade previous actual-clock, gain-axis, local projected, and reverse history ranks; their focal larger companion groups are stable over the full D window. The new high sufficient residual has long two-sided natural shared history; its synchronous part already shares an actual long physical backbone with almost unchanged larger companion mass (in the full original histories), and its asynchronous part has many previous high overlaps without physical synchronization. One can now study the arithmetic of those long backbones and compare their state evolution across distant source cells. A bound on the masses at the oldest surviving shared cut, or a way to force a large logarithmic growth within sufficiently many such stable windows, would address the remaining mass problem. Mere repeated code-count estimates cannot prove this. Joint medium o(NT) and high o(F) on the same unbounded dyadic windows remain open. Main unchanged.
