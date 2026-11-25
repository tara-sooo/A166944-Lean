# Moving reverse ancestry windows and first-heavy crossing at the cubic-log clock scale

2026-11-25 JST. Continues eb2dfe093af6b242178baaa4ce488d4fd07b1693 (same-high physical formation), f83cb64cd8d883e3fdbb0dcfff3b9773f552e3ac (reverse exceptional-degree sets), fa2d2d214de5c446c546913b66cdc851028a8e53 (projected first contact), and imports the least-factor support theorem from f8d81fc374e78c1c2587de34890678957f0924f6 in the parallel prime-root lane. New unconditional first-heavy and moving-light bounds that permit arbitrarily deep history before crossing. Whole same-state suffix deletion for two such good-prefix histories, and whole projected-pair deletions. No full twin proof or Lean compilation.

## 1. Improved short-clock target

Use the actual canonical MIN dynamics, dyadic X, N=X/2 odd original M in [X,2X), B=ceil(sqrt(7X)), start s=M+2,C0=2M-2, original K(M)=floor((7M-1)/4), H=4B,a=2B. Assume H+2B<=min(K-s), eventually. Keep the full actual prefix through first vertex at or beyond relative H, or terminal twin; no reruns. Strictly increasing even C and time t; C<=2t; total gain <=2H+B+6; wait<=2r(C), r(C) the least eligible odd prime <=B dividing (C-1)(C+1), or zero at twin. All horizons in [2X,7X). Let w_M(C) be clipped waiting duration in relative slab [a,H)/(2r(C)), zero at unoccupied horizons. Thus 0<=w<=1, R_M=sum r w<=B, R=sum R_M, U(C)=sum w_M(C), E=sum r U^2. Under no twin in the prefix, R=NB. Deleting o(X) entire original tags preserves R=(N-o(X))B.

The least-factor support theorem in f8d81fc (research/2026-11-25-min-prime-root-minfactor-support.md) applies to all horizons independently of whether the sources are primes. For p=r(C), p divides exactly one C+sigma, sigma=+-1. Write (C+sigma)/p=2n+1; the forms 2n+1 and p(2n+1)-2sigma avoid all odd primes q<p and give two distinct forbidden residues for each such q. The established uniform two-form upper sieve with z=floor(p^1/8) gives O(X/(p log^2 p)+p^3/4)=O(X/(p log^2 p)) choices, uniformly p<=B; bounded p absorbed. In S(Z)=sum_{0<r<=Z}r, split p<=sqrt Z (at most O(X sqrt Z) total since each C has one r) and larger p (each bucket contributes O(X/log^2 Z), at most O(Z/log Z) primes). Hence

    S(Z)=O(X Z/log^3(2+Z)), S_*=S(B)=O(XB/log^3 B).      (1)

No trajectory distribution or lower-bound sieve assumed. Cauchy R^2<=S_* E now gives the weaker sufficient target

    E=o(XB log^3 B)                                     (2)

on an unbounded sequence of dyadic windows, after any o(X) original-tag deletion or o(XB) linear incidence deletion. Indeed under no twin R is asymptotic to NB, but the product in Cauchy would be o(X^2 B^2). Even one twin in each such window suffices for infinitely many, as its smaller prime >=2X-1. All earlier o(XB log^2 B) pair bounds remain valid, as do previous absorption inequalities. The cubic-log threshold is used in the NEW results below; it is not a proof of (2).

## 2. Frozen reference ensemble and eligible starting states

Set u=log B, ell=log u, L largest even primorial <=6 max(1,log ell)^1/4 with LOW cutoff y. Contiguous LOW-only gain <L. Depth means #completed nonLOW selected events p>y, not distinct labels. Reverse degree d_y(C)=#odd p in (y,B] dividing C or C+2. T=ceil(20ell), g=max(2,TL), D={C:d_y(C)>T}. As f83cb64 proves, total exceptional edge mass Dedge=sum_D d_y=O(X/u^4), by elementary sum 2^omega<=sum tau. For a horizon set S, relaxed reverse step consists of subtracting even LOW offset e<L, then reversing p in its candidate divisor set at the resulting post-horizon. Its distinct-horizon size <=g|S|+Dedge. The union of relaxed reverse ancestors through at most j nonLOW jumps, including final LOW offset, has size O(Lg^j(|S|+Dedge)). This bound ignores time and exact clock competition but contains every actual starting horizon of such a suffix.

Use the reference ensemble of all original odd tags after the earlier shallow degree pruning of fa2d2d2 (visiting D within k_g=floor(1.5ell/log g) nonLOW depth removes o(X) roots). Freeze its actual prefix lists and counts:

    A(C)=#reference tags visiting C, including terminal/final states,
    A(t,C)=#reference tags visiting physical state (t,C).

These are COUNT masses, not fractional clock occupation. Counts need not be monotone along a path because of arrivals, different physical times, and cutoffs. They will NOT be recomputed after further root deletion. Light projected means A(C)<=tau_P=floor(u^2.5); light physical means A(t,C)<=tau_S=floor(u^2.25). These grow relative to the previous thresholds.

As in prior note, GOOD-shallow refers to absolute nonLOW depth<=k_g (not the new first-heavy predicates). Its uniform mass per horizon m_g=O(Lu^1.5). High label threshold P=ceil(B/u^1/8), RECENT means <=k=floor(ell/(8 log g)) nonLOW selections after last high physical anchor, REGULAR means every intervening actual post-nonLOW horizon has d_y<=T. The number m_p of regular physical keys per horizon is O(Lg^k B/P)=u^(1/4+o(1)). Each key fixes actual arrival time by determinism, so the number of different times supporting regular recent tags at that horizon is <=m_p. No constraint on absolute history depth for regular recent.

A source-state incidence is an eligible START if it satisfies ANY:
(i) it is the original root state;
(ii) it is light projected;
(iii) it is light physical and that history is GOOD-shallow or RECENT REGULAR.
Call (i) or (iii) a CERTIFIED physical start. The number of distinct eligible tags at each C is at most

    K_start=1+tau_P+m_g+tau_S m_p=u^(5/2+o(1)).         (3)

There is at most one original root at each C, at most tau_P tags if light projected, at most m_g shallow, and at most tau_S at each of at most m_p regular physical times. Overlap only helps. This is an actual source-tag cap on STARTS, even if they occur at great absolute depth. An arbitrary light physical state is not by itself a projected tag cap; the extra certification is essential.

## 3. NEW moving exceptional pruning (not restricted to initial depth)

Choose

    k0=floor(ell/(4 log g)), k1=k0+1.

Then k0 tends to infinity; Lg^k1=u^(1/4+o(1)). Remove every reference tag having an eligible start at some visited C_s and a subsequent visited C_d in D within at most k1 further nonLOW selections (including coincident start and exceptional state). All decisions use original reference labels; no new dynamics or recalculation of mass thresholds.

The possible start horizons C_s lie in the relaxed reverse union of D through k1 steps. By (3) there are <=K_start original tags per such horizon. Therefore

    #new removed tags
       <= O(K_start Lg^k1 (|D|+Dedge))
        = O(X u^(-5/4+o(1)))=o(X).                    (4)

This counts original roots, not number of possible exceptional suffix words, and includes arbitrarily deep starts. No independence assumption between start and D. Added linear budget lost <=B times removed count=o(XB). The earlier shallow pruning and this new pruning have a total o(X) cost.

For a retained tag at C, call it MOVING if some eligible start on its prefix is at depth distance <=k1 from current state. In this case every intervening actual post-nonLOW horizon after that start is outside D: otherwise the tag would have been deleted by (4). Compress actual LOW blocks; each regular reverse nonLOW step has at most T labels and L/2 possible LOW offsets, followed by a final LOW offset. Hence there are at most

    m_leaf=(L/2) sum_{j=0}^{k1}(TL/2)^j

candidate starting horizons counted with multiplicity in the reverse tree. Each candidate start contributes at most K_start actual tags. This proves uniform current MOVING mass

    m=K_start m_leaf=O(K_start Lg^k1)=u^(11/4+o(1)).   (5)

For each C this bound holds regardless of earlier history, earlier crossings, or physical merging. If there are many eligible starts for a tag, use any one as a witness; counting all possible starts only overcounts. By (1),(5), writing U_mov for their fractional occupation,

    R_mov=sum r U_mov <=m S_*=O(XB u^(-1/4+o(1)))=o(XB),
    E-E_notmov=sum r(2U U_mov-U_mov^2)
                 <=2m R=O(XB u^(11/4+o(1)))=o(XB u^3). (6)

This is a simultaneous LINEAR and actual pair-energy deletion for arbitrary moving resets. It applies even if a tag returns to a light state after having crossed a heavy threshold long ago. It deletes incidences, not necessarily the entire tag, after (4). The original full lists must still be used to classify first contacts.

A structural consequence: at every surviving occupied incidence after removing MOVING, there was NO light projected horizon or original root within k1 preceding nonLOW selections, nor a certified light physical state within that distance. In particular at least k1+1 nonLOW events occurred and every visited horizon in that recent depth window was heavy projected. Under no-twin windows, for every fixed eps>0 all but o(X) retained roots spend less than eps B of their slab cost in MOVING states by (6). Thus most of their time budget lies in such uninterrupted heavy-history windows. This is stronger than merely requiring a large current occupation or a fixed absolute depth, but is not a contradiction by itself.

## 4. NEW first-heavy prefix predicates, arbitrary absolute depth before crossing

For each tag let i_P be the index of its FIRST visited horizon with A(C)>tau_P (absent if none). Define G_P as a GOOD PREFIX: before i_P, or from i_P through at most k0 further nonLOW selections. If the tag never crosses, G_P holds along its whole prefix. Call the part at/after i_P FRESH_P. If i_P is the root, the root itself is an eligible start. Otherwise the state just before i_P is light projected, hence an eligible start within at most k0+1 nonLOW selections of each FRESH_P state. Before crossing, the state itself is an eligible start. Therefore G_P is contained in MOVING and has uniform horizon mass <=m. Each tag has at most (k0+1)L/2 FRESH_P visits, by the LOW gain barrier, including endpoint states. It may have arbitrarily many G_P visits before crossing; do not use that smaller visit cap for all G_P. Monotone prefix status holds even if later masses become light again.

Similarly i_S is first visited physical state with A(t,C)>tau_S. Define G_S to hold before i_S (or throughout if no crossing). Extend it from i_S through at most k0 further nonLOW selections ONLY if i_S is the root OR the immediately preceding state was a CERTIFIED physical start. Call the extension FRESH_S. Otherwise G_S ends strictly before crossing. Before crossing G_S mass at each physical state <=tau_S (not at each projected horizon). On the extension it is contained in MOVING by the same predecessor argument. Define G=G_P OR G_S. Both are monotone-prefix predicates, hence their union is too. At each physical state,

    #G tags <=tau_S + m = u^(11/4+o(1)),              (7)

since all G_P and FRESH_S tags are MOVING, and the remaining G_S tags are physically light. The actual cap is valid after further root deletion, as the frozen reference counts are upper bounds on retained counts. This directly treats physical heavy-threshold crossings even when projected mass is already large, provided their entering light history is certified. Uncertified physical-light histories are still good BEFORE crossing but have no extension.

## 5. NEW whole SAME_STATE suffix via the expiry identity

At each physical vertex v let g_v be #retained G tags there and e_v be #whose LAST G vertex is v. Each tag has one expiry (root is G, final vertex allowed). If two distinct roots first physically meet while both G, they follow an identical deterministic suffix until either truncated path ends. Charge the pair to the earlier absolute-time expiry; the other root is still G at that same vertex. Conversely every pair counted this way first met while both G by monotonicity. Therefore, exactly as the earlier expiry theorem,

    F_GG = sum_v [ e_v(g_v-e_v)+binom(e_v,2) ]
         <= N(tau_S+m).                               (8)

Each unordered pair has total ordered common-state slab energy <=2B by per-root cost, even after both G prefixes have expired. Thus

    E_same,GG <=2B F_GG=O(XB u^(11/4+o(1)))
                         =o(XB u^3).                  (9)

This is a whole-suffix bound on actual original pairs, not a count of newly formed physical vertices. It covers two arbitrarily deep histories if they have not crossed the relevant heavy thresholds too long ago, including physically light predecessor groups that already have large projected ancestors. Does NOT count their asynchronous pre-meeting overlaps under (9); those are handled separately or remain.

## 6. NEW whole projected-pair terms at first projected contact

For distinct original tags with first common horizon C*=min(V_M intersect V_M'), their entire ordered slab pair energy <=2B, regardless of whether they subsequently synchronize or diverge. Count two new classes:
(A) one FRESH_P and the other G_P at first contact. Count from the FRESH_P incidence (at most N(k0+1)L/2 such visits); other side has <=m tags per horizon. Therefore F<=O(N(k0+1)L m) and E_fresh=O(XB u^(11/4+o(1)))=o(XB u^3). Either tag may have been arbitrarily deep before crossing.
(B) one G_P and the other RECENT (no regularity required). Each root has O(B/P) high hits, each recent window has <=(k+1)L/2 visits, hence total recent incidences X u^(1/8+o(1)). At each, <=m G_P partners. Thus E_rec,G_P=O(XB u^(23/8+o(1)))=o(XB u^3).

These whole-pair terms count every later projected overlap even after both prefixes expire. They extend the earlier absolute-shallow class at the weaker but sufficient cubic-log target. A pair with both G_P before first crossing and neither recent is NOT covered by (A) or (B) merely because both are light; G_P before crossing can be long. The actual current moving deletion covers their current incidences but not necessarily their entire later energy. The physical expiry estimate handles their common physical suffix if both G at first physical meeting.

Combine (6),(9) and section 6 by disjoint priority or union upper bound, together with any previous valid deletions/absorptions for the same retained family. Remaining E_rest=o(XB u^3) would suffice by (1),(2). This is a genuine independent new mass cap and whole-pair bound, but no general bound on the frequency of first heavy groups or on subsequent growth after all these moving windows expire. In particular balanced deep noncertified physical mergers and continued heavy projected ancestry can remain.

## 7. Actual finite audit

Standalone research/min_clock_first_heavy_audit.mjs, exact remote readback ba09294a45cbb7a7de6ff5747cb72d352d34d4f3, blob ff9533ab33d1a9430ad172e02990e7c4c9cae968. Run:

    node research/min_clock_first_heavy_audit.mjs 1024 4096 16384 65536

Executed actual JS function in the available runtime, four windows x four modes, all 16 final runs. Initial generated script failed with duplicate variable declaration (diag); corrected before successful runs. Not a separate Node invocation. 4658 literal parity-GCD comparisons at X1024 per mode inherited from canonical prefix. Freeze reference counts of both types, certify starts, enumerate exact distinct-horizon reverse layers of D, verify all actual flagged tags' witness starts lie in reverse union, count deleted roots and original cost. Checks actual post-nonLOW suffix regularity at fresh crossings, uniform moving/G_P/physical G cap including terminals, monotone good prefix, integer expiry equality, whole suffix and projected contact count bounds; independent E=sum r W^2 oracle and exact disjoint union of new classes. Floating tolerances for fractional energy. The sieve support is imported from the independent least-factor audit, not newly proved by the finite trajectories.

Analytic k0=k=k_g=0 in these finite windows, T=ceil(20ell) and no exceptional degree vertices observed. Diagnostic k0=3,k1=4, tau_P=12,tau_S=8, T6,k_g5,k3,P=ceil(B/4); wide P=ceil(B/8) (the new tests do not depend on A), degree T4. These exercise nonzero depths and exceptions; the asymptotic exponents are not numerically reached. Reference family itself has prior shallow degree pruning; do not compare to previous cumulative residuals without identical marks and priority.

At X65536,B678 standard diagnostic: original N32768, prior degree deletion944 leaves reference31824, second deletion388 all with an exceptional witness at depth>k_g, cost37943. Retained31436, R335301.5, E15274957.82 (reference E16529423.70). D has 551 horizons; relaxed reverse union intersects 34659 visited reference horizons, containing 117803 eligible-start incidences (overcounts root multiplicity). Actual maximum starts per horizon26, moving mass86, G_P mass64, physical extension mass60, G mass per physical state60. First projected crossings29058, of which918 at depth>5; first physical crossings24951, of which3752 at depth>5, 22518 qualifying physical extensions. Current G_P occupied cost zero but MOVING cost3213.5, moving energy45062.93 including diagonal; moving resets beyond first crossing thus nonvacuous.

First projected contacts2360202, first physical meetings881684. G-G first physical pairs223296 exactly equals expiry count; 53059 with at least one history beyond old absolute shallow depth, 199833 with at least one fresh extension. Whole ordered common-state energy2769348.40 vs currently G-G shared energy4955.83. Projected priority fresh class323465 pairs with energy2697324.70, recent class370691 with energy2050365.34; fresh and recent independent deep counters overlap priority classes. These overlap (9); do not sum independent totals.

New-only disjoint energy ledger on SAME retained family, using priority diagonal, current moving, whole projected fresh/recent, whole physical G-G common-state suffix, rest:
| term | energy |
|---|---:|
| diagonal |194258.73|
| moving, off-diagonal |43227.40|
| whole projected classes after moving |4747459.12|
| whole physical G-G after preceding classes |846817.89|
| rest |9443194.68|

Analytic X65536 (no root deletion, k0=0): E18998125.55, G-G first physical539936, whole shared E10897812.28, moving E4990323.74, new-only residual6267977.78. This reflects finite thresholds and not asymptotic savings. Wide X65536 extra cut392, same E15274957.82, G-G225817, new-only residual8645147.99. Degree diagnostic X65536 extra cut2744 of reference7596, retained4852,E76720.79,new-only residual3779.73, very substantial root removal; no numerical o(X) claim.

## 8. Next question

The cubic-log support improvement gives a full extra logarithm for the same original short-clock ensemble. The new moving cap and first-heavy expiry estimate do not merely enumerate shallow absolute histories: they start from actual bounded-mass incidences at arbitrary depth. The remaining problem is to control persistent heavy projected histories and physical groups formed from noncertified or already heavy predecessors, especially comparable thick ones. The frequency of first crossings globally is not yet bounded below o(X); the results control their subsequent local ancestry and the covered first-contact products. One next concrete direction is to use the improved least-factor support at each r-scale to bound the clock budget inside uninterrupted heavy-history stretches, rather than treating all such histories as one class. Main unchanged, no Lean compilation or proof of twin-prime infinitude.
