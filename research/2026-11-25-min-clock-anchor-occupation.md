# Pointwise anchor occupation and same-high first physical merger energy

2026-11-25 JST. Continues 70efe438043f2621f2c4ea7c6881211d75b1b088 (tail-layer absorption), 73d8d17df179b01c1787a8e25c48fc7a3152a267 (physical anchor CRT), fa2d2d214de5c446c546913b66cdc851028a8e53 (projected first contact). New pointwise absorption without lower remaining-time threshold, two-sided prefix filtering, and actual same-high first physical merger decomposition with unconditional shallow/regular-thin bounds. The latter covers an important part of previously untreated ancestry formation, even if first projected contact preceded the high event. Paper proof, not Lean-compiled, full target OPEN.

## 1. Setup and retained family

Dyadic X, N=X/2 original odd M in [X,2X), B=ceil(sqrt(7X)), canonical MIN root (s,C0)=(M+2,2M-2), K(M)=floor((7M-1)/4). H=4B,a=2B and H+2B<=min(K-s) eventually. Actual full prefix includes root and first crossing state at or beyond s+H (or terminal twin). No rerun after deletion. C,t strictly increasing, C<=2t, total gain <=2H+B+6, actual waits <=2r(C) for positive least active prime r(C). Define w_M(C)=clipped wait duration in relative slab [a,H)/(2r(C)), zero if not occupied. Each R_M=sum r w<=B, R=sum R_M, E=sum_C r(C) U(C)^2, U=sum_M w_M. E includes both orders and diagonal. For unordered distinct pairs e(M,M')=2 sum_C r w_M w_M'. Target E=o(XB log^2 B), under no twins R=NB; o(X) original tag deletion preserves R=(N-o(X))B. No claim deleted pair energy is negligible from that fact alone.

Use P=ceil(B/log^(1/8)B), high selected prime p>=P, A=max(1,floor(log^(1/8)B)), physical high anchor alpha=(u,J,p) at actual post-event vertex. Two distinct anchors close if |J-J'|<=A OR |u-v|<=A. Earlier note 70efe43 proved maximum arithmetic graph degree D=O((A+1)B/P)=O(log^(1/4)B), and number of high hits per tag h<=floor((2H+B+6)/(P-1))=O(log^(1/8)B). Restrict to actual retained anchors if desired.

As in fa2d2d2, let ell=loglog B, L largest even primorial <=6 max(1,log ell)^1/4 with LOW cutoff y, T=ceil(20ell), g=max(2,TL), k_g=floor(1.5ell/log g), k=floor(ell/(8log g)). NonLOW means selected p>y. Prune o(X) entire original tags visiting exceptional reverse-degree d_y(C)>T within k_g completed nonLOW selections. GOOD tag at a state means <=k_g completed nonLOW selections; uniform original-tag cap m_g=O(L log^1.5 B)=log^(1.5+o(1))B at every horizon. RECENT tag has latest high anchor followed by <=k subsequent nonLOW selections; REGULAR means the actual post-horizons of those subsequent nonLOW selections have d_y<=T (anchor itself exempt). Number of regular projected keys at any horizon O(Lg^k), physical keys O(Lg^k B/P)=m_p=log^(1/4+o(1))B. Each physical key fixes the actual arrival time at that horizon by deterministic forward replay. These previously proved caps are used below at the actual predecessor horizon as well as at contacts. All other bounds hold for arbitrary retained subfamilies.

## 2. NEW all-past-anchor occupation norm (no small-tail penalty)

For each actual high anchor alpha define

    U_alpha(C)=sum w_M(C) over retained tags visiting alpha at or before C.

Include tags which have selected ANOTHER high event after alpha. This is not the occupation of tags whose latest anchor is alpha at C. For any C each tag occurs in at most h anchor groups, and every U_alpha<=U. Thus exactly

    sum_alpha U_alpha(C) <= h U(C),
    sum_alpha U_alpha(C)^2 <= U(C) sum_alpha U_alpha(C) <= h U(C)^2.

After summing over C with weight r(C),

    R_A := sum_C r sum_alpha U_alpha <= hR,
    E_A := sum_C r sum_alpha U_alpha^2 <= hE.          (1)

No lower bound on relative remaining times and no source cells are needed. This is an upper bound on total repeated internal occupation energy, including diagonals, not the earlier internal pair lower bound. It allows charge directly to actual energy at each later horizon rather than converting tail counts into energy via Cauchy.

## 3. NEW pointwise close-anchor edge estimates with prefix filtering

Use either FIRST PROJECTED contact (min common horizon, ignoring times) or FIRST PHYSICAL meeting (first common (t,C)). Suppose both latest high anchors at that contact exist and are distinct. They may be arbitrarily old, with no restriction on later depth or regularity. For a fixed pair of physical anchors the first intersection of their two deterministic continuations, in the corresponding projected or physical sense, is unique if it exists. Any first original contact occurring at/after both anchors must occur there. Root-specific prefix truncations only shorten the same continuation. For first projected contact equal projected keys (J,p) impossible; for physical first meeting equal projected keys with different times may occur. For physical meetings we require distinct full physical keys here; equal full key is treated in section 5.

At the unique contact v, take actual original groups with latest anchor alpha or beta there. They are disjoint. One may filter each group independently: discard a tag in alpha's group if its full path strictly before the contact intersects the common deterministic suffix of beta's group from beta up to but excluding contact, in the same projected/physical sense. Do the symmetric filter. A pair truly first contacting at v must pass both filters. This is only a necessary condition; prefixes prior to both anchors may also intersect. All candidate group members have a common deterministic suffix to contact from their respective anchors, so the filter does not depend on the identity of the opposite tag.

For each edge alpha,beta and later C let F_alpha,beta(C),F_beta,alpha(C) be sums of actual slab weights of the corresponding filtered groups there, irrespective of subsequent high selections. They are <=U_alpha(C),U_beta(C). With no filtering the same inequalities hold. For physical first meeting assign only contributions from the common physical suffix (subsequent visits with both roots are synchronized). For projected first contact assign all projected overlaps after the contact. In either case the actual edge-cell ordered energy is at most

    2 r(C) F_alpha,beta(C) F_beta,alpha(C).             (2)

The product includes all qualifying original pairs once per unordered anchor edge and horizon, and may overcount in projected case. Each fixed edge has only one contact for each contact type; no multiplier for #possible contact horizons or intervening history.

Set tau=log^1.5 B and I=log^1/2 B. At each later horizon C classify edge-cells by actual weights, rather than one classification of the entire pair:
- THIN when min(F_alpha,beta,F_beta,alpha)<=tau.
- IMBALANCED/FILTERED when min(F_alpha,beta,F_beta,alpha)*I<=max(U_alpha,U_beta), after thin (optional).

For thin, charge (2) to larger full occupation, <=2r tau max(U_alpha,U_beta). Each anchor charged at most D times per C, so by (1),

    E_edge,thin <=2 tau D R_A <=2 tau D hR
                 =O(XB log^(15/8) B)=o(XB log^2 B).   (3)

For second class, charge to anchor with maximal full occupation:

    F_alpha,beta F_beta,alpha <= max(U_alpha,U_beta)^2/I.
    E_edge,imb/filter <= (2D/I) E_A <=(2Dh/I) E
                       =O(log^(-1/8)B) E.            (4)

This is ABSORPTION, not an independent little-o estimate on this term. It has no low-tail restriction, no dyadic factor, and uses a weaker imbalance ratio sqrt(log B) on actual occupations than log B on tail-layer counts in 70efe43. If raw U_alpha,U_beta comparable but one filtered group is sufficiently small relative to the larger U, the same absorption applies. Conditions are pointwise, so different contributions of the same original pair can belong to different classes. Thin class permits arbitrarily large original group cardinalities with small fractional occupation.

The projected and physical contact types can both be used: choose a disjoint priority or union bound, paying at most a factor two in (3),(4). Physical first meetings may occur LONG AFTER first projected contact, and distinct latest anchors then need not be the anchors at first projected contact. This reaches new synchronized terms. No claim that the two-sided filter eliminates most mass.

## 4. NEW exact same-high merger cross-predecessor identity

Consider a first physical meeting at which both tags' latest physical high anchor is the SAME alpha=(u,J,p). Necessarily they meet AT alpha itself, because otherwise they would already share that earlier physical vertex. They both chose the same p at u from the common predecessor HORIZON D0=J-p+1, but at distinct preceding times t_1,t_2. (If their preceding physical states were equal, they would already have physically met.) Conversely, any two original tags selecting this high event from distinct preceding physical states first physically meet at alpha. Any earlier shared physical state would imply a common forward continuation and thus the same predecessor. Earlier projected horizon contact is allowed.

For each physical high anchor alpha, partition all actual original tags selecting it by their preceding time t at D0. For later C define U_alpha,t(C) as their total occupation from alpha onward, even after another high event. These disjoint predecessor groups partition U_alpha(C) exactly. Consequently

    E_samehigh,alpha(C)
      = r(C) [ U_alpha(C)^2 - sum_t U_alpha,t(C)^2 ].  (5)

The left side is precisely the ordered pair energy at C of first physical meetings at alpha with same incoming high label p. All participating pairs have distinct predecessor groups and share the continuation from alpha; they contribute only when both weights nonzero. Identity includes cross products of actual old ancestors in each group. Summation over alpha counts each such original pair once, since first physical meeting unique. This is a formation-energy identity for a physical merger, not just an arithmetic count of the possible merged vertices.

## 5. NEW unconditional and absorbing subterms of (5)

(A) One shallow predecessor history. Mark the tags in each alpha group whose predecessor state at D0 was GOOD. Total such tags per alpha <=m_g by uniform horizon cap, even if other predecessor groups arbitrarily deep/thick. Their occupation at later C is <=m_g. Using (1), their cross-predecessor energy satisfies

    E_same,good <= 2 m_g R_A <=2m_g hR
                 =O(XB log^(13/8+o(1)) B)
                 =o(XB log^2 B).                     (6)

This is a one-shallow/one-arbitrarily-deep estimate at FIRST PHYSICAL meeting, even though they share the SAME high anchor at the meeting. Previous projected distinct-key bounds could not apply at that meeting. The other side need not be recent or regular.

(B) Regular recent thin predecessor groups. For each preceding time t define U_alpha,t^reg(C) using only tags whose history was RECENT REGULAR at that predecessor (before p). At D0 the number of distinct predecessor times supporting any such tag is <=m_p: each of <=m_p regular physical keys has deterministic arrival time. Hence for the part of (5) involving at least one such regular subgroup with U_alpha,t^reg(C)<=tau, its total thin regular occupation at C is <=tau m_p. Thus

    E_same,regthin <=2 tau m_p R_A <=2 tau m_p hR
                    =O(XB log^(15/8+o(1)) B)
                    =o(XB log^2 B).                   (7)

This does not require the whole predecessor group thin, or any restriction on partner's history. Classification uses actual future occupation of the restricted regular subgroup. Previous recent-thin results required both histories recent at first projected contact; (7) applies after arbitrary prior projected overlap, and the other side can have no high anchor before this event.

(C) Small predecessor clock, arbitrary histories. If r(D0)<=Y=log^(1/8)B, every actual predecessor time t is in [u-2r(D0),u), so at most 2r(D0)<=2Y distinct predecessor groups exist, independent of depth or previous high labels. Restrict (5) at each C to edges between these groups. When min(U_alpha,t,U_alpha,t')<=tau, sum cross energies <=4r Y tau U_alpha. Thus

    E_same,clockthin <=4Y tau R_A <=4Y tau hR
                      =O(XB log^(7/4) B)
                      =o(XB log^2 B).                 (8)

When min(U_alpha,t,U_alpha,t')*I<=max(...), charge to larger squared group occupation, using degree <=2Y and sum_t U_alpha,t^2<=U_alpha^2. Hence

    E_same,clockimb <=(4Y/I) E_A <=(4Yh/I) E
                     =O(log^(-1/4)B) E.              (9)

These estimates cover the ENTIRE contribution from those first physical meeting pairs at subsequent horizons satisfying the relevant occupation condition, not merely the short incoming wait. In particular a fast high event can create a long common suffix, which was not excluded by the old fast-event incidence deletion. No bound for arbitrary large-r(D0) same-label incoming class follows from (8),(9).

Use disjoint priority among (6)-(9) or union upper bound. Combined with (3),(4) and previously negligible terms, the remaining energy E_rest satisfies

    E <= E_rest + o(XB log^2B) + O(log^(-1/8)B) E,
    E <= (1+o(1)) E_rest + o(XB log^2B).              (10)

The additional terms absorbed in (10) are not independently negligible without control of E. All estimates refer to the same retained family, so moving the E term to the left is valid for sufficiently large B. This extends reduction beyond close *distinct* physical anchors; (6)-(9) cover identical high anchors at physical merger. There is no complete balanced thick-group or threshold-crossing estimate yet. In particular large predecessor clocks, deep histories without regular recent thin subgroups, and comparable large occupancies remain. Far/anchorless contacts and nonhigh physical mergers remain as before.

## 6. Actual finite audit

Standalone research/min_clock_anchor_occupation_audit.mjs, final exact remote readback 18d4cbedeadd1a71e00e7175f7f5aeae2f2b8eec, blob 72cdfbd264df4b7c1db05db179d6c174ad3c4f84. Run:

    node research/min_clock_anchor_occupation_audit.mjs 1024 4096 16384 65536

Executed actual JS audit function in available runtime, four X1024..65536 x four base modes, then four extra clock diagnostics (20 final-equivalent runs; base script rerun after adding same-high identity, final modification only adds fifth mode and leaves the other four parameter choices unchanged). Not a separate Node invocation. 4658 literal parity-GCD comparisons at X1024 per mode. All original MIN prefix states kept, exact degree pruning, independent W^2 energy oracle. Anchor occupations include every earlier high hit, and global/pointwise norms (1) verified. Separate projected and physical first-contact edge maps: uniqueness, deterministic replay, two-sided prefix filter, each actual first pair survives both filters, edge-cell energy <=product (2), actual degree-based norm bounds. Same-high merge ledger verifies distinct predecessor times, regular key caps, shallow horizon cap, incoming interval count, exact independent cross-predecessor energy (5) at every occupied cell, and all bounds (6)-(9) with measured quantities. Integer counts exact; fractional energies use floating tolerances.

Analytic thresholds P=B/log^1/8 B,A=1,k=k_g=0 in these finite windows; no close projected or physical first contacts in analytic modes. Same-high analytic X65536 has 18418 first pairs and energy508122.44, but almost all remains outside new classes. Standard diagnostic P=ceil(B/4), A=floor(P/8), T6, k_g5,k3, tau/old thin4 for new pointwise classes (old regular-thin12, old weighted caps256/144), new I=2,Y=12; degree mode T4. Wide P=B/8,A=P/2,Y=ceil(P/4), rest same. Clock diagnostic same as wide but Y=B to exercise all predecessor-clock classes; NOT the asymptotic small-clock threshold. In standard mode no same-high first-meeting anchors have r(D0)<=12; wide has only four at X65536 and zero positive incremental clock-class energies. The clock diagnostic is nonvacuous for (8),(9) but does not establish their asymptotic small-Y saving.

Largest X65536, B678, standard diagnostic retained31824 after 944 roots removed, E=16529423.70, R=373244.5. E_A=36840026.36 (not an assertion E_A<=E; h36 finite). First physical meetings895784, of which same high anchor246824 (704 anchors), total actual later same-high cross-predecessor energy7220487.63, independently recovered by (5). Max predecessor degree9, max recent regular predecessor times2. Same-high class total before previous-priority filtering: good1975714.47, regthin87751.64, clock classes zero, remaining5157021.53. Different-anchor physical first contact edges52; 655 original physical first meeting pairs had such an edge but no close projected anchor pair. New disjoint extra after previous priority:

| class | ordered energy |
|---|---:|
| different physical anchors pointwise thin |2579.35|
| same high shallow predecessor |1299234.74|
| same high regular thin predecessor |71509.10|
| rest |8290903.62|

Prior residual9664226.81. Additional total1373323.19 (~14.21% of prior residual). The old-priority energy matches the earlier layer audit exactly. Note the new contributions are occupation incidences, not distinct pair counts unless explicitly stated.

Wide X65536 retained same family: prior residual8142549.47, new projected thin6075.89, distinct physical thin111.19, same-high good1056429.23, regthin134486.66, new rest6945446.51 (~14.70% reduction). Same-high first pairs362003,1291 anchors, exact energy8637572.60; max predecessor degree9, max regular times3. Two-sided projected prefix filter at wide removes 243 group memberships across 7 of 997 distinct anchor edges (may repeat same original tag across edges), but no additional positive-energy cell classified solely by filter in tested modes. Physical filter removes zero memberships in these modes. Thus the prefix-filter absorption is a proved bound whose extra positive-energy case was not observed; do not present it as a finite energy saving. Pointwise imbalance observed before priority (wide projected745778.80) but no incremental imbalance after prior classes in base modes.

Clock diagnostic Y=B at X65536: same high energy8637572.60 unchanged, clock thin416936.45, clock imbalance2432189.14 before prior priority; additional disjoint clock thin256604.47, clock imbalance1339889.69, residual5348952.35. This is solely a broad diagnostic, no asymptotic contraction or valid small-Y finite reduction claimed. Compare only within same parameter settings. The true analysis retains Y=log^1/8 B, and the proof of (9) depends on this.

## 7. Next problem

The same-high formation identity isolates actual products of predecessor groups even if the projected first contact happened earlier. It is a more direct treatment of physical group formation than counting rare close anchor pairs. The unresolved dominant parts are balanced thick predecessor groups at same-label high or medium mergers, especially long-clock predecessor horizons, and deep nonrecent histories. Need an independent control of the formation of large ancestry groups (e.g. first threshold-crossing of actual active tag sets under a cutoff-aware flow), not another noncontractive multiple of E. No complete energy upper bound or twin infinitude; main unchanged; no Lean compilation.
