# Unified donor level episodes: common net descent exits and direct rough-target coercivity

2026-11-25 JST. Continues f522cdc29401d196066f84726bff94b2ed41520e. New paper deductions: an alternative to recursively estimating the inherited origin interaction graph, covering BOTH shared and inherited donor-square moments at once. First, each actual high-level episode is assigned to its first future true downcross in the common original recorded suffix, or to the earlier original endpoint. Second, the entire moment is controlled directly by natural occupation and actual net descent of the original rough target waits of the donor anchors. In the largest finite samples the first transport mostly reaches terminal survivors; the second mostly reaches positive-drift rough target waits. Both are conditional energy reductions, not small-o estimates for the controlling moments. No Lean compilation; twin infinitude OPEN.

## 1. Actual ensemble

Use the same original dyadic X, odd roots M in [X,2X), B=ceil(sqrt(7X)), u=log B, H=4B, s=M+2,C_initial=2M-2, gate K(M)=floor((7M-1)/4), fixed-cap deterministic MIN. Original completed waits include the crossing event at/beyond nominal cutoff, with e_M<=s+6B and possible earlier actual twin terminal. No charge after the original endpoints. True d=2t-C in [0,12B+6] and total gain <=12B+6. Each completed wait at C of length w, selected p and least eligible r satisfies w<=2r, r<=p, p>=3.

Retain long-age LOW donor anchors g of 24bfe41/a068c67, with actual last nonLOW selected event at t_g, common post horizon J_g, d_g=2t_g-J_g>6, and unique rough target completed slot of least eligible r_g>=R. Each actual donor through g has the same deterministic continuation from the anchor to that target. Let x_i(g) in [0,1] be the fixed actual normalized donor row weights. Keep D_g=d_g-6 and the gain-weighted square decomposition
    M^sharp = Z^sharp + 2 S^sharp + 2 I^sharp,
    S^sharp+I^sharp = sum_g (r_g/B) D_g sum_(i<j in g) x_i(g)x_j(g).
For each pair/anchor/level lambda=7..d_g there is weight w_ijg=(r_g/B)x_i x_j. Classify as shared if both actual last upcrosses agree, inherited otherwise, as in a068c67 and 58ad116. The two types exhaust all such contributions. Internal donor pairs need not have positive old cross charge between themselves. All estimates concern these donor moments, not the original W_g without the separate cross-to-donor comparison.

## 2. NEW canonical high-level episode and first future exit

Fix an actual unordered internal donor pair i,j and a level lambda. Its contributing anchor g lies at an actual common recorded post-state (same selected labeled event), after both last stationary upcrosses. Define an episode by the pair, lambda, and the two last actual upward keys in stable source order. If the pair subsequently drops below lambda and later rises again, the new upward keys identify a NEW episode, not a repeat of the old one. The shared/inherited type is fixed within an episode. Let e=min(e_i,e_j) be the earlier original recorded endpoint. For each contribution find the first future tick t after t_g with common true d(t)<lambda, if t<=e. From the common recorded anchor onward both tags have identical completed recorded waits through e. Between events deficit increases by 2 per stationary tick, so a first downcross can only be an actual common completed event. If there is no such event through e, assign terminal exit (e,C(e),lambda). The common state exists at e even if only one of the tags stops there.

This exit is independent of the choice of anchor within the same episode: there is no downcross/rebirth between contributing anchors with the same two last upward keys, by definition. More explicitly one can assign the levels at an anchor to successive strict decreases of the running minimum of the common post-deficit sequence initialized at d_g; each new record low assigns exactly the previously unassigned integers above that low. Levels never assigned are precisely the terminal survivors.

At a matched exit from actual common recorded state (a,C) to (v,C+p-1) the net drop
    Delta_-=p-1-2(v-a)>0
contains the matched lambda in the integer interval (d_v,d_a]. Indeed the level has survived throughout from the recorded anchor and was present at the preceding recorded arrival a. This is a NET recorded descent, not just the true tick jump p-3. Since all contributing anchors precede the matched exit, none can create a duplicate episode at the same pair/event/level. An episode that ends at the earlier original endpoint has lambda<=d(e) and there is at most one terminal surviving episode per pair/level.

For fixed pair, across all its actual contributing anchors (including distinct episodes), target slots are distinct and completed in both actual prefixes. Hence
    theta_ij=sum_g w_ijg <= sum_g r_g/B <=1.5(12B+6)/B<=27=U0.
No factor for the number of later rough slots or the number of episodes. In particular the sum of weights for any fixed pair/level over ALL episodes is <=theta_ij, and the same holds per exit. A pair sharing any actual anchor has |M_i-M_j|<=6B; thus O(XB) possible pairs. The endpoint and type assignments make no use of the origin interaction graph or of the previous same-slot/distinct-slot/skip classifications.

## 3. NEW full descent/terminal transport

Define D_net over all actual unordered source pairs sharing an identical completed recorded wait (both actual start state and actual departure, not merely same horizon or departure clock), with weight (p-1-2w)_+ per pair/wait. Define T over all distinct pairs sharing a physical state at their earlier original endpoint e (both present there), with weight (d(e)-6)_+. Restricting either sum to the actual supporting donor pairs/edges is also valid. The preceding exact episode partition gives
    S^sharp+I^sharp = C_matched+C_terminal
                     <= U0(D_net+T).                   (1)
At each pair/wait, the total weight of matched exit levels is <=theta_ij times its actual net drop; at the terminal pair it is <=theta_ij(d(e)-6)_+. This is an upper bound by the complete original descent and endpoint moments; T is not identical to the OLD masked terminal occupation charge and should not be equated with it. The exact partition has nonnegative terms and no charge after original endpoints. The inequality also holds with the pair-specific multiplier theta_ij inside the two controlling sums, hence pairs with theta_ij<=eta transfer with coefficient eta instead of U0. A large theta requires actual accumulated target gain >=eta B, but no assertion that such pairs are rare. The prior diagonal Z^sharp=O(XB) then gives M^sharp<=O(XB)+54(D_net+T).

Unlike the earlier future extension for the OLD terminal level ledger, (1) covers all shared/inherited episodes of the donor-square moment already at their original endpoints. The previous old-terminal reference extension cannot simply be counted again as a reduction of these donor moments; it would require allocating the new episode weights to the corresponding reference states separately. No universal bound on D_net or T is established here.

## 4. Absolute low-level, close-source and episode-token payments

Fix ell=max(1,floor(u^11/4)), m=u^11/4. Pay levels <=6+ell over all anchors/episodes of each pair: total <=U0 ell per pair. Then pay remaining weights for pairs with |M_i-M_j|<=ell: O(X ell) possible pairs, each has total <=U0*12B. Both payments total O(XB ell)=o(XB u³). This low-level filter is valid for BOTH shared and inherited moments (not only inherited); the close-source filter is about source values, not distance between upward origins.

For each remaining pair episode choose one token for each endpoint (M,z,C,lambda), the actual last upcross on that endpoint. A stationary original tick generates at most two tokens. Thus the number of distinct tokens is <=2 sum_M(e_M-s_M)=O(XB). Split each token into matched and terminal roles, with at most a factor two, since the same source's excursion can outlive a partner cutoff. Use capacity m per token/role on the total actual remaining episode weights incident to that role across all original partner endpoints and contributing g. Repeatedly pay all remaining incident episodes of any role whose current degree<=m. With fixed weights and capacities the cost is O(XBm)=o(XB u³), each role pays once. The residual has >m/U0 distinct partner source episodes per active role; in fact at a fixed token, a fixed partner source cannot have two different overlapping above-level episodes while sharing the token's actual state: after meeting, the reference suffix is deterministic until the token's death. The partner may have a later original endpoint but cannot generate a new level before the common excursion dies. Thus for fixed role a retained token needs >m/U0 distinct original partners. This bilateral iterative form is paper-only; the numerical audit uses the simpler disjoint orientation toward the smaller original source, separate matched/terminal groups, and a single threshold test on each such group. That one-sided ledger pays O(XBm) by the same token-count proof, and does not assert bilateral cores. Low/close and token payments are disjoint priorities.

## 5. NEW direct recorded rough-target coercivity

There is a separate short proof which bypasses both the origin graph and the first-exit partition for the entire offdiagonal donor moment. For each contributing internal donor pair at anchor g, both tags have the same actual recorded target arrival, the same completed target wait of length w, least eligible r=r_g, and outgoing selected p. This is because the nonLOW anchor is the same labeled event, the following LOW tail is deterministic, and both original paths actually complete the target slot. The target is paid once per pair, regardless of the number of levels or later old origins. The selected target wait need not be positive.

Define its natural ordered offdiagonal occupation product e=w²/(2r) and actual net drop delta=(p-1-2w)_+. Then
    r <= 18 e + 3 delta.                                (2)
Proof: write x=w/r>=0. Since p>=r and p>=3, p-1>=2r/3. For x>=1/3, 18e=9r x²>=r. For x<1/3, 18e+3delta>=r(9x²+2-6x)=r[1+(3x-1)²]>=r. This also covers zero drift and short negative waits. The constants separate the natural and descent terms more sharply than the initial 18(e+delta) bound. No probabilistic independence or lower bound on w is needed.

The total pair/anchor charge over all high levels is exactly (r/B) x_i x_j D_g, with D_g<=12B. Define E_target and D_target over DISTINCT actual supporting donor pair/target recorded waits, weighted by x_i(g)x_j(g) (or use unweighted as larger moments). E_target is the sum of e, D_target the sum of delta, with these weights. Then
    S^sharp+I^sharp <=216 E_target +36 D_target.         (3)
This is strictly limited to the actual ROUGH recipient slots of the long LOW donor anchors, and to pairs with the SAME recorded arrival there. Not all projected same-horizon products and not all positive occupation. Split target visits according to actual net drift:
    S^sharp+I^sharp <=216 E_+^full
                     +216 E_target,nonpos+36 D_target.
Here the full positive offdiagonal moment bounds the positive target subset because each distinct pair/target term is counted once and x_i x_j<=1. The descent term is supported only on nonpositive target waits. Thus the remaining special obstacle for this direct route is the nonpositive shared recorded ROUGH target moment, not the inherited-origin graph's arbitrary degree. It is still an open quadratic moment. Zero-drift targets are included in E_target,nonpos and do not contribute to D_target. A target with very short wait can be controlled by its drop; a near-zero net drift may still have large natural occupation. The statement is a new direct comparison of the ENTIRE donor square, not a proof of smallness for E_+^full or of closure of W_g. The old cross coefficients chi and recipient reuse are still open. No combination adds the overlapping transfers (1) and (3).

## 6. Audit

Standalone research/min_clock_donor_episode_exit_audit.mjs. Initial successful source commit 66361b4412e82abdbd96906d87daaadc80119b90, second ac8cc3b0d668b3629c5f18cd32e6b8c2640bdd45, final 3f2c06f0034acc646fb6de3d751452ffaf0a71be, verified exact blob 1ff9b39b03a588a4a80c35b973b508dbb6d3b851. First attempted global episode-storage execution returned an RPC error; no numerical result from that attempt. The successful audit instead stores each pair's episode ledger temporarily and aggregates source tokens. It retains original sampled rough levels, masks, donor anchor extraction, independent shared/inherited partition checks and literal MIN. It replaces the earlier downstream inherited crossing/origin analyses in ascentAudit by the new exit ledger (earlier functions remain in file but are not invoked in that path). Checks actual common recorded suffix, first future strict running minima and 128 literal true-tick first-downcross oracles per nonempty mode, canonical pair/upcross episode exit independent of anchor, per-pair total target gain and per-level weight caps, actual matched net drop intervals, original common endpoint, actual low/close disjoint filter and one-sided token budgets. Final code orders episode keys canonically, verifies per-source token counts, checks both actual rough target records, distinct pair/target keys and sharpened (2),(3). All final checks passed.

Run:
    node research/min_clock_donor_episode_exit_audit.mjs 4096 16384 65536
Actual JS function executed in available runtime, not separate Node invocation. 12 modes (3 X, two original occupations, independent L30/y5 and L6/y3), same 12 sampled original rough slot/level targets per X, diagnostic low and close threshold8, token caps1 and8, R=max(y+1,ceil B/16). Four modes nonempty (X4096 L6 both occupations same moment, X65536 L30/L6 full-positive). These are actual normalized sampled donor moments; not full original occupation, not asymptotic constants. No Lean compilation.

| X / LOW | total S+I | matched in actual original prefix | terminal | matched shared | matched inherited |
|---|---:|---:|---:|---:|---:|
|4096 L6 (either occupation)|10175.29412|169.58824|10005.70588|169.58824|0|
|65536 L30 full|1169082.55458|1990.41593|1167092.13865|1825.57817|164.83776|
|65536 L6 full|1511912.58408|4090.26844|1507822.31564|3775.60177|314.66667|

Largest L30/L6: 4417/20708 distinct internal donor pairs, 2899036/4468956 distinct pair-level episodes, 2899036/5222616 anchor-level checks, 0/753660 repeated episode incidences aggregated; max pair-level weights .40855457/1.02949853, max single episode .40855457/.64749263. 231/323 matched pair-recorded edges, net-drop supporting unweighted sums12012/19170; terminal supporting pair counts4417/20707 and terminal-cap sums4879476/19540476. Terminal inherited29785.13569/93434.17994. Low/close disjoint payments14027.83481+65286.91445 /44944.77876+78248.64602, eligible1089767.80530/1388719.15928. 65960/82106 smaller-source token-role memberships. At diagnostic cap8 all eligible matched paid (1550.97345/1957.02950), terminal paid54962.70796/68032.38938, residual terminal1033254.12389/1318729.74041. At cap1 matched residual1361.41003/1562.59587, terminal residual1086384.33628/1384682.37758. No general smallness of terminal tail. X4096 L6 cap8 all eligible7760.94118 paid.

Direct rough-target ledger (weighted actual pair products, independent of exit payment):
| X / LOW | charge positive target | charge nonpositive target | E_target | D_target |
|---|---:|---:|---:|---:|
|4096 L6|0|10175.29412|1470.00000|930|
|65536 L30|1156101.58112|12980.97345|942785.24121|12012|
|65536 L6|1496831.75811|15080.82596|2322700.68389|17550|

Actual distinct pair/target counts465/4417/33330. At X65536 both classifications about99% charge on positive targets; the remaining negative target share is finite sample only (X4096 L6 is entirely negative). No zero drift in these samples. L6 largest short w<r/4 sector320.38348. Max actual ratio charge/(x_i x_j*(e+delta)) 4.23971 at X4096 and1.22788 at X65536; this is not a fitted universal constant. The small observed nonpositive fraction is not a proof of its asymptotic negligibility. Main and other branches unchanged.

## 7. Next direction

Focus on the positive-drift rough target moment and the nonpositive shared-recorded target sector from (3) rather than continuing to refine the inherited-origin graph in isolation. The nonpositive target sector can be split by actual deficit drawdown fraction and exact equality of arrival state, with the target roughness and last nonLOW anchor geometry available. For terminal-heavy (1), an actual separate future extension with new episode weights may distinguish GAP/AFTER-BOTH/survivor, but does not resolve the terminal mass by itself. Full positive moment, cross-to-donor coefficient, recipient reuse and all original remaining sectors are still open. No twin infinitude claim.
