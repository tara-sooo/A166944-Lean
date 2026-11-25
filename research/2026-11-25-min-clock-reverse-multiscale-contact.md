# Nested primorial cuts, exact first-contact shells, and global first-contact quotas

2026-11-25 JST. Continues 22ea74efea4b5c6cb3610328b53a3d0609966773. New paper deductions: equivalence between equality of labeled crossing cohorts and the horizon of the true first physical meeting; nested primorial cuts that allocate every old terminal pair-level charge to exactly one first-contact shell; summable weighted opposite-cohort capacities across all scales and a comparable-label arithmetic envelope at shallow shells. Also a separate global first-contact arithmetic quota, which aggregates a pair's terminal charges over ALL its original rough origins instead of paying per origin, with distinct reset/nonreset support estimates. The heavy cores and small-label first-contact contribution remain open. No Lean compilation, twin infinitude OPEN.

## 1. Original setup and exact first physical contact

Keep X dyadic, N=X/2 odd original sources M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2, C0=2M-2, H=4B, u=log B, K(M)=floor((7M-1)/4). All original masks, weights and completed crossing-event convention are unchanged. e_M<=s_M+H+2B, d(t)=2t-C(t)>=0 and d<=12B+6 in the original recorded prefix. The old terminal charge at A=(C,v,lambda) is from a true stationary tick z=ceil((C+lambda)/2)<v with both original tags actually present at z-1,z in the same completed rough slot. Each pair-level weight is at most 1/2; each unordered pair total over all old terminal levels/slots is <=6B+3; the total source-origin membership count is O(XB) as in 5cc7609. In this note first physical contact always means the earliest shared true tick state in the FULL original histories, not first overlap of retained masks or projected horizon equality.

For a positive original pair-level edge, its first physical contact (t*,J*) exists and J*<=C, t*<=z-1. Determinism implies common true states until the earlier original cutoff. If M<M' then J*>=2M'-2 and t*>=s_M'. A shared tick at an earlier horizon cannot be followed by a split. These facts require the common fixed cap B and actual cutoff convention.

## 2. Exact nested crossing partition

For an even horizon boundary K<C, label each vertex of the origin graph by its unique actual first crossing of K:
    g_K(M)=(J,t,q), D<=K<J, J=D+q-1,
with the full physical post-state and selected prime. If 2M-2>K (root already on the right), instead assign a DISTINCT singleton label root:M, never one common root-inside label. All non-singleton crossings exist because the tag reaches C>K. For a primorial boundary (multiple of an even L) the previous block-entry lemma gives q>y for every such crossing, where y is the largest prime in L. The following equivalence holds for ANY boundary K<C:
    g_K(M)=g_K(M') iff J*<=K.                         (1)
Proof: equality for distinct roots cannot be a singleton. A common crossing label (J,t,q) implies the identical true preceding state (t-1,J-q+1), with horizon <=K, because both selected that q at tick t. Thus they met by that state. Conversely if J*<=K, both roots begin at horizons <=K and both follow the same true trajectory from their meeting. Their first event crossing K is necessarily after that meeting and identical. This argument includes distinct recorded arrival times into the same waiting state, and does not confuse a common post-state reached by different incoming primes with a common crossing label.

As K increases the partitions coarsen; in particular equal crossing labels at a smaller K imply equal labels at every larger boundary below C. Root singleton labels are essential for exactness. Put
    K_0 = L floor((C-1)/L),
    K_j = K_0 - L(2^j-1),   j>=0.
Stop at the first j with K_j below every original root horizon in the origin cohort. Use C as artificial upper boundary with ALL vertices in one class, since they really share C; no crossing beyond C is invented. Every pair separates at a UNIQUE first descending boundary j, and (1) gives the exact contact shell
    K_j < J* <= U_j,   U_0=C, U_j=K_(j-1) (j>=1).    (2)
Both lower entry keys at K_j are different, both vertices lie in the same upper class (all at j0), and both lower landing horizons J_i satisfy K_j<J_i<=J*<=U_j. This includes a root singleton, interpreted as its own canonical initial state, not a fictitious event. Before the respective crossing of K_j the two trajectories cannot have shared any physical state, since this would contradict (1). They may have different entry clocks, or enter at the same clock and horizon with distinct labels, so no ordering of entry clocks is assumed. For all supported pairs the horizon gain from either original root to C is O(B); there are O(log B) scales until the root singleton partition.

## 3. Summable actual multiscale partner capacities

Use the tiny even primorial L<=u^(1/16) from 22ea74e, f=u^(1/16), m=u^(11/4). Work with actual old pair-level weights at each origin A, optionally separately by GAP, AFTER-BOTH and survivor type. Freeze earlier payments if any. Assign every remaining positive edge to its unique shell j and common upper cohort P by (2). The distinct lower entry cohorts within P that occur on these actual edges are divided into three classes:
  root singleton, comparable nonroot q>=r(C)/f, small nonroot q<r(C)/f.
Let k_(A,j,P,c) be the number of occupied lower cohorts in class c (actual positive endpoints, not candidate labels). For each vertex M in P and each opposite lower cohort g in class c, constrain the weight of its current incident edges assigned to this shell and having opposite endpoint in g. Use cap
    b_(M,j,g)=m theta_j/max(1,k_(A,j,P,c)),
    theta_j=(j+1)^(-2).
For fixed M and j there is only one upper parent P. Sum over occupied opposite cohorts: at most 3m theta_j. Sum over all j: at most 3m sum theta_j <6m. This does not multiply by the number of cuts or incoming prime labels. Repeatedly pay all remaining edges of any constraint whose current weight is <=cap, once per constraint. The remaining weights are fixed throughout except for removal. By charging each payment to that constraint, the total paid at A is <=6m times its original vertex count. The same proof as previous weighted-core peeling yields the greatest admissible support independent of deletion order; this refers to fixed edge weights, not reoptimization of other quotas.

Summing original source-origin memberships O(XB), with bounded type split if used, gives the unconditional absolute energy payment
    P_multi=O(XB m)=O(XB u^(11/4))=o(XB u^3).          (3)
No reference length W factor, no log B factor for multiple reverse scales, and no loss of linear occupation. Both endpoint constraints hold on every retained edge. In particular each endpoint has >2 b_(M,j,g) distinct actual charged opposite partners through the SPECIFIC crossing cohort g at the SAME shell and SAME upper parent. The opposite histories are physically disjoint before the lower cut. A vertex can have many partners at other scales; they do not count toward this constraint. The cap may be <1/2 at a deep scale with many opposite cohorts; no uniform diverging partner count there.

This is compatible with the single-block quotas, global birth-key cap and future-destination quotas from earlier checkpoints. To combine, apply on the actual unpaid residual rather than adding overlapping raw paid amounts. A later fractional subtraction can destroy the strict degree inequalities, so reapply peeling on the actual remainder if the core condition is used later. The numerical diagnostics here compare independent payments, not cumulative prior masks beyond the original delayed masks.

## 4. Arithmetic restrictions inside shallow shells

At an assigned shell let Delta_j=C-K_j<=L 2^j, and width h_j=U_j-K_j<=Delta_j. For every actual nonroot lower entry g=(J,t,q) supporting such an edge, all completed gain from J to the origin C is C-J, with clock cost <=3(C-J); the remaining stationary time up to z is <=2r. Hence
    K_j<J<=U_j,  z-2r(C)-3 Delta_j <= t <= z-1.       (4)
For fixed J, parity s, q divides J+2s and t is in the single progression 0 or q+2 mod 2q. In the comparable sector q>=r/f>=cB/u^(2+1/16), there are O(1) such prime factors per side. The number of phases in (4) is O(1+(r+Delta_j)/q)=O(f(1+Delta_j/r)). Thus at each upper parent, and indeed across all parents at the same A,j, the comparable lower cohort count obeys
    k_comp <= O((h_j+1) f(1+Delta_j/r)).               (5)
The singleton root cohort count is O(h_j+1) because its initial horizon is in that shell. Small-label cohorts need a separate bound; no extension of (5) to them is claimed.

For shallow shells Delta_j<=u^gamma with fixed gamma>=1/16, we have Delta_j/r=o(1) and j=O(log u). Hence a surviving edge with opposite comparable cohort requires
    > c u^(43/16-gamma)/(1+log u)^2
actual partners within that specific cohort. For example gamma=1/4 gives exponent 39/16=2.4375, and root-singleton opposite constraints in such shallow shells have cap >=c u^(11/4-gamma)/(1+log u)^2>1/2 eventually. Consequently ALL such shallow root-singleton-opposite edges are removed by the quota: a singleton can contribute at most one edge of weight <=1/2. In fact this root-side elimination holds whenever (h_j+1)(j+1)^2=o(m), with a suitable constant for the non-asymptotic inequality. This is a quadratic absolute payment rather than deleting all roots in an interval. At the first shell j=0 one recovers the local comparable group count O(L f) and partner threshold Omega(u^(21/8)). For deep shells the count and phase width can be much larger; no similar lower bound there.

## 5. Separate global first-contact arithmetic quota (new)

The unique true first physical contact of a pair is a property of its original unmasked histories, not of its charged rough origin. It therefore gives a second partition of the entire OLD terminal ledger, aggregating over ALL original A and levels for that pair. The total charge of one unordered pair remains <=6B+3, irrespective of how many original origins it shares. This is crucial: the quota below is paid once at the first-contact key, not at every later rough origin.

Classify the first contact (t*,J*): root injection (one canonical start), jump into a state where the other tag is stationary, or two distinct simultaneous jumps. If neither tag is a root at this tick, at least one must have jumped; otherwise they were already equal at t*-1. Two incoming jumps must have distinct primes p,q, otherwise their true predecessors coincide, contradicting firstness. For each incoming positive p, with s=t* mod2,
    J*+2s=0 mod p,
    t*=rho(p,s) mod 2p,
    d*=2t*-J*=6s+2p k.
For two distinct jumps, pq divides d*-6s (also by direct divisibility of each). If nonzero, pq<=|d*-6s|<=12B+6. Thus at nonreset first contacts at most one incoming jump can exceed sqrt(12B+6); if a large incoming p>=Q then the other must be <=(12B+6)/p. At reset d*=6s, this product restriction disappears. A root injection with a simultaneous jump can occur only at the odd canonical root d*=6, and incoming p divides that root M'; root plus stationary is possible without any incoming jump. These are exact consequences of the true first tick, not a claim that every arithmetic candidate is reachable.

Choose fixed alpha>0 and Q=ceil(B/u^alpha), eventually >=7. For pairs having at least one incoming jump p>=Q at the first contact, assign the entire original terminal charge of the pair to its first-contact labeled key (t*,J*,p), taking the largest incoming positive label when there are two. Thus no pair is counted twice. This includes jump-stationary and root-injection jump contacts; pairs without large incoming jump remain outside this quota. We can also keep separate GAP/AFTER-BOTH/survivor weights if desired, combining them before the quota. Define reset/nonreset by d*=6s versus d*!=6s (for p>=Q, k>=0, and nonreset k>=1).

The number of possible distinct labeled first-contact keys in the original O(X) horizon rectangle has bounds
    S_reset=O(X sum_{Q<=p<=B}1/p)
           =O(X log u/u),
    S_nonreset=O(XB sum_{Q<=p<=B}1/p^2)
              =O(XB/(Q log Q))
              =O(X u^(alpha-1)).                       (6)
For each p, parity s and phase k, J*=-2s mod p has O(X/p) values (rounding harmless), and t* fixed. Reset phase k=0, nonreset has O(B/p) choices by original deficit strip. Standard Chebyshev reciprocal estimates give (6); no independent clock CRT enumeration beyond this. The count does NOT include all root pairs or assume one pair per key. It is also independent of reference extension length because first contact is ORIGINAL. A sharper distinct two-jump nonreset count with second-label q follows by p q | (d*-6s)/2 and p q|J*+2s: at fixed p,q there are O(B/(pq)) positive phases and O(X/(pq)) horizons, giving O(XB sum_p p^-2 sum_q q^-2), hence the same order, with extra actual q restriction. This sharper form is optional paper-only.

Let V_K be the actual aggregate old terminal charge on a first-contact key over ALL original slots/levels, after any frozen earlier payments. Pay min(V_K,cap) with
    cap_reset=B u^(15/4),
    cap_nonreset=B u^(15/4-alpha).
Then (6) gives
    P_contact <= cap_reset S_reset+cap_nonreset S_nonreset
              =O(XB u^(11/4)(1+log u))=o(XB u^3).     (7)
This is a new absolute quadratic payment with a factor B per key made possible by using unique ORIGINAL first contacts rather than an origin-level key. For example alpha=2 permits B u^1.75 on nonreset and B u^3.75 on reset; alpha=1/4 permits B u^3.5 on nonreset. A key receiving charge from only O(u^(15/4-alpha)) distinct pairs (with sufficiently small constant, by the <=6B+3 per pair bound) is entirely covered in the nonreset sector, and analogous reset count u^3.75. A heavy key can carry arbitrarily larger actual pair mass; (7) only pays a bounded portion. This does not show that large incoming labels rarely cause actual merges weighted by source multiplicity. The small/no-large-jump first-contact sector and high-charge keys remain open. No claim that reset absence or the nonreset product restriction alone solves them.

## 6. Scope and next target

The old terminal energy can now be reduced by (3),(7), along with prior birth and future destination payments, with total additional o(XB u^3). Residual edges must have a specific shell, common upper cohort and distinct lower cohort, plus actual partner mass exceeding the allocated cap. Shallow large-label and shallow root-singleton cases have stronger restrictions. The first-contact keys receiving large-label charges must also exceed their aggregate quotas (before subsequent payments). These structural reductions do not bound the sum of remaining high-degree graphs. Next investigate low-label first contact, especially jump-stationary events and canonical/virtual root contacts; use genuine separated precontact histories at the assigned shell and their bounded gain to estimate actual partner mass. The independent prime-root multigrid branch uses a different ensemble and projected-contact energy; no theorem transferred. Keep earlier terminal extension, immediate/later, distinct-slot, low-r and MED/full-positive residuals. No Lean compilation.

## 7. Finite audits

Standalone research/min_clock_reverse_multiscale_contact_audit.mjs. Initial source commit e23cf5bc7ee9cb0d9565ad21ce1f53e21e371b27, final source commit 3b5aa30f7d38095fcc6173cf53a3b34e54f90bea, exact final blob 0dfc478b5730f5d52e7fa8fc6a1f51b5dd4d7ec2. Uses the exact 22ea74e forward and inverse sampled-slot engine with original stress masks. New code assigns EVERY actual sampled old terminal edge (including root-inside) by first differing nested cut, checks exact first-contact horizon equivalence at every cut, common parent, landing and clock bound, first-contact incoming labels and nonreset product restriction, and compares up to64 first contacts per nonempty sampled origin/mode to independent literal true-tick scans. Checks actual comparable envelope by enumerating candidate J,p,parity and phases, total quota capacity, edge ledger and actual remaining degree constraints. New global first-contact control deduplicates original pair-level across sampled origins, verifies per-pair total <=6B+3, phase/divisibility and independent relaxed key counts, separate reset and nonreset caps. Initial counter const declaration failed before any result; corrected before committing valid runs. All final checks passed.

Run:
    node research/min_clock_reverse_multiscale_contact_audit.mjs 4096 16384 65536
Initial full multiscale execution: 3 X, 12 sampled slots each, scale threshold 4 or16, two occupations =12 window/threshold/occupation combinations (144 sampled origin/mode graphs). Final source rerun all 3 X at threshold16, both occupations=6 additional combinations. Actual function executed in available JS runtime, not separate Node invocation. Stress L30,y5,f4,D=floor(B/4), original delayed masks as before. Multiscale m=4,16 and large-first-contact Q=max(5,ceil B/4), numerical caps reset32/nonreset8 in sampled weights, NOT asymptotic caps or a full original terminal energy estimate. Single level lambda=2z-C per selected origin; no future extension/type split here. The audit independently pays the multiscale graph and first-contact key quota on the same original sampled charge (not cumulative). The shallow asymptotic exponent and two-jump count proof are paper deductions, not numerical estimates. Many selected samples have zero late-HIGH terminal charge.

At X65536 (B678), full-positive sampled energy28022.47055 on 73625 pair-level incidences, 50620 distinct pairs. All 4 nonempty sampled graphs survive threshold4; threshold16 pays183.98507 leaving27838.48548. Late HIGH sampled zero. Exact first-contact classification raw across these samples: root injection1617.08150, jump-stationary24491.61350, two-jump nonreset0, two-jump reset1913.77555. The zero two-jump nonreset count is a finite sample fact, not a general exclusion. At threshold16 residual1615.08666,24309.95575,0,1913.44307 respectively. Largest actual comparable groups in an upper parent5, small3. 256 independent literal first-contact oracle checks at this X per scale threshold. The key diagnostic Q170 has nine realized large-label reset keys with weight192.18118, quota paid108.26421, remaining83.91697, max278 distinct pairs/key. No large nonreset key realized in these sampled energies, despite relaxed arithmetic support reset38067,nonreset485746. At X4096 there are two large reset keys in both occupations, no large nonreset. At X16384 no large-label contact in sampled charge. Thus the large nonreset arithmetic estimate has no nonvacuous large-key realization in these runs.

Sampled full-positive multiscale ledger:
| X | threshold | raw | paid | remaining |
|---:|---:|---:|---:|---:|
|4096|4|1195.8690|42.3801|1153.4889|
|4096|16|1195.8690|70.7129|1125.1561|
|16384|4|99.7943|66.7156|33.0787|
|16384|16|99.7943|85.7731|14.0212|
|65536|4|28022.4705|0|28022.4705|
|65536|16|28022.4705|183.9851|27838.4855|

At X65536, C203040 origin with235 roots from previous checkpoint, raw10920.4928 on27495 edges, shell distribution:
| shell j | cut K_j | raw energy |
|---:|---:|---:|
|0|203010|5485.6245|
|1|202980|0|
|2|202920|0|
|3|202800|1346.8051|
|4|202560|2069.8267|
|5|202080|1633.5704|
|6|201120|384.6661|
At both thresholds all these edges survive. In particular the old within-single-entry portion5434.8682 is now resolved exactly into four earlier first-contact shells, while the old cross-entry portion5485.6245 is shell0. For C165690, previous all215 roots in one small entry group, total10129.0672 splits into shells j3=3964.8881,j4=1861.5821,j5=3934.9478,j6=367.6493; threshold16 pays94.2239 from shell3 only. This establishes the actual ancestry geometry without producing a numerical contraction at the largest sample. X4096 late raw682.3904, paid0.0061 at threshold4/0.0549 at16; X16384 and65536 late zero. No asymptotic inference from this selective finite audit. Main and other research branches unchanged.
