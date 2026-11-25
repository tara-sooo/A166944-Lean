# Inherited same-slot hits: surviving ascent levels, bilateral level cores and positive-square transport

2026-11-25 JST. Continues dd8b3aa6998658a2d34e3f5fbe3c3a9c685d2e15. New paper results: same-slot HIT is unique per internal pair; the inherited count is bounded by the earlier arrival's actual positive NET drift, arrival age and shared post-deficit; positive-positive hits transport to the FULL SAME-SLOT positive occupation, and nonpositive late arrivals have an exact mixed natural/net-drop representation. A more useful refinement builds a bipartite core at each actual slot and surviving ascent level. BOTH sides can be peeled with an absolute O(XB log^(11/4) B) budget, including the late independent donor (whose upcross occurred elsewhere). Balanced actual level graphs transfer to a surviving-positive ascent square, itself bounded by SIX times the full positive same-slot occupation including diagonal. Remaining unbalanced levels, distinct-slot hits and skips remain open. No Lean compilation; twin infinitude OPEN.

## 1. Setup and sharp same-slot level interval

Retain original all-odd dyadic roots M in [X,2X), N=X/2, B=ceil(sqrt(7X)), u=log B,H=4B,s=M+2,C0=2M-2, original gate K(M)=floor((7M-1)/4). Actual fixed-cap MIN, complete original waits including crossing event, stop by s+H+2B or earlier twin, true d=2t-C in [0,12B+6], total gain <=12B+6. For a completed wait at C of length w, selected p and minimal r, w<=2r<=2p<=3(p-1). No new occupation. Use inherited aggregate pair-level b_ij(lambda)<=U0=27 of 58ad116, actual internal donor pair source separation<=6B and O(XB) possible pairs. Sum is I^sharp. Every contributing pair-level survives through its later donor anchor; weights are independent of the number of anchor targets after the gain-weighted aggregation.

Pay the previous low and recent filters at ell=max(1,floor(u^11/4)): lambda<=6+ell or one independent last upcross less than ell ticks before true first contact tau; total O(XB ell). For the remaining level, let L be the source with the later last-upcross clock z at horizon C, and E be the earlier-upcross source. In dd8b3aa, E's first crossing of C is a HIT if it lands exactly C, and same-slot if both tags depart at the same v. In this case E arrives at b=tau, L arrived at a<z<b, and both actually complete the same outgoing p at v. L is the earlier ARRIVAL but later UP-CROSS origin. These orientations are fixed for all assigned same-slot levels of this pair. The first true meeting is unique, so a pair can contribute to AT MOST ONE such same-slot key (C,v), regardless of which levels and subsequent g are counted. This does not apply to distinct-slot hits.

Define w_L=v-a, w_E=v-b, Delta_L=2w_L-(p-1), Delta_E=2w_E-(p-1), d_a=2a-C, d_v=2v-(C+p-1). Note d_v is the actual POST-event deficit, NOT the pre-jump stationary value 2v-C. The late origin z=ceil((C+lambda)/2) was a true stationary upward crossing of L and survives through v to g, so
    d_a < lambda <= d_v,
    lambda <= 2(b-ell)-C
(the latter from z<=b-ell). The positive net drift Delta_L>0 is necessary. Delta_L-Delta_E=2(b-a). Therefore the number of eligible same-slot levels of a fixed pair is bounded by
    n_ij <= [min(d_v,2(b-ell)-C)-max(6+ell,d_a)]_+
          <= min(Delta_L, 2(b-a)-2, (d_v-6)_+).       (1)
Each b_ij<=U0, so total charge of this pair here <=U0 n_ij. No assertion that every integer in the interval is a charged inherited level: it must also have the independent earlier origin, survive, and receive actual weight from a later anchor. In particular NO contributing inherited level is consumed at v, even when Delta_E<0; the negative drift of E consumes higher levels. The possibility of consumed inherited levels at v is excluded by definition.

Since a pair contributes to at most one same-slot key, all such charge for which Delta_L<=ell OR age b-a<=ell OR d_v<=6+ell OR r<=ell/4 is O(XB ell). For the last case use Delta_L<=2w_L<=4r. This is an additional absolute payment on I^sharp, after the previous low/recent filters; not one-for-one on original cross weights W_g. Remaining pairs have positive receiver drift>ell, arrival age>ell, d_v>6+ell, r>ell/4. No lower bound comparable to B is inferred.

## 2. Same-slot positive-positive and mixed transfers

For each same-slot key S=(C,v) let P_S=sum of w/(2r) over actual full positive net drift original visits, and N_S=sum over actual NONPOSITIVE visits of (p-1)/(4r). All tags at S have the same outgoing p. Equivalently N_S is their sum of w/(2r)+(-Delta)_+/(4r), exactly since Delta<=0. Define
    E_pos^slot = sum_S r P_S² = E_+^full + diagonal,
    E_mix^slot = 2 sum_S r P_S N_S.
Here E_+^full denotes the original full-positive same-slot ordered offdiagonal moment, as in a068c67; the diagonal is O(XB) because w<=2r and sum r over original visits O(XB). The mixed moment includes actual nonpositive waits with their natural weights PLUS one-half of actual net negative drift normalized as in dd8b3aa. It is a same-SLOT moment, not the full projected same-horizon product.

If Delta_E>0, then w_E>(p-1)/2>=p/3>=r/3. Its actual same-slot ordered offdiagonal product with L is e=w_L w_E/(2r)>=w_L/6. Since (1) implies charge<=2U0 w_L, the total positive-positive sector is <=12U0 E_+^full=324 E_+^full.

If Delta_E<=0, define delta_E=-Delta_E>=0. Its mixed pair term is
    e_mix=w_L w_E/(2r)+w_L delta_E/(4r)
         =w_L(p-1)/(4r)>=w_L/6.
The equality holds at zero drift too. Thus the mixed sector <=12U0 E_mix^slot=324 E_mix^slot. No repeated pair/horizon factor: charge aggregated across all anchor g, and actual pair/S counted once. The same-slot restriction is sharper than using full E_proj and E_+,-^proj. The full mixed moment is still open. In particular this actual first common recorded departure may be a recorded birth, so the mixed negative product cannot be claimed a shared recorded descent of a previously born pair. Nor can it pay the inherited levels by matching a downward crossing of those same levels.

On slots with N_S<=kappa P_S, the mixed portion <=648 kappa sum_S r P_S². This holds also with P_S,N_S computed from only participating actual vertices of the corresponding raw support (subset of full occupation). A fixed bounded kappa transfers this sector to positive-only occupation; small kappa gives a small coefficient, conditional on the positive moment bound. No universal balance is proved. This coarse slot balance is separate from the sharper level balance below.

An optional aggregate role-core (audited): per actual earlier-arrival positive vertex S give capacity m Delta_L on its outgoing role, per later-arrival vertex give capacity m r on its incoming role, m=u^11/4. Sum both capacities over all visits O(XB m), since Delta_L<=4r and sum r=O(B) per source. Iterative removal of incident edge weights at low-degree roles costs no more. Each pair weight<=U0 Delta_L<=4U0 r; both retained roles then have actual partners in the relevant slot (earlier role >m/U0; later role >m/(4U0)). One tag may serve both roles but count at most twice. Diagnostic uses m/B instead of asymptotic m for the aggregate role ledger so it can be nontrivial, explicitly separate from the level-cap test. No actual occupation changes.

## 3. NEW bilateral slot-level arrival core

Instead of aggregate pair weights at a slot, form the actual bipartite graph separately at every (S,lambda) after previous payments. Left vertices are the actual L tags with a true stationary upcross at z=ceil((C+lambda)/2), surviving to the post-state v. Right vertices are the actual E tags arriving at b>=z+ell after an independent last upcross at a different horizon. At this level a source cannot be on both sides because left arrival a<z and right arrival b>=z+ell. Both are actual original complete visits at S. Each edge is a positive inherited pair-level b<=U0, unique at S,lambda and never replicated across later anchors. Do not use all possible ancestor tags as edges.

The critical membership budget includes the RIGHT vertices even though their own upcross is elsewhere. For fixed S all eligible levels lie in the SAME surviving ascent interval
    2v-C-4r < lambda <= d_v,
because a>=v-2r and lambda>d_a. Its length is <=4r. Thus each actual source visiting S can participate at <=4r different lambda, with disjoint roles per lambda. Sum over all original visits:
    sum_(S,lambda) #actual endpoint vertices
        <=4 sum_(M,actual original completed visits) r
        <=6 sum_M total gain
        =O(XB).                                      (2)
No later-anchor, reference-length or log-scale multiplier. This is stronger than treating right-side arrivals at each level as unrelated possible sources; the budget follows from their ACTUAL completed slot memberships.

Set m=u^11/4, and at each S,lambda repeatedly pay all currently remaining edges of either vertex whose current weighted degree<=m. Each vertex pays at most once at that key; each edge once. By (2)
    P_level=O(XB m)=o(XB u³).                         (3)
Every retained vertex now needs >m/U0 distinct actual charged opposite partners at that very level, actual slot and first-contact role. The largest admissible support for these fixed weights is independent of peel order. Any subsequent fractional payment may destroy this property; repeat on the actual remainder if needed. This can follow previous excursion/entropy/aggregate/rough quotas as disjoint priority; the audit compares independent ledgers.

## 4. NEW six-constant surviving positive ascent square

For actual full positive visits i at a fixed S define their recorded surviving ascent intervals (d_i,d_v] in integer levels. Let A_full(S,lambda)=number of visits with d_i<lambda<=d_v, lambda>=7. Every left vertex from section3 is in this actual count, even if its first-contact history with a right vertex is different. Define
    Q_asc = sum_(S,lambda>=7) A_full(S,lambda)^2.
This is a positive NET ascent level square on shared actual completed slots (includes diagonal). At a fixed S two such intervals share their upper endpoint d_v, hence their full overlap has length min(Delta_i,Delta_j). Restriction lambda>=7 only reduces it. Expand the square over ordered tag pairs including identical ones. Put a0=p-1>0. For w=min(w_i,w_j) we have
    min(Delta_i,Delta_j)=2w-a0 <= w²/a0 <= w_i w_j/a0,
since (w-a0)^2>=0. Also 4r/(p-1)<=4p/(p-1)<=6. Therefore
    Q_asc <= 6 sum_S r P_S²
          =6(E_+^full+O(XB)).                       (4)
This sharpens the cruder 12 or24 constants from a generic level-count bound. It is actual recorded positive ascent overlap, not the shared-recorded-edge flux A_shared (earlier arrivals need not share their recorded starting states), nor a claim that Q_asc itself is small.

For any remaining level graph write n_L,n_E for numbers of actual positive incident vertices on each side. The total weight <=U0 n_L n_E. In the BALANCED sector n_E<=kappa n_L at that level (any chosen fixed kappa>0),
    charge <= U0 kappa n_L² <= U0 kappa A_full².
Sum over any such slot-level keys, and by (4),
    I_same,bal^sharp <=162 kappa(E_+^full+O(XB)).     (5)
No assumption on Delta_E is needed: this handles positive, zero and negative late visits together without E_mix or E_proj. Balance here concerns actual incident SOURCE COUNTS at the specific surviving level, not just P_S,N_S at the whole slot. Slot balance and level balance need not agree. This is verified by a finite example where the whole slot is balanced but some levels are strongly unbalanced.

Consequently, after (3), every nonempty unbalanced graph has >m/U0 vertices on EACH side and n_E>kappa n_L, with actual high-level independent earlier origins. In particular it is not enough for one side to contain many uncharged ancestors. Equations (3),(5) give
    I_same^sharp <=162 kappa E_+^full + I_same,unbal^sharp
                     +O((1+kappa)XB u^11/4)          (6)
including additional small and previous low/recent payments, for fixed kappa. One may separately transfer all positive-positive edges as in section2 and then use (5) on actual residual mixed edges; no overlap added. For example with kappa=1, all balanced level cores transport with constant162. For a growing kappa the factor remains explicit; no uniform bound on unbalanced charge or E_+^full. No circular absorption of the original total energy. Distinct-slot and skip cases of dd8b3aa remain outside (6).

## 5. Audit and finite observations

Standalone research/min_clock_inherited_same_slot_audit.mjs. Initial source 8997ae4034bf8e49db8e013f34c12915154f6a8b, second c44f3872fc111edba6b0c0e3240639b6a5dc4ebc, final 11936c2b698b77ab1e1605218a1f4137be8b1fcc, exact final blob 53c3d08351e6bbc7b50a7d507f927bce82d858a3. The initial audit used the pre-jump value 2v-C in the post-deficit variable; corrected to 2v-(C+p-1), reran all samples, numbers unchanged because the inherited levels actually survive the outgoing jump. Initial level oracle skipped fully emptied graphs; final includes them. All final checks passed, including actual level interval, unique same-slot pair, drift and arrival gap, exact mixed identity, fixed role/level cores, membership bound per slot, independent repeated-peeling oracle up to64 level keys, and sharp six-constant full ascent-square transport. Actual positive-square test uses the original waits of all participating sampled vertices, not full all-source occupation. No Lean compilation.

Run:
    node research/min_clock_inherited_same_slot_audit.mjs 4096 16384 65536
Actual JS function executed in available runtime, not separate Node. Final 36 slot/level ledgers: 3 X, two original occupations, independent LOW L30/y5 and L6/y3, diagnostics (ell,m)=(4,0.25),(4,8),(16,32), same 12 sampled original origin-levels per X, original masks unchanged. Several ledgers empty. Aggregate role uses m/B while per-level capacity uses m; neither is asymptotic. These are independent payments on same actual eligible sampled I^sharp; do not add them. Balance threshold kappa=1. Additional small-Delta/age/end/r sector empty in these samples, because previous low/recent filters already exclude it here. Paper (1) proof also yields the upper endpoint 2(b-ell)-C via the explicit z inequality checked in code. No general elimination of low drift from finite data.

Largest X65536 full-positive ell4 same-slot sector:
| LOW | raw same-slot | positive-positive | positive/nonpositive | actual same-slot keys |
|---|---:|---:|---:|---:|
|L30|26069.93805|319.56047|25750.37758|3|
|L6|40800.23304|14888.01475|25912.21829|14|
All mixed late arrivals strictly negative, no zero or short w_E<r/4 here. All coarse slot mixed weights satisfy N_S<=P_S on participating vertices. Restricted positive pair product14349.46318/61489.59848; mixed product15056.37313/15230.16624. Aggregate role m8 pays only17.98230/18.61652 respectively; NOT a numerical contraction. At X4096 L6 ell4 there is one actual short negative same-slot hit1.45882, mixed natural0.9 and actual drop product1.8, combined mixed1.8, showing the short mixed formula nonvacuous. Its same-slot charge43.76471, of which42.30588 positive-positive. The remaining X16384 and larger late samples empty.

Level cores:
| X65536 classification | ell | cap m | same-slot raw | paid | balanced residual | unbalanced residual |
|---|---:|---:|---:|---:|---:|---:|
|L30|4|0.25|26069.93805|59.19174|26010.74631|0|
|L30|4|8|26069.93805|26069.93805|0|0|
|L30|16|32|22850.45723|22850.45723|0|0|
|L6|4|0.25|40800.23304|88.03835|26023.94690|14688.24779|
|L6|4|8|40800.23304|40800.23304|0|0|
|L6|16|32|26405.33333|26405.33333|0|0|

For ell4 L30/L6 respectively 146/340 level keys, 10502/24094 actual source-level memberships, full restricted positive-square Q1076242/2071290. At m0.25, 20/64 keys fully paid, actual remaining max right/left count ratio .8181818/81.5, balanced square770058/770204. L6 unbalanced residual14,688.25 despite all coarse slot mixed mass balanced. L30 all residual balanced. At m8 all keys fully paid in both, with total available capacity84016/192752; actual payment much less. Thus finite full removal uses the per-level absolute budget and the actual edge weights, not a claimed asymptotic contraction or general all-source bound. X4096 L6 ell4 m0.25 paid1.45882, balanced42.30588, m8 all43.76471 paid. Same donor moments in both occupations there. At ell16 no eligible X4096. All independent oracles passed. Main and other branches unchanged.

## 6. Next direction

For the new residual (unbalanced level graphs), the right-side donor count greatly exceeds the actual surviving ascent class at S,lambda. Their earlier last upcrosses are independent of the left origin; group these right vertices by their actual earlier (z,C) and actual arrival/entry label at S. A heavy right cohort's own earlier positive upcross square may support a gain-weighted transfer, but distinct right origins require a new noncircular comparison. Distinct-slot exact hits remain a separate important sector (at X65536 L6 ell4 raw8293.97050); need actual departure phase and arrival lag restrictions. Heavy skip and full positive moment remain open, as do chi and recipient reuse, other old terminal and immediate/later, low-r/MED etc. No theorem of twin infinitude.
