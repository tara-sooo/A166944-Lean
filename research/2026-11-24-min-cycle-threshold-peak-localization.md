# Directed threshold surplus and scale-dependent peak localization

2026-11-24 JST. Continues 81e22d734cfde276e31d0836e48ebb6356c361b7 in the SAME branch research/min-cycle-forest-2026-11-24, per user's preference to avoid multiplying serial research branches. Elementary paper deductions and exact finite audits; no Lean compilation. Global decay estimate and twin-prime infinitude remain open.

## 1. Two exact weights, including actual elapsed time

Use canonical MIN, odd M in [X,2X), dyadic X divisible by four, B=ceil(sqrt(7X)), start (M+2,2M-2), cutoff floor((7M-1)/4). Use the established LOW barrier with y=7, L=210, or growing y with L<=sqrt B eventually. Partition into an initial LOW-only block and high blocks (a single p>y followed by all succeeding low events before the next high or terminal). For each block i let C_i be its high pre-event horizon, p_i the selected high prime, w_i the exact sum of r(C) at its events, and a_i the sum of actual clock waits of those same events (each wait is the new time minus previous event time or start). Then
    0 < w_i <= p_i+3L/2,
    0 < a_i <= 2w_i <= 2p_i+3L.
Initial block bounds are 3L/2 and 3L respectively. The two totals are R and E, with E<=2R. E counts time until the last actual event, NOT the terminal quiet tail. If every terminal is non-twin, the established clock inequality gives
    E >= 9X^2/16 - 5X/4 - 2B*(X/2).
For either weight b_i=w_i or b_i=a_i, use edges p_i->p_(i+1) of weight b_i; the last block is separate. The previous maximum spanning tree ledger applies unchanged with upper bound 2B+3L for a_i. In particular if S_time is the elapsed-time weighted cycle surplus, then E-S_time=O(X^2/log B) for the stated L choices. Thus liminf S_time/X^2<9/16 on unbounded dyadic X suffices for twin infinitude. This criterion avoids the slack in the inequality E<=2R. It is a new sufficient criterion, not a proof of the required asymptotic bound.

## 2. Exact directed threshold identity

For either weight, retain edges of weight >=u. Let e be their number, v the number of incident (nonisolated) vertices, c the number of weak components on these vertices, a the number of vertices with positive outdegree, and z=v-a the number of incident vertices with zero outdegree. Write D=e-a=sum_p(outdeg(p)-1)_+. Then
    beta=e-v+c = D+c-z.
For each component with at least one zero-outdegree vertex, c-z contributes <=0. For each sinkless component it contributes exactly +1. Hence
    beta <= D + c_sinkless.
Here sink means zero outdegree, not a strongly connected component. Every finite sinkless component contains a directed cycle, but a component containing such a cycle need not be sinkless. The formula handles loops and parallel edges, and does not require connectedness. Also |beta-D|<=k where k is the total number of distinct labels of the original word, including isolated vertices. The same identities hold reversing all arrows with indegree and zero-indegree vertices.

Summation over all thresholds gives an exact alternative surplus D_weight: for each label remove a maximum-weight outgoing edge, if any, and sum the weights of the remaining outgoing edges. It equals sum_u D(u). The total absolute error between the cycle surplus and this outgoing surplus, over the original sources, is <=(X/2)*pi(B)*(2B+3L)=O(X^2/log B). For a threshold tail u>=u0 the same error bound holds; the signed term c-z may substantially improve the finite tail. Therefore the expensive-cycle question can be upper-bounded via repeated expensive departures from the same label; one need not enumerate long graph cycles individually. No claim that this upper bound is always tight or improves on the maximum spanning tree at finite X.

## 3. Scale-dependent nearby repeat lemma

This gives a quantitative restriction on which repeats need be considered. Fix 0<gamma<1 and define the radius for label p by
    T_p = ceil((p+3L/2) B / log^gamma B).
For each source and each high block (including the last), use the total order on its occurrences of label p given by decreasing b_i, breaking ties in favor of the earlier occurrence. Call a block a peak if there is no strictly higher-priority block of that label at a horizon distance <=T_p. Call every other block a nearby repeat. Distinct peaks with the same label have pairwise horizon distance >T_p: otherwise the lower-priority peak has a higher-priority neighbor, contradiction. All pre-event horizons belong to an interval of length O(X). Consequently the number of peaks for each label is <=1+5X/T_p, and their summed weight is
    <= 2(p+3L/2)(1+5X/T_p).
Summing over all p<=B and all original sources bounds total peak cost by
    O(X*pi(B)*(B+L) + X^2*pi(B)*log^gamma B/B)
    = O(X^2/log^(1-gamma) B).
Initial block cost O(XL) is also negligible. This proof needs no assumption on coalescence, clock mixing, or the placement of repeated labels, and handles arbitrary internal histories between the two occurrences.

Let N_b(X;u0) be the sum, over all nearby-repeat blocks with the indicated priority witness, of (b_i-u0+1)_+. The exact threshold tail of ALL high-block weights is N_b plus the peak tail, bounded by the preceding peak cost independently of u0. Since every rejected forest edge corresponds to one high block,
    sum_(u>=u0) sum_M beta_M(u)
       <= N_b(X;u0) + O(X^2/log^(1-gamma) B).
At u0=1, total b cost differs from N_b by o(X^2), so the corresponding liminf criterion is equivalent to the full-weight or elapsed-time criterion. For fixed y=7 this already holds. For growing y with L<=sqrt B, the low threshold range u<=floor(sqrt y) contributes o(X^2) by the high-event count O(X^2/y). Hence a sufficient condition using time weights is liminf N_a(X;floor(sqrt y)+1)/X^2<9/16, and the analogous R-weight condition uses 9/32.

For large weight b_i, the nearby witness necessarily has a large weight as well; specifically with elapsed weights both endpoint least-factor costs at their high event are >=(b_i-3L)/2. With R weights they are >=b_i-3L/2. These are two rough-neighbor constraints at distinct horizons for the same selected prime p. Their signed horizon difference is a nonzero even multiple of p; if C_j>C_i then C_j-C_i>=p-1 and C_j-C_i+sigma_j-sigma_i>=p-3>0 for p>3. Thus the witness gives
    C_j-C_i = 2m p + sigma_i-sigma_j,  m>=1,
    m <= (T_p+2)/(2p).
In particular when p>>L the multiplier range is O(B/log^gamma B), rather than O(X/p) for unrestricted repeats. For fixed low p this is a substantial reduction in the permitted separation; for top-band p the saving is logarithmic. This does NOT bound the number of source-tagged realizations of these pairs. A crude CRT count of possible pairs followed by arbitrary source multiplicity does not supply the needed decay. A useful next analytic target is an anti-concentration estimate on these two rough, same-label visits, retaining the priority comparison and original cutoffs.

## 4. Exact finite audit

Executed the JavaScript function body in the current runtime on six dyadic windows X=256,1024,4096,16384,65536,262144. Integer arithmetic is exact in the tested range. The 6140 clock comparisons for the two smallest windows were independently checked against the literal parity-GCD oracle. R and event counts match the previous audit. The elapsed total is computed directly as the sum of actual waits. Both weight choices check the maximum spanning forest ledger; each sampled threshold independently constructs its components and verifies beta-D=c-z, beta<=D+c_sinkless, and the layer-cake totals. All peaks are checked for pairwise spacing at the four tested radius factors 2,8,32,B/sqrt(log B), with radius ceil((p+315)*factor), fixed LOW7. The first three are finite diagnostic choices and do not imply the asymptotic peak bound.

    node research/min_cycle_threshold_peak_audit.mjs 256 1024 4096 16384 65536 262144

|X|R|E|R cycle surplus|elapsed cycle surplus|
|--:|--:|--:|--:|--:|
|256|9044|8582|1261|852|
|1024|33536|28100|1598|1352|
|4096|331583|287798|37783|27840|
|16384|2144640|1900790|218826|170712|
|65536|15481975|13809350|1208931|945799|
|262144|107745566|92575566|7366835|5706121|

At X262144 (B1355, 131072 sources, 3946588 events), the R-weight threshold layers:

|u|beta|outgoing D|sinkless components|tail sum beta|
|--:|--:|--:|--:|--:|
|1|425129|388797|36332|7366835|
|8|380467|353178|32468|4446642|
|16|184814|178805|21561|1892808|
|32|33603|42929|7578|384528|
|64|1590|8222|43|147312|
|128|614|1992|0|89679|
|256|177|510|0|53288|
|512|139|235|0|12510|
|1024|0|0|0|0|

Elapsed-weight beta at u=1,32,64,128,256,512,1024 respectively 425129,22653,1208,41,36,23,0. The corresponding elapsed tail sums are 5706121,266105,40983,14846,10228,1903,0. The outgoing upper bound is notably looser at some high thresholds; e.g. R-weight u64 tail D=509856 vs tail beta=147312. This is a diagnostic of the information lost in replacing graph cycles by repeat departures.

At X262144 for R weights the nearby-repeat costs at factors 2,8,32,B/sqrt(log B) are respectively 5193972,8025057,8353465,8353465; elapsed costs 3966554,6224673,6509026,6509026. At this finite scale the asymptotic radius is very large, so it does not meaningfully truncate most observed repeats. The local lemma is an asymptotic reduction, not evidence for a particular decay rate. No uniform bound on N_b has been established.

Script and JSON read back exactly at commit 813776c32371e28c18f544511b4b5e91ef49109f. All files added to the existing serial research branch, no new branch. Main unchanged.
