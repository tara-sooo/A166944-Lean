# Dyadic cut transfer, cutoff-tagged suffix replay and near-origin energy

2026-11-24 JST. Continues 7b90eee85b10dfc3f816f085da865fe50bf08e6d (dyadic cut roadmap). New unconditional partial energy estimate, exact transfer formula, finite audit. The central energy estimate and twin-prime conjecture remain open. No new Lean compilation.

## 1. Unconditional near-origin energy bound, across ALL levels

Retain full canonical actual trajectories, original odd M in [X,2X), C0(M)=2M-2, B=ceil(sqrt(7X)), N=X/2, original cutoff K(M), pre-event horizon sets V_M, r(C) the least eligible prime or zero, W(C), R=sum r(C)W(C)=O(X^2), E=sum r(C)W(C)^2. The parent Cauchy/sieve argument uses E=O(X^2 B log B) on unbounded dyadic windows.

For distinct sources M<M', charge their common pre-event C as near-origin if 0<=C-C0(M')<=T. At fixed C there are at most floor(T/4)+1 such later sources, since the original horizons are spaced by 4. For each later source there are at most W(C) earlier sources at C. Thus their UNORDERED weighted contribution, across the complete binary source tree (each pair has exactly one lowest common ancestor), is at most
    (floor(T/4)+1) R.
The ordered energy term is at most twice this. In particular it is O(T X^2), regardless of coalescence, times or repeated prime labels.

Define W_late(C)=#{M:C in V_M, C-C0(M)>T} and E_late=sum_C r(C)W_late(C)^2. Monotonicity in the ordered initial horizons shows that a distinct pair is not near-origin if and only if BOTH origins are more than T below C. Thus
    E <= E_late + (2 floor(T/4)+3) R.
The extra R covers the removed diagonal. Choosing T=floor(B log B) yields E<=E_late+O(X^2 B log B). This is a genuine unconditional removal from the original energy target. It does not bound E_late. One may also use the parent's small-block and near-cut bounds; these are overlapping removable classes, not disjoint quantities to subtract twice. In particular for remaining far-cut pairs, common horizons in (J,J+B] are already excluded because their right root starts above J+B.

## 2. Exact boundary-entry transfer with ORIGINAL cutoff tags

Use binary source blocks I of k consecutive original indices i=0,...,N-1, M=X+2i+1, k a power of 2. The cut is J=2X+4(mid-1), where mid is the first right index. Retain only sources whose root horizons are more than B from J, on each side. Let H_far(I)=sum_C r(C) W_Lfar(C) W_Rfar(C). Its late part additionally requires C-C0(M_right)>T. The earlier horizon is then also more than T from its origin.

Every retained left source contributing to H_far has a unique first crossing J: pre-horizon D<=J, label p, post-horizon D+p-1>J, time t. Its entry key e=(p,D,t) in block I is tagged with the source's original K(M). The arithmetic bound from the parent gives at most one possible D for fixed p and divisibility side; it is important to distinguish a projected key (p,D) from the physical entry (t,D+p-1).

Let A_e be the original left-source set entering through e, K_e=max_(M in A_e) K(M), and a_e(v)=#{M in A_e:K(M)>=v}. Replay one canonical suffix from the post-entry state with cutoff K_e, and write (C,v(C)) for each pre-event horizon and its NEXT selection time. Every source in A_e follows that suffix until its own cutoff; it contributes at C exactly when its cutoff is >=v(C). This includes correct treatment of crossing directly into a terminal. With W_Rfar,late(C) counting retained right sources with original cutoffs and C-C0(M)>T, there is an exact identity
    H_far,late(I) = sum_(entry e) sum_((C,v(C)) in replay_e) r(C) a_e(v(C)) W_Rfar,late(C).
The same identity with W_Rfar gives H_far(I). No independence, no new incoming mass estimate. It permits factoring the left tagged populations into one replay per entry plus an exact monotone cutoff survival count. It retains all source weights; counting entries alone is not enough.

For example a_e(v) is bounded above by the number of left-root indices in the block satisfying K(M)>=v and C0(M)<J-B. This simple cutoff restriction gives no uniform control of incoming mass or of the overlap with late right occupation. The main open analytic target remains the coarse-level sum of the last display, on unbounded dyadic windows, of order O(X^2 B) per level (or total O(X^2 B log B)). This is the original target with previously bounded terms removed, not an additional theorem. A further practical route is to count original-root masses in exact reverse intervals of the entry states, and bound their product with the late right-occupation measure; the needed product estimate is still missing.

## 3. Finite audit, including independent suffix replay from each entry

Code research/min_dyadic_cut_audit.cpp. Compile and run:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_dyadic_cut_audit.cpp -o /tmp/min_dyadic_cut_audit
    /tmp/min_dyadic_cut_audit 256 1024 4096 16384 65536 262144 1048576
All seven windows actually run. Tested Git blob c8989d489a96f07fffeb388d53e6e2587b708c32, exact remote readback at 4d40f470b42fd83a9fa92b82e94fac966d5783d3. The code replays all original full trajectories, records each pre-event/terminal vertex, and groups by C and source block. It computes H and H_far (both roots farther than B from J) at all levels. At k>B it groups each first crossing by (block,p,D,t), includes crossings into terminal states, and replays each entry once with maximum cutoff, verifying BOTH exact suffix identities against direct occupation counts. In this diagnostic T=B, not B log B. All assertions pass, including E=R+2 sum H and sum H_far,near-origin<= (floor(B/4)+1)R. Energy totals agree with the earlier distance-band audit.

| X | B | E including diagonal | sum H_far over ALL levels | near-origin part of sum H_far (T=B) |
|--:|--:|--:|--:|--:|
|256|43|161478|5385|4349|
|1024|85|601806|9489|8439|
|4096|170|12181333|131499|101137|
|16384|339|129745176|3273026|2599040|
|65536|678|1404923195|12505984|10109564|
|262144|1355|14915941604|169796381|141435387|
|1048576|2710|133827345196|983960851|783122463|

At X=1048576, N=524288, 19219036 events, R=730547400. All-level far-cut unordered weight 983960851, near-origin part 783122463 (79.5888%), remainder 200838388. Far-cut does NOT mean |M-M'|>B, though it excludes roots near the separating cut. The coarse levels k>B have far-cut weight 706298737, near-origin part 535129474 (75.7653%), remainder 171169263. At those levels there are 25846 crossing source-level incidences, 466 distinct physical-tagged entry keys summed across blocks and levels, 132 keys contributing a positive far-cut weight, and 18153 suffix-event replay checks. These are not unique global root or physical-state counts.

| k | crossing sources | physical-tagged entries | max entry mass | H_far | late remainder (T=B) |
|--:|--:|--:|--:|--:|--:|
|4096|11519|225|513|378827153|118628537|
|8192|7039|125|397|114632736|26247058|
|16384|4406|63|905|174071966|22196312|
|32768|1639|31|609|5400073|0|
|65536|720|14|171|21259832|3156736|
|131072|485|5|431|12106158|940620|
|262144|9|1|9|819|0|
|524288|29|2|27|0|0|

The prior full distance-band audit at this same window measured maximum total horizon gain 16586, less than floor(B log B)=21421. Therefore E_late for the stronger T=floor(B log B) is zero there, simply because no source travels far enough. This is not an asymptotic estimate and does not test the difficult long-trajectory regime. The T=B audit was chosen to expose nonzero late overlap. No proof that future gains remain below the larger threshold is obtained.

Main untouched. Next work should target the source-weighted incoming mass times late right overlap from section 2, rather than merely counting more classes of short cycles. 
