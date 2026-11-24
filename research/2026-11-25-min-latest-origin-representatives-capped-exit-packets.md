# Latest-origin representatives and capped first-exit packets through a larger barrier

2026-11-25 JST. Continues b860b7a16400317a2d55f5ec7a6241fdeb5c20cd on the SAME research/min-cycle-forest-2026-11-24 branch. Original deterministic forest and source-count deductions using the established per-prime sieve and finite-time potential estimate. Exact finite source replay. No Lean compilation. Neither the LOW potential limit nor the weighted large-packet far-coalescence bound is proved.

## 1. Retain the physical forest and replace majority marks by ordered representatives

Use the canonical MIN source paths with original individual cutoffs and the existing barrier-cell/full-inverse accounting stops. N=X/2, B=ceil(sqrt(7X)), Y the LOW cutoff of that accounting construction, L=2 product_(3<=p<Y prime)p, cell threshold T=ceil(X/log^2Y), inverse projected threshold ceil(B^2/p). Retain only tags reaching an accounting stop. S is their number, and S=N-o(X) on no-twin windows. Their full V(t,C) and A(n,p,C) graph is a non-splitting physical forest, as proved in the preceding note; actual proposed prime-stop A vertices and cell-entry V vertices are terminal. The actual MIN paths, cutoffs and accounting stops are not modified.

Fix an integer representative cap k>=1. At every physical vertex A or V, declare the min(k,m) tags with LARGEST original M among its m tags to be its representatives. Equivalently, use largest initial horizon C0=2M-2. Singleton source injections are included in the order at their first V. This selection is on original source indices, not on physical arrival time or current height.

An exact property is no resurrection: if a tag is representative of a vertex, it was representative of every earlier vertex on its own retained path. Indeed the tags with larger M that accompanied it earlier all persist along the common suffix in the retained forest. Once k of them occur in its group, it can never again be among the top k. This uses non-splitting of retained tags, not the full population with different natural cutoffs. Thus each tag has an initial representative prefix, possibly empty, ending at its first discard or at its terminal vertex. Representative paths may be discarded upon a V merger or an A merger; at a proposed unexecuted prime-stop A there is no executed post-state. None are artificially re-injected or refreshed after discard.

At every V pre-state and A event class, the number of tags executing a representative prefix is <=k, irrespective of how large the underlying physical group has become. In contrast to the previous strict-majority construction, this cap is INDEPENDENT of the width of any origin-color cell. In particular, a tag can remain representative even after it has lost its color majority or reached a group of arbitrarily large mass.

## 2. Apply the small-incidence height estimate to representative prefixes

For each retained tag, test attained h=2t-C along its representative prefix, including the final V landing immediately after an executed event at which it was representative, even if discarded at that landing. At a root h=6. Test an executed event only if its tag is representative at its A vertex; a tag discarded at A does not execute that event in the representative prefix. These are deterministic truncations of real paths, not modified MIN trajectories.

For integer H>6, let B_H be the set of distinct representative tags which attain h>=H in this sense. Let B_p be the set of tags having an executed representative event of label p>2H+2 before any such height hit (including an event that first hits H at its post-state). Here the subscript p labels the whole large-prime exception set, not one particular prime. At such an event h<H, h'>=0, and w<=2r(C), hence
    4r(C)>=p-1-h>p/2.
For fixed projected key (p,C), the pre-height band and w<=2p give O(1+H/p)=O(1) possible clocks n for p>2H+2. Each actual (p,C,n) has at most k representative incidences, even if the whole event class is huge. By the existing uniform S_p^cost=O(X/log^2 p) sieve cost,
    |B_p| <= O(k X sum_(p>2H+2 prime)1/(p log^2 p))
          = O(k X/log^2 H).
This bound is unconditional.

Let S_time be the observation scale of the finite-time averaged clipped correction; use the same Y, 11<=P<=Y, 2P<=S_time, 0<=K<=S_time, and H>=max(12,L,2(K+6)), H<=B as in the low-height first-passage theorem. Define
    eta=P[Pr_phase(D_(Y,2S_time)>K)+K/(S_time+1)]
          +1/log^2 P + sum_(q>=Y prime)(K-q+1)_+/q^2.
The same proof gives
    |B_H| <= O(k X eta).
For clarity, this is an extension to a different population of truncated paths: discard the large-event exceptions above, truncate at the first attained H; each prior V and executed A incidence count is <=k by no resurrection. For all remaining labels p<=2H+2, there are O(H/p) possible physical clocks per projected key, even if the last event hits H and immediately loses representative status at V. Count all possible pre-states in each phase rectangle O(XH/L^2), and use the previous clipped potential leakage for p<P, per-key sieve for p>=P, and initial-to-final potential increase >=H/2. This is exactly the earlier first-passage argument with a bounded *incidence* count, not a small whole-group mass assumption. Since eta>=1/log^2 P and P<=H, the large-event exception is absorbed in the same bound. Thus for Bad=B_H union B_p,
    |Bad| <= O(k X eta).
There is no assumption that the representative tags are uniformly distributed in low phases. The full uniform rectangle is only used as a counting majorant.

This is a new use of the prior height bound for representatives that continue after arbitrary large physical mergers. It does NOT imply that all tags in a group containing a bad representative are bad, or that the total physical mass following that representative is small.

## 3. Coarse origin cells with an independently chosen, larger prime barrier

Choose an additional integer cutoff z>2H+2 and z>=Y, and put
    W=2 product_(3<=p<z prime)p.
Require z<=B and W=B^o(1) in the asymptotic application. Because z>=Y, L divides W: each accounting L-cell is contained in one W-cell. Cells are (cW,(c+1)W] with right-closed convention. Color every root by c=floor((C0-1)/W). Each W-cell contains at most b_W=floor(W/4)+1 original roots. Origin color is never larger than the current cell. All p<z events remain within the current W-cell by the exact barrier. The new W is much LARGER than the small width used for majority marking in the preceding note; we do not require W eta->0. A convenient scale is H=floor(log^(1/4)B), z=ceil(3H+10), W=exp(O(H))=B^o(1), with Y growing sufficiently slowly to meet the previous height requirements. This makes the representative cap k independent of W.

At any executed crossing A from cell c to a later W-cell, let m_e be the number of retained tags in that A whose ORIGIN color is c. If m_e>0, call these tags an exit packet. This is the first departure from their origin cell, by monotone C. The packet is a disjoint set of original tags; no tag belongs to two exit packets, even if it later crosses hundreds of cells. Tags of earlier colors that accompany it are NOT counted in its packet. Since all tags at A have origin color <=c, all local c tags have larger original M than all immigrant tags. Consequently exactly min(k,m_e) of its members are representatives at A. They have been representatives throughout their actual prefixes up to A, no matter how much the full group grew. The crossing label p>=z>2H+2. For each of these representatives, either it already attained H on its prefix or the crossing event satisfies the large-label low-height exception B_p. This holds even if the crossing itself resets the height or the tag is discarded on landing. Therefore the sum of capped exit packet sizes has the exact pathwise bound
    C_exit(k)=sum_(exit packets e) min(k,m_e) <= |Bad|.
In particular
    C_exit(k) <= O(k X eta).
The representative charges are to DISTINCT tags because each is charged only at its first departure. This is the principal new transport bound. It includes large immigrant groups that previously made many journeys, without multiplying their mass by the number of journeys. It bounds capped LOCAL exit mass, not the total mass of all crossings and not the number of earlier-color immigrants.

Consequences:
- total number of nonempty exit packets <=C_exit(k);
- number of packets with m_e>=k <= C_exit(k)/k = O(X eta);
- total original mass in packets of size <=k <= C_exit(k);
- the total number of source tags ever departing their origin cell equals sum_e m_e, which can be much larger than C_exit(k).
No implication that the last quantity is o(X) is asserted. This bound is stronger than simply capping each actual group at its first local saturation, because the top-k tokens stay available to account for later resident departures even after earlier physical or cross-color saturation.

## 4. Terminal color component bound and contraction of the surviving packets

For every terminal physical group v, let m_(v,c) be its count of origin color c. If c is strictly earlier than the terminal physical cell, each tag in that component belonged to an exit packet at its own first departure. All tags of an exit packet have the same deterministic retained suffix (the same physical A event), hence the same terminal physical group. They can never split. Thus the nonresident terminal color components are disjoint unions of exit packets of the corresponding color. Since min(k,sum_i x_i)<=sum_i min(k,x_i),
    sum_(v,c foreign) min(k,m_(v,c)) <= C_exit(k).
In particular all small nonresident terminal color components (size <=k) together contain at most C_exit(k) tags, and the number of nonresident components of size >=k is <=C_exit(k)/k. This holds regardless of the number of incoming colors in a terminal group. Small-packet mass and small-terminal-component mass are distinct quantities; the latter may be smaller.

The total resident terminal mass (origin and physical terminal W-cell coincide) is bounded by
    S_res <= b_W (J_p+J_c),
where J_p is the number of stopped projected prime keys and J_c the number of stopped accounting L-cells. For a projected prime stop the horizon C determines one W-cell; its resident source count across all clock classes is <=b_W. For a stopped L-cell the same holds because L divides W. Do not multiply by number of physical terminal classes. Since J_p<=N/B, J_c=O(log^2Y), W=B^o(1), we have S_res=o(X). Consequently on no-twin windows almost all S=N-o(X) tags have departed their W-cell. This is a separate unconditional consequence of the old stopping counts and the larger barrier.

If the previously unresolved finite-time signed-peak condition supplies eta->0 along a diverging sequence, choose k->infinity sufficiently slowly with k eta->0. Then C_exit(k)=o(X), and under no twins:
    sum_(e:m_e>k) m_e = N-o(X),
    # such packets = O(X eta)=o(X).
The analogous statements hold for the nonresident terminal color components. Thus one can delete the resident terminal tags and all small exit packets at cost o(X) original mass. All remaining leaves can be regarded as large monochrome exit packets, each following one actual shared suffix. Their total number is at most O(X eta). This is a conditional concentration INTO large packets, not an anti-concentration theorem.

For the coarse color variance of the preceding note, all tags of a packet share the same origin color, so the packet has internal variance zero. After deletion of small packets and resident terminal tags, contract each remaining packet's pre-exit tree into a weighted leaf at its first-exit A; if members previously met other colors, simply regard the surviving packet as injected there and retain the actual suffixes of all packets. This yields a weighted non-splitting forest even when injection is into an already existing group. Terminal color counts are unchanged by this contraction. At every subsequent merge the usual weighted centroid variance identity applies with weights m_e; the sum of increments is the coarse terminal color variance. Deleting r tags from the original terminal groups changes their variance by at most r: the variance is the minimum sum of squared distances to a centroid for one-hot vectors e_c/sqrt(2), and adding one vector increases it by at most 1. Thus the contraction preserves the original coarse terminal variance to within o(X) on the conditional deletion event. This does not imply the same result for fine origin colors or the hat kernel at distances smaller than W, since a single coarse packet can have large internal variance for those kernels.

The new bound removes small packets and the need for a cumulative ordinary-immigrant-incidence estimate at this coarse scale. It does NOT bound the remaining sum of weighted merge increments. A large exit packet may contain up to b_W roots, far larger than k. Merger of two large packets can carry substantial variance even though the number of packet leaves is small. Multiplying the packet count by b_W can lose the full saving, since W eta need not be small. The original low-height first-majority-loss inequality used a much smaller W and is not implied to have a vanishing transport term. No contradiction with S=N-o(X) follows from the new concentration alone.

## 5. Exact finite replay

Saved research/min_latest_representative_transport_audit.mjs and research/min_latest_representative_transport_results.json with exact remote readback at c4ba6460a5b108fd968e55303c33d7e07e80b7fe. Reuse the previous actual source path diagnostic stops (Y11,L210,T=max(53,ceil(X/256)), inverse cap numerator max(2,floor(B/4))*B). Replay only retained stop prefixes. X=4096,16384,65536,262144, coarse cutoff z=5,7,11,13,17 (script variable y), W=6,30,210,2310,30030, fixed k=8. H=max(12,floor(sqrt B)) except z17 where H7 deliberately tests z>2H+2. These finite H7 cases do not satisfy the analytic potential hypothesis H>=L; they test only the deterministic bad-representative certificate and conservation, not the limiting height estimate. Most other finite choices have z<=2H+2; ordinary representative exits are explicitly allowed there. At z<Y the terminal resident bound via L dividing W is not tested.

Check at every physical replay vertex that all incoming group members persist, top-k representatives never resurrect, representative count is min(k,m), and all discarded tags plus terminal representatives equal S. For every executed large representative jump before height H check r>p/8. At every W-cell crossing check p>=z and local top-k count exactly min(k,m_e). Every packet member exits its origin exactly once. For z>2H+2 verify every charged representative belongs to the bad union of height-hit and large-event tags. Check that capForeignTerminal<=capExitMass, smallForeignTerminal<=capExitMass, smallExitMass<=capExitMass, and exitMass equals foreign terminal mass. No numerical test of eta, no Lean compilation, no proof of asymptotic convergence.

At X262144, S629, one physical prime-stop group, k8: 3953 replay vertices, 14284 representative incidences, 621 permanent discards and 8 terminal representatives. For W210, 606 source tags depart their origin, in 64 exit packets; capped first-exit mass313, small-packet mass129, large-packet mass477 across23 packets, terminal foreign capped mass168, terminal small foreign color mass24. For W2310, 568 source tags depart, in8 packets; capped mass58, only2 source tags in packets of size<=8, 566 in7 larger packets; foreign terminal capped mass16. All58 charged representatives are height/large-event bad in this sample, even though this diagnostic z13 does not guarantee it by the theorem. For W30030 and H7 at X65536, S9416, 141 tags depart in10 packets, capped mass61; all61 representative charges pass the deterministic large-barrier certificate. There are120 tags in5 larger packets, 21 in smaller packets. Terminal foreign cap29, small foreign mass5. At X262144,W30030 all629 stopped tags are resident; this large coarse cell is not informative about crossing. Finite results illustrate reduction of repeated transport to first exits, not a small asymptotic fraction or an unconditional deficit. In particular the largest sample can have very few packets carrying most of the stopped mass.

## 6. Next target

The genuine new gain is that representative height control is independent of the origin barrier width and survives arbitrary earlier mergers. It supplies a capped source-first-exit estimate, and a conditional reduction to a small number of large weighted packets rather than counting all immigrant incidences. Further work needs an upper bound on the weighted merger of those packets or a bound on large packet formation; the packet count alone does not control mass. The LOW phase coefficient eta is independently unresolved. No new branch, no main edit, no twin-prime proof.
