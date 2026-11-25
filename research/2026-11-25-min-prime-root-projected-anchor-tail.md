# Projected high-anchor CRT envelope and prefix-filtered remaining-clock products

2026-11-25 JST. Continuation of 758672d013252a19c0f4798a772fb3dea0cee6a6 on research/min-prime-root-repeat-energy-2026-11-25. Inspired by the parallel physical-anchor paper 73d8d17df179, but counts projected (horizon,label) keys, not physical states, on gain-stopped PRIME roots. Gives an unconditional whole-pair energy exclusion for close last-large anchors with bounded actual weighted group products. Both groups may be much thicker than earlier logarithmic thin caps. Works even after arbitrarily many intervening non-large events and for asynchronous contacts. Does not bound all weighted products or all anchor separations. Paper deduction and finite audit, no Lean compilation or novelty claim.

## 1. Full paths and projected anchors

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, l=log u, T=floor(X/u^(1/4)), N=Theta(X/u) prime roots M in [X,2X), with original gain-stopped MIN prefixes including initial and terminal vertices. All visited horizons lie in [2X-2,7X], each path is strictly increasing in horizon, total gain <T+B, and r(C)<=p<=1.5(p-1) at an actual event.

Fix the high incidence cutoff Q=ceil(B/u). Retained high incidence sets may have all the preceding root, event and multiscale source-cell deletions; in particular the high support is any subset of original p>=Q selections. Let R_M(J)=sum of r(C) over retained high incidences of M with C>=J (or use the full high set as an upper bound). For distinct roots with first common FULL projected horizon C*, their ordered pair energy e=2 sum of r(C) over common retained high incidences satisfies
    e <= 2 min(R_M(C*),R_M'(C*)) <= 3(T+B).
This is the earlier whole-pair budget, valid for all later recontacts, including unequal physical times.

Use V=ceil(B exp(-sqrt(u))) as a common anchor cutoff; eventually V<Q. At a vertex C following at least one completed selection p>=V, define its latest-large projected anchor alpha=(D,p), the post-horizon and label of that selection. The root group A_alpha consists of all ORIGINAL roots which ever select p with post-horizon D in the original prefix. This includes those that later select another large label; it deliberately overcounts actual latest-anchor groups at any C. There is no restriction on the anchor's time or on intervening depth. The post-event condition implies p divides D or D+2.

At the first projected contact of two roots with both anchors defined, the keys must differ. If the same D<C* occurred on both paths it would be an earlier common horizon; if D=C* with same p the two predecessors D-p+1 would be common. Two projected anchor keys do NOT determine unique physical states or unique future paths. Unlike the parallel physical-anchor paper, no uniqueness of C* for a fixed key pair is asserted or needed.

## 2. Counting close projected anchor pairs independently of their actual masses

Let A be an integer distance cutoff, with 2<=A<V-2. Consider unordered pairs of distinct projected keys (D,p),(E,q) with |D-E|<=A, both labels >=V and at least one >=Q. Partition into symmetric distinct p,q>=Q; asymmetric distinct max(p,q)>=Q and min(p,q) in [V,Q); same label p=q>=Q. Let s(U)=sum_{U<=p<=B}1/p over primes. For fixed distinct p,q, a fixed signed offset E-D in [-A,A], and a choice of the two divisibility sides, CRT leaves a single residue class for D modulo pq. The horizon interval has length O(X) and pq<=B^2=Theta(X), so the number of solutions is O(X/(pq)), including the additive one. Counting even D only decreases it. Summing gives
    K_sym(A) << X(A+1)s(Q)^2,
    K_asym(A) << X(A+1)s(Q)s(V).
These are counts of arithmetic key pairs, NOT counts of first contact horizons or source pairs. In particular one does not need to multiply by the number of possible contact horizons after the anchors.

If p=q, distinct keys mean D!=E. Because A<p-2 and each post-horizon is 0 or -2 mod p, the only possibility is |D-E|=2, with opposite divisibility sides. Thus
    K_same(A) << X s(Q).
This count includes asynchronous contacts and does not impose any restriction on their eventual clock lag or later synchronization. The same-label argument is independent of the distinct-prime CRT bound.

Using the elementary upper bound for prime counts and partial summation,
    s(Q)=O((1+l)/u), s(V)=O(u^(-1/2)).
Choose A=floor(B^(1/4)), eventually within [2,V-2]. Then
    K_sym << X A (1+l)^2/u^2,
    K_asym << X A (1+l)/u^(3/2),
    K_same << X (1+l)/u.
No random-source or random-moduli hypothesis; the groups can contain arbitrarily many original tags.

## 3. Prefix-filtered exact tail product for an entire key pair

Order the keys by D<=E, breaking equal-horizon ties by label. All first contacts assigned to this key pair have C*>=E. Define
    A'={M in A_alpha: C_end(M)>=E},
    B'={M' in A_beta: D=E OR M' does not visit D}.
The second condition is new: if D<E and the later-anchor root visits D, then both roots share D before C*, so the pair cannot be assigned to these keys at its first contact. For D=E retain the whole later group. The two groups are disjoint in this filtered product: for D<E every root in A' visited D, while B' excludes that; for D=E distinct incoming labels cannot both belong to the same strictly increasing path at that vertex. The first group must reach at least E, so the end condition is necessary. These filters need only the group memberships and original horizon lists; they do not require calculating all first contacts. They remain valid when some original tags are removed.

Define the coarse aggregate tail bound
    U_ab = 2 min(|B'| sum_{M in A'} R_M(E),
                 |A'| sum_{M' in B'} R_M'(E)).
It is at most 3(T+B)|A'||B'| and bounds the combined ordered energy of all first contacts assigned to this fixed key pair, because each source pair is assigned once and R_M(C*)<=R_M(E). It allows any number of different actual first contact horizons for that key pair.

The earlier near-root exclusion uses d=floor(B u^(3/2)). Such pairs already contribute o(T^2 B) in total. For the remaining far roots a tighter exact product is
    U_ab^far = 2 sum_{M in A', M' in B', |M-M'|>d}
                      min(R_M(E),R_M'(E)).
Then 0<=U_ab^far<=U_ab<=3(T+B)|A'||B'|. The exact all-distance product U_ab^all, obtained by dropping |M-M'|>d, lies between U_ab^far and U_ab. The total assigned far pair energy <=U_ab^far, even when two projected anchors have multiple physical states or future paths. This bound can also be evaluated using source cells: partition A',B' by original M; the exact sum splits into cross-cell sums of min remaining clocks with the same distance test. Same cells of width <=d never contribute. No claim that groups in different cells must first contact. This exact product includes pairs that never contact at all; the overcount is safe.

Write normalized weighted product W_ab=U_ab^far/[3(T+B)]. A raw group size product is an upper bound on W_ab, but the latter can be much smaller when most trajectories have little retained clock after E, or when the later group already visited D, or when roots are near. Use of FULL high tails provides an upper bound independent of previous accounting choices; use of final retained tails can only improve it. This is not a new bound on actual masses of all groups.

## 4. Unconditional whole-pair energy deletion with polynomial-sized group caps

For the three key-pair classes take caps
    c_sym=B u^(5/4)/A,
    c_asym=B u^(3/4)/A,
    c_same=B sqrt(u).
Mark the entire energy of all FAR pairs assigned to a close key pair with W_ab<=its cap. Summing U_ab^far<=3(T+B)c over the arithmetic envelope in section 2 yields
    E_sym << T X B (1+l)^2/u^(3/4),
    E_asym << T X B (1+l)/u^(3/4),
    E_same << T X B (1+l)/sqrt(u).
As T=Theta(X/u^(1/4)), these imply
    E_sym/(T^2 B) = O((1+l)^2/sqrt(u)),
    E_asym/(T^2 B) = O((1+l)/sqrt(u)),
    E_same/(T^2 B) = O((1+l)/u^(1/4)).
All tend to zero. Thus the new union class contributes o(T^2 B) unconditionally, with NO bound on either history's non-LOW depth. This is an energy exclusion on source pairs, not removal of all the participating roots or events from the linear budget.

Since A~B^(1/4), the symmetric cap is of order B^(3/4)u^(5/4), asymmetric B^(3/4)u^(3/4), and same B sqrt(u). In particular BOTH groups can have size of order B^(3/8) (with constant or log slack) in the distinct-label cases, or sqrt(B) in the same-label case. This is far beyond the previous polylogarithmic thin-group bounds, but requires close latest-large anchors. Larger group sizes can also satisfy the weighted cap. For any smaller A>=2 with A<V-2 the same formulas and savings hold; this gives a tradeoff in anchor separation and allowable products. For example if A=floor(B^(1/2)) the distinct caps still allow both masses of order B^(1/4). The audit uses the primary A=B^(1/4) and separate finite diagnostic parameters.

For pairs evading this exclusion yet satisfying the same close-anchor label conditions, the normalized weighted product is strictly larger than its cap; in particular the raw product is larger, and at least one group size exceeds the square root of the cap. Neither both groups individually thick nor universal bounded anchor separation follows from this lemma. No control of deep/deep large product contacts, far anchors, or missing anchors is claimed. The same-label conclusion covers only close shifted anchor keys with the weighted cap, not all asynchronous first contacts.

## 5. Integration with the existing hybrid

Take the surviving original root family after b076ed8 and 758672d, keep all previous clock/selected weight deletions, and apply the nested source-cell thinning and dispersion last. Define the new residual energy E_anchor,bad on far first-contact pairs that evade all earlier pair exclusions and section 4. All the excluded classes have total ordered energy o(T^2 B) on this family (by bounds valid on arbitrary retained subsets). The full retained high energy thus equals E_anchor,bad+o(T^2 B); this does NOT compare the original full energy with the energy after linear-cost root or event pruning. The medium Z_m is unchanged.

The joint OPEN sufficient conditions are still
    Z_m=O(N B log^3 B),
    E_anchor,bad=o(T^2 B)
on the same unbounded dyadic windows, together with the already established linear deletion bounds. As in a5e1119 this would force R_surv=o(NT), contrary to the no-twin gain crossing lower bound (N-o(N))(T-6)/4. The new method removes a class even with both deep and thick ancestry, but does not prove the residual inequalities.

The next quantitative problem is to bound the tail products themselves for dispersed source groups, or show that expensive first-contact pairs must have close anchors. The exact prefix exclusion in section 3 means that simply multiplying two raw group masses can count many roots that already share an earlier horizon. Far and missing anchors remain a separate obstruction. No main or other branch changes.

## 6. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_projected_anchor_tail_audit.mjs, exact remote readback at 63a1dd2fa89c898b57fce82839a6cd7a62e20e39, blob 1420b71f90af450eeb47871e61f51667a13e87a1. Run:
    node research/min_prime_root_projected_anchor_tail_audit.mjs 256 1024 4096 16384 65536 262144
Executed its audit function in the available ECMAScript runtime (not a separate Node executable), four modes x six windows, all 24 passed. Exact SPF MIN, original prime roots and cutoffs; literal parity-GCD comparisons at X256/1024 short1183, four/tight1707 each, gain1719. Enumerates actual original projected anchors and full horizon lists, plus independent arithmetic envelope of candidate keys from divisibility and bounded differences. For every first projected contact checks distinct keys, prefix filter membership, group pair counts, pair and aggregate energy bounds, exact min-tail sum over original root product with and without near-distance filter. Independently computes full high E from horizon multiplicity squares and verifies the disjoint pair ledger. Actual finite sums are safe integers at tested sizes; thresholds in gain mode are floating approximations. The audit isolates this operation on the full high set p>=Qh=ceil(B/log B); it does not reapply all prior root and cell removals. The theorem holds for their intersection. The enumeration verifies inclusion in the finite envelope, not the limiting CRT count or prime sum estimates.

Diagnostic short T=B, four/tight T=4B, Q=ceil(B/4), V=ceil(B/8) (small guards), A=floor(B/8) min2, d=floor(B/64). Here Q denotes the diagnostic anchor threshold, Qh the outgoing high threshold. Caps sym/asym/same 64/32/64 in short/four, 8/4/8 in tight. Gain uses analytic T,Q,V,A,d,caps with small guards. It has all actual source pairs within its near exclusion at largest X, so the far diagnostic there is vacuous. No extrapolation of finite removal rates. At the largest four diagnostic the envelope is much looser than actual groups: 9,565,160 symmetric and 11,098,086 asymmetric candidate key pairs, 136,751 same-label; actual first-contact key pairs 505/917/0. Same-label first contacts are present only in smaller finite samples here (e.g. 1 at X256, 2 at X65536); they contribute zero full-high energy in these examples. The same-label bound is checked where actual labels exceed A+2; the primary asymptotic condition eventually holds. No finite nonzero energy test of that class.

| X | four-mode close first pairs | ordered eligible sym+asym energy before near filter | actual total high E |
|--:|--:|--:|--:|
|256|31|1602|9370|
|1024|80|1334|17543|
|4096|505|25268|304073|
|16384|2008|256860|2448963|
|65536|10018|2684862|23319896|
|262144|41861|19281712|216308331|

At X262144, B1355,N20390,T5420, original events612685, visits633075, R16602377. Among 366974 first projected root pairs, 41861 have eligible close label geometry before any tail cap, 25744 of these contact strictly after both anchors and 22088 have C*-max(D,E)>=6. Max such span368; none exceeds B. Thus the no-depth-restriction theorem is not tested on spans >B in these samples. 1422 actual key groups, 25 prefix-filter reductions, 1422 coarse tail reductions, 44 further exact min reductions, 151 further near-distance reductions. Sum over actual close key groups of the raw uniform gain budget =1,161,573,750; after prefix filtering 1,151,655,150; coarse remaining-clock product 36,492,232; exact all-distance 35,983,888; exact far 35,483,202. These are bounds, not actual pair energies. Largest raw product1040.

Four mode: 303 key pairs whose raw product exceeds its cap nevertheless pass the coarse weighted cap; these cover 28003 first root pairs and actual ordered energy11,977,636 (including near roots). 21,320 eligible first root pairs have both raw group masses >4, actual energy9,389,708. After d-distance filtering the exact weighted cap covers 39,345 far first root pairs with energy19,011,628; 2,015 far close pairs above cap contribute3,906,090. Full high diagonal9,807,301, total E216,308,331, consistent with prior audits. New class may overlap older exclusions; this is not an incremental energy subtraction from the fully accumulated hybrid.

Tight mode at largest X: 872 key pairs with raw product above cap pass coarse weighted cap. Exact far product newly passes one further group beyond exact all-distance cap, covering125,664 actual far pair energy. Far eligible energy8,841,664 over31,258 pairs; above cap14,076,054 over10,102 pairs. At X65536 one additional group passes exact all-distance cap beyond coarse. Short mode at largest X: all 1237 close actual key pairs pass the coarse cap, 17,001 far root pairs contribute4,911,836; 246 groups have a strict prefix filter reduction. These finite diagnostics exercise actual products and tail refinements, not asymptotic saving or the final high residual. No Lean compilation.
