# Two-sided high-clock history cores and bandwise shared-hit chain energy

2026-11-25 JST. Continues f8d81fc374e78c1c2587de34890678957f0924f6 on research/min-prime-root-repeat-energy-2026-11-25. Uses the improved least-factor support and local two-form sieve to impose simultaneous actual predecessor AND successor multiplicity conditions on high incidences. Also gives an injective energy transfer ledger and a bandwise chain-birth decomposition of the remaining energy. No bound for the full residual energy or medium moment, no Lean compilation or novelty assertion.

## 1. Input and two-sided gain span

Retain the established gain prefix T=floor(X/u^(1/4)), u=log B, l=log u, B=ceil(sqrt(7X)), N=Theta(X/u) original prime roots M. Every original full path has gain G_M<T+B, actual selected p and minimum eligible odd prime r(C)<=p, wait<=2r(C), r(C)<=1.5(p-1). Fix ANY high-incidence subset I of the original paths, with p>=Q=ceil(B/u) and r(C)>p/sqrt(log p). The relative-cheap deletion in a5e1119 justifies restricting to this set at negligible LINEAR cost. I may already include all previous root and event deletions, but freeze I before the history operation below (and preferably before the final source-cell thinning). Let W_I(C) denote its tag mass, E_I=sum_C r(C)W_I(C)^2. All history indices are in each source's frozen I list, not in the full MIN event list; no dynamics are rerun.

Use
    k=max(1,floor(u^(1/8))), G=floor(B sqrt(u)),
    m=floor(B u^(3/2)), tau=floor(u^3).
For each source order its I hits by strictly increasing horizon C_0,...,C_{n-1}. Delete the first and last k hits (union if overlapping). Their total clock cost is at most 2kNB=o(NT). For an interior index i delete if C_{i+k}-C_{i-k}>G. The sum of these spans over all interior indices is at most 2k G_M: expand each span into consecutive gaps in the frozen list, each gap is counted at most 2k times. Thus the clock cost of this long-span deletion is at most
    B/G * 2k sum_M G_M = O(NT/u^(3/8))=o(NT).
After both, each surviving central hit has all 2k frozen neighbors C_{i+j}, j=-k,...,-1,1,...,k, within one interval of length G around it (indeed the entire block spans <=G). The neighbors need not be consecutive full MIN events, nor survive later accounting deletions. There is no assertion about individual selected labels repeating.

## 2. Global ancestry mass for every frozen neighbor

All positive clocks in I have r>=Q/sqrt(u)>=B/u^(3/2). By the least-factor bucket bound of f8d81fc, the support H of such horizons has cardinality O(X(1+l)/u³). This counts only positive r; twin horizons with r=0 are excluded. Define small input horizons D by W_I(D)<=m. Their total incidence count is <=m |H|. For a fixed signed lag j, each I hit at D has at most one central hit whose jth neighbor is this hit; this is just uniqueness of the index i-j in its frozen list. The same is true for lag zero. Consequently delete every central hit whose own horizon or any of its 2k neighbors has W_I<=m at cost at most
    B (2k+1) m |H|
      = O(NT (1+l)/u^(1/8))=o(NT).
This holds before or after the first deletion by the same upper bound. In particular all frozen neighbors of a residual incidence now have global INPUT multiplicity >B u^1.5 up to floors. The assertion is not a recursive claim of large FINAL multiplicity at the neighbors. Such a recursive deletion could cascade along arbitrarily long source lists; it is not made here.

## 3. Local support and simultaneous history core

For a central C after the preceding gates and a signed lag j define its group
    A_j(C,D)={M: the surviving central tag M at C has frozen jth neighbor D}.
At a fixed j these groups partition the central tags. The possible D all lie in [C-G,C+G], and their r>=B/u^1.5 implies both D±1 avoid all odd primes <=z=floor(B^(1/16)) eventually. The self-contained Selberg upper bound from 32d4185 applies to forms 2n-1,2n+1 on the local n interval. It gives
    # possible D << G/(log z)^2 + z^6 << G/u².
The error z^6<=B^(.375) is negligible here. This bound is uniform in C and in the frozen subset. It is a local ROUGH-horizon count, not the global cubic-log factor bucket bound on a short interval. In particular one cannot simply assume local cubic-log density.

At each C repeatedly delete every nonempty group of size <=tau, for ANY of the 2k signed lags, until none remain. Parallel rounds or a deterministic sequential order both work. Removing a group removes all its remaining tags; it will stay empty. A group can be charged at most once, and has at most tau tags at removal. Even if previous removals create more thin groups, the total clock cost at C is bounded by
    r(C) tau * (initial number of possible groups)
      << r(C) tau k G/u².
Use the improved S_*=sum_C r(C)=O(XB/u³) of f8d81fc. Summing over C gives
    R_peel << tau k G S_*/u²
           = O(X B²/u^(11/8))
           = O(NT/u^(1/8))=o(NT).
No probability assumptions about memberships or independence. This is a finite monotone peeling process at each central horizon, not a new MIN path. Unlike simple single-pass thinning, every remaining tag simultaneously lies in groups of size >tau at EVERY positive and negative lag. For each such tag and each lag it has at least tau other original roots which visit the same central and same neighbor horizon, with that same relative index. These companion roots can differ from lag to lag. Neither common physical time nor agreement of the full 2k+1-word follows.

All the new linear deletion costs sum to O(NT(1+l)/u^(1/8))=o(NT). All are deletions of high tags, so LOW attachment O(LNT/Q)=o(NT) as before; none is used as a selected-weight propagation seed.

### Compatibility with the strengthened multiscale source-cell conditions

If the final cell conditions of f8d81fc are also desired, freeze I before these final steps. Instead of separately doing history peeling and nested cell thinning, use a JOINT peel at each C: the group families are the 2k frozen-lag partitions AND each of the source-cell partitions d_a=B2^a<=B u^(9/4), m_a=floor(2^a u^(7/4)). A small group in any partition is deleted. Each initial group still disappears at most once. For each cell scale the number of possible cells <=ceil(T/(2d_a))+2, hence the total charge for that family is at most m_a(ceil(T/(2d_a))+2)S_*=O(NT/u^.25), the same old bound. Sum over O(1+l) scales. This preserves EVERY occupied cell's thickness and every frozen-lag group's thickness at the end, even if interleaved deletion would have broken a single-pass result. The previous effective dispersion gates with K_a=floor(u^2.5/2^a) are then applied to entire horizons; so is the global FINAL mass gate W<=m, at cost <=mS_*=O(NT/u^.25). Whole-horizon removal cannot change the membership of any surviving central C's groups. Thus all conditions coexist at o(NT) cost. The neighbors' large INPUT masses remain on the frozen I, not necessarily on this final set. The auditor isolates history peeling; the joint cell/history process is a paper extension by the same one-charge ledger, not a cumulative finite audit.

## 4. Injective lag energy transfer

Let J be any subset of I which has the signed lag j defined, e.g. the final core, and let w_j(C,D) count its actual central tags with jth frozen neighbor D. Then
    sum_C sum_D r(D) w_j(C,D)^2 <= E_I.                (1)
For fixed D and j, each I tag there has at most one central C at the required offset, so the groups indexed by C are disjoint subsets of the I tags at D. Sum of their squared sizes <=W_I(D)^2. The same proof with w(w-1) gives the ordered off-diagonal version bounded by E_I-R_I. This transfers squared group occupation at current horizons to energy at the corresponding historical or future horizon without counting any pair twice for a fixed lag. The weight on the left is r(D), not r(C); replacing by r(C) costs at most B/(Q/sqrt u)=O(u^1.5). Inequality (1) is not a contraction relative to E_J and does not itself prove E_I small. Applying it for many j costs a factor 2k if summed without additional information.

For reference, define the shared-neighbor energy at the central horizons for a fixed j as sum_C r(C) sum_D w_j(C,D)^2. The cross-group energy plus this equals E_J exactly; a shared preceding neighbor implies an earlier projected contact, but not necessarily an earlier common physical state. The earlier first-contact budget remains applicable to all current tags.

## 5. A separate chain-birth criterion with constant clock-ratio loss

For ANY retained high incidence set J, split its per-root ordered lists into dyadic bands of the ACTUAL clock r, not selected p. A band b consists of 2^b<=r<2^(b+1). Because r is a function of C, all tags at a common C have the same band; the total energy is exactly the sum of band energies. For each unordered distinct root pair in a band, call a shared hit a chain birth if either root has no preceding hit in that band or their immediately preceding band hits have different horizons. Otherwise the two previous hits coincide and the shared hit extends the previous chain. This definition is on the frozen J band lists; even if the original projected paths met earlier, a new band-chain birth can occur later. There is a unique previous shared hit whenever both immediately previous hits coincide, so maximal common consecutive-band-hit chains are disjoint and uniquely defined. Each has ages 1,2,..., length of that chain.

Let E_birth be the sum of ORDERED off-diagonal weights 2r(C) over all births in all bands, and E_old(k) the sum over shared hits of chain age>k. The diagonal is R_J=O(NT). The first at most k hits of each chain all have clocks <2 times the birth clock because they lie in the same dyadic band. Consequently
    E_J <= R_J + 2k E_birth + E_old(k).                (2)
Also E_J=R_J+E_young(k)+E_old(k) exactly, where young means age<=k. Without the bands the coefficient could be O(k u^1.5), so the dyadic grouping removes that large clock-ratio loss. An old pair necessarily shares at least k immediately preceding hits in BOTH roots' lists within the band, but can have different MIN labels, different intervening events or different times. This is a new alternative residual target, not a bound on the actual birth mass.

For the final history/core/cell set one may use its own band lists in (2); this does not redefine the frozen I lags in sections 1-4. A sufficient replacement for the high target E_J=o(T² B u) is
    E_birth=o(T² B u/k), E_old(k)=o(T² B u)
on the same unbounded windows as the medium condition. It is also possible to subtract previously proved whole-pair classes first: restrict both chain sums to eligible root pairs (the exclusions depend on the pair), so their complete chains and the same charge proof remain valid. This avoids double counting the pair exclusions. Neither estimate is established. The band chain reduction in particular isolates repeated close-in-list projected overlap, rather than assuming all large energy comes from first physical mergers.

## 6. Integration and limits

Use the old root/linear marks, including relative-cheap, then freeze I. Add sections 1-3, jointly with source cells if desired, then whole-horizon dispersion and mass floors. On the final set the earlier first-contact/anchor pair estimates remain valid on any subset. The surviving ensemble still has N-o(N) roots; under no twin terminal the original prefix cost is >=(N-o(N))(T-6)/4. The preceding LOW/medium argument and improved support bound prove the joint sufficient conditions
    Z_m=O(N B u³), E_newbad=o(T² B u),
where E_newbad is the off-diagonal energy on the final core of pairs not already excluded. Alternatively use (2) for those pairs. All marked LINEAR costs are o(NT); no claim that the history-core operation discards only negligible quadratic energy. We have not bounded residual thick group occupations, chain births or long common chains, and have not established a new r-indexed medium moment criterion (the medium condition remains on selected labels). This turn's actual advance is high-history pruning and the exact transfer/decomposition, not a bound on the full moments.

## 7. Reproducible finite checks

Standalone ECMAScript research/min_prime_root_high_history_audit.mjs, final exact remote readback at 397c04d7c34662865e831eee4c33e98a567c2845, blob f8888f4b58f8ea1f97e34086ae8085d189a738f1. Run:
    node research/min_prime_root_high_history_audit.mjs 256 1024 4096 16384 65536 262144
Executed its audit function in the available ECMAScript runtime, not a separate Node process. Five modes x six windows, all 30 final runs passed. Exact SPF original MIN, literal parity-GCD comparator in smallest two windows, all original root/cutoff or gain-crossing tests, full positive-clock support and exact small-prime rough interval counts, signed span sum and global-neighbor mass charge, peeling group-once ledger and actual cascade removals, exact transfer for every lag independently recomputed by reversing the frozen index map, energy and linear partition. Independent pair sweep checks chains on unbanded input, then on both input and final band lists, birth/young/old exact energy and 2k band bound. The finite audit uses a coarse exact small-prime rough count (q<=min(17,ceil(rmin)-1)), not an empirical estimate of the analytic local sieve. Integer energy values are exact at tested sizes. It does not apply the accumulated previous marks, joint cell/history peeling, or check asymptotic constants.

Analytic mode T=X/u^.25,Q=B/u, relative r>p/sqrt(log p), k=floor(u^.125) with min1, G=B sqrt u, m=floor(Bu^1.5), tau=floor(u³). At tested sizes k=1 and the global mass gate deletes all remaining hits. Diagnostic short T=B, wide and one T=4B, Q=7, r>p/2, k=2 (one k=1), G=B,m=4,tau=2. High diagnostic T=4B,Q=ceil(B/8) min5,k=2,G=B,m=2,tau=1. These exercise nonempty cores and actual cascade, not the limiting deletion savings.

| X | wide input high tags | wide final core tags | final horizons | additional cascade-deleted tags |
|--:|--:|--:|--:|--:|
|256|140|0|0|0|
|1024|348|0|0|0|
|4096|2468|523|72|2|
|16384|11319|3952|379|2|
|65536|49712|21088|1783|15|
|262144|224748|114594|8109|42|

At X262144, B1355,N20390, T=4B=5420, wide full R16602377, events612685; relative-expensive input p>=7 tags224748, R_I14658404, E_I311130640. End deletion 67237 tags clock4215039; long span3141 tags clock619525; input mass gate37570 tags clock2361658; simultaneous peel2206 tags clock128760, of which42 tags clock802 are in rounds after the first. Initial candidate group keys39722, removed groups3055, min final group3 max91. Final 114594 tags, R_J7333422, E_J173466110, 8109 horizons. Signed lag order -1,+1,-2,+2 weighted transfer 162766448/157450096/161337090/161229076, all below E_I; 458376 exact final lag membership checks. Current-weight internal group energies 156611518/161717114/144066336/155795038. Original unbanded pair chains max length72; band input max23; final band max22. Final band energy exact partition diagonal7333422, birth117041084 (contained in young), young147505302, old18627386 (k=2), total173466110. Young remains dominant, so the band criterion does not numerically dispose of the main obstruction.

Short mode largest: final63536 tags/6837 horizons, E36812858, 41 cascade-deleted tags; final band young31467098, old2031138. High diagnostic largest: final44 tags at3 horizons, E170640, min group4; no old pairs in final band lists. Analytic largest input23150 tags E218152748, no final core; this is a vacuous finite test of the asymptotic thresholds. No limiting inference. Main and other branches unchanged.

## 8. Next target

Investigate arithmetic control of band-chain births (two distinct immediately preceding band horizons or an absent predecessor) and the formation of large shared predecessor groups, particularly those surviving joint source-cell and history peeling. The local rough support and transfer identity give precise group capacities and budgets; the outstanding need is a bound stronger than merely E_I on the transported energy, or an independent estimate of the birth term. Medium moment remains open. 
