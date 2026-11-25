# Concurrent occupation graph and actual-clock transfer of medium asynchronous costs

2026-11-25 JST. Continuation of c9054d2bcd1be3e163cf6791ec5d972db672cf13 on research/min-prime-root-repeat-energy-2026-11-25. New actual-clock charge bound for asynchronous repeat pairs whose simultaneous waiting states belong to a sparse occupation relation for a sufficient fraction of their repeat segment. Uses a depth-two time-axis union cover and arithmetic degree bounds for common-time waiting horizons. This gives an absolute o(NT) exclusion for a class of overlapping pairs, not a bound on all remaining overlapping pairs. No Lean compilation.

## 1. Inherited setup and endpoint transfer

Use dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u) prime starts, Q=ceil(B/u). Original MIN gain-stopped paths, full frozen sparse medium list y<p<Q, actual attached LOW blocks and gap-adaptive phase/source cells of 8fd0a10 remain unchanged. Total actual completed time W_all<=3NH and exact 2W_M=G_M+Delta_end-6, Delta=2t-C>=0. The sufficient actual target W_all=o(NT) from c9054d2 is retained. The old proxy cost a_M(E)=r+attached LOW proxy and new actual b_M(E)<=2a_M(E) are distinct. All inherited paid classes transfer by this domination.

Every full long quota edge (M,r,C,E) of gain h=E-C>D_r allocates b_M(E)/k_P to its last k_P predecessor choices (P dyadic band of least factor r). The edge's extended interval ends at F, after actual E selection and its attached LOW block. The actual b_M(E)=t_M(F)-t_M(E). Partner charges use the existing normalized successor-group or small-pool rule. No change to partner choices. All pairs belong to the same fixed finest original source cell (width d from 8fd0a10); phase cells depend on keys, not on the current clock time.

Let m_g=u^(19/4)/ell^4. From the gap-phase mass lower bound of 8fd0a10,
    m_{P,S}/((1+L/P) max(K_P,U)) >> m_g (Q/P)^(1/8).
For a fixed directed pair (M,M') and later hit E, there are at most k_P original quota predecessor choices of M across all gap bands and cells. For each unpaid charge its full original partner pool has denominator >=m_{P,S}/(2 max(K_P,U)). Therefore the total assigned ACTUAL cost at that E for this directed pair, even for an arbitrary subset of retained edges, is
    <= sup_S 2 max(K_P,U) b_M(E)/m_{P,S}
    << b_M(E)/m_g * (P/Q)^(1/8)
    <= C0 b_M(E)/m_g.                                (1)
Here C0 is an absolute constant; it does not depend on the directed pair or E. This is actual-relative (not just a bound by r/m_g). The numerator is the focal's own b_M(E), so no comparability assumption between the two actual costs. The corresponding earlier-endpoint bound need not be relative to that earlier actual cost and is not used here.

Retain the previous fast-focal exclusion of c9054d2 with rho=u^-1/64 and all earlier paid classes, including near-origin and close successor times. In particular upper-band P>=Q/u^1/24 disjoint pairs are paid and any upper-band residual far pair has intersection/max(duration)>=1-O(rho). The new proof also works for any overlapping lower-band far pair. The present paper does not estimate lower-band disjoint pairs.

## 2. Concurrent waiting states

Use integer clock times j (or half-open unit intervals [j,j+1)). For each root M and each time j during a completed waiting interval [t_i,t_{i+1}), define its waiting horizon C_M(j)=C_i, outgoing selected prime p_M(j)=p_i, and scheduled exit s_M(j)=t_{i+1}. It is inactive outside the union of its completed waiting intervals. In particular do not extend terminal states indefinitely. At a fixed j and within a fixed source cell, group all original active tags by waiting horizon C. Denote the group size n_j(C). If two active roots have equal waiting horizon C at j, their scheduled exits and selected primes are identical. Indeed both have no eligible tick between their respective arrival time and j, and the earliest eligible tick strictly after j (with least-label tie rule) depends only on j,C; both are completed events. Thus each group is a well-defined waiting-horizon state (C,p,s,n), even if the tags entered C at different physical times. This is not the same as the original selected-vertex mass at (t_i,C).

For any retained asynchronous repeat pair with common projected C<E but different actual physical times at E and different successors, on the common interval
    J=[max(t_M(C),t_M'(C)), min(t_M(E),t_M'(E)))
both roots are active, with waiting horizons in [C,E). They CANNOT have equal waiting horizon at any j in J: they would have identical next actual physical state, both on their paths up to E, and hence identical physical time at E by deterministic continuation. Thus their waiting-horizon difference is nonzero and has magnitude <h=E-C<=A_r<=Amax, where Amax=ceil((Q+1.5L)^2 u^1.5). This also proves the difference cannot change sign in the interior without one or both making a jump: if it changes sign in a single integer clock step, the gain of the overtaking jump exceeds the previous absolute difference. No conclusion that a sign change forces a physical merger.

Clock congruences: at any scheduled tick s, parity fixes the sign sigma(s)=+1 for odd, -1 for even; p divides C+sigma(s), and p divides s-2 for odd s, s for even s. If two waiting groups have the same selected prime p, then
    C'-C + sigma(s')-sigma(s) = 0 mod p.
If also s'=s, their distinct even horizons differ by a nonzero multiple of 2p. All times and horizons considered here are from the original full completed paths, hence O(X).

## 3. Sparse occupation relations

Choose
    eta_occ = u^-1/16,
    z = max(1,floor(m_g/u^.25)),
    m_occ = max(1,floor(m_g/u^.5)),
    D_0 = max(1,floor(u^.25)),
    D_t = max(1,floor(u^.125)),
    R_0 = max(5,ceil(B^.125)),
    D_h = ceil(R_0 u^.125),
    J_0 = max(1,floor(u^.25)).
For the asymptotic estimates floors and min1 are harmless, because m_g is a positive power of u divided by ell^4. These are proof parameters, not a change to MIN.

At a fixed clock time and source cell, let g=(C,p,s,n), g'=(C',p',s',n') be different waiting-horizon groups. Put a directed link g -> g' if ANY of the following tests holds:
A. The total number of other original active tags in the cell within |C''-C|<=Amax is <=z (including other tags at C, excluding the focal itself), and |C'-C|<=Amax.
B. n'<=m_occ and |C'-C|<=D_0.
C. n'<=m_occ, p,p'>=R_0, |C'-C|<=D_h, and |s'-s|<=D_t.
D. n'<=m_occ, p'=p, and |C'-C|<=J_0 p.
The union of tests is taken once, with any priority for counting. These are original full ACTIVE masses, not masses after quota deletions. A thin tag group need not be a small first physical merger. Test A does not use thin groups; B does not restrict labels or ticks; C applies to different as well as equal selected labels, and D need not have near ticks.

For any focal tag in g the number of linked partner TAGS (in the forward direction) is
    <= z + O(m_occ (D_0 + (D_t+1)(1+D_h/R_0) + J_0+1))
    = O(m_g/u^.25).                                (2)
Proof: A contributes <=z by definition. B has at most 2D_0 candidate integer horizons. In C fix s' within D_t of s; because p'>=R_0 and p' divides either s' or s'-2 according to parity, the number of possible distinct p' is O(log X/log R_0)=O(1), by their product dividing a positive O(X) integer. For each such p' the even horizons C' lie in a single residue modulo 2p'; within the interval of length 2D_h there are at most floor(D_h/p')+1 possible horizons. At a given time/horizon all active tags are in just one group, so counting keys overcounts rather than undercounts groups. This gives O((D_t+1)(1+D_h/R_0)) groups. In D the two possible tick parities give at most two progressions of even horizons modulo 2p, so at most 2(J_0+1) groups. All three group tests multiply these counts by m_occ, irrespective of the focal's mass. With the stated powers, each count factor is O(u^.25). No prime distribution assumption about the actual trajectories.

Use the SYMMETRIC good occupation relation G: g->g' OR g'->g. Its maximum individual degree need not obey (2), because a thin group may have many incoming links from a thick group. But its TOTAL ordered tag-pair count at a fixed time and cell is at most twice that of the directed relation. Consequently, if G_{M,M'} is the set of integer times at which the pair is active in the same fixed source cell, with distinct waiting horizons and related by G, then
    sum_{ordered M != M'} |G_{M,M'}|
       << (m_g/u^.25) W_all
       << (m_g/u^.25) NH.                          (3)
This is valid even if G is sampled at every active clock time, not just the repeat endpoints; sum of active counts over cells/times is exactly W_all. It also works for any other symmetric relation obtained by symmetrizing a directed rule whose total time-integrated tag degree satisfies (3).

## 4. Time-axis union cover of directed repeat charges

Take any actual residual far overlapping charge from focal M to partner M' at key (r,C,E), after previous exclusions including fast focal. Write I=[t_M(C),t_M(F)), where F is after E and its attached LOW, and J for its unextended common time interval from section 2. Pay this charge if
    |G_{M,M'} intersect J| >= eta_occ |I|.            (4)
Using J is more restrictive than using I, so it guarantees sufficient good occupation inside I. It can test either orientation of the occupation relation; the actual cost remains focal-specific. All clock intervals are half-open and lengths count integer times; endpoint conventions cause no duplication. No requirement that two roots have the same gain transcript or simultaneous actual selections.

For a FIXED ordered pair collect all accepted extended time intervals I, across all factor/gap bands, with any remaining paid masks. Let U be their union. Each later focal E appears with at most the total charge in (1). Its complete E-plus-LOW time block [t_M(E),t_M(F)) is contained in U. Distinct such E blocks on one original root are disjoint. Thus all accepted pair charges total <=C0 |U|/m_g (even if some accepted intervals end at the same E).

The same depth-two union subcover lemma as in c9054d2 applies on the TIME axis. Choose a subfamily with exact union U and multiplicity <=2 almost everywhere (also at each integer unit interval). By (4), for each chosen interval |I|<=|G intersect I|/eta_occ. Hence
    |U| <= sum chosen |I|
        <= (1/eta_occ) sum chosen |G intersect I|
        <= (2/eta_occ)|G intersect U|.
It follows that the total accepted actual charge for this directed pair is
    <= (2 C0/(m_g eta_occ)) |G_{M,M'}|.              (5)
There is no repeated-segment multiplicity factor, no number-of-band factor and no assumption that the source-specific quota subsets coincide. The occupation relation is fixed on the FULL active root ensemble and depends only on time and current waiting states, not on the chosen repeat key. This key-independence is crucial to summing the cover.

Summing (5) and using (3) proves the absolute new exclusion
    W_occ << NH/(u^.25 eta_occ)
          = O(NT/u^(3/16)) = o(NT).                 (6)
The proof also gives a general transfer lemma for any symmetric concurrent occupation relation with time-integrated ordered pair count o(m_g eta_occ NT). One can separately pay a finite union of such relations, or use their combined count. Neither (5) nor (6) asserts smallness of all actual charges at a given clock time; (4) is the density condition on the entire interval.

## 5. Remaining upper-band concurrent structure

For the upper-band slow far charges from c9054d2, J has length (1-O(rho)) times the full extended focal interval length |I|; indeed unextended elapsed times overlap to fraction 1-O(rho), and extension is o(rho² h), while focal duration >=rho h/2. Every still-unpaid charge after (6) has |G intersect J|<eta_occ |I|, so outside O(eta_occ) fraction of its common elapsed time NONE of the four tests holds in EITHER orientation. At those times:
- two distinct waiting horizons differ by <Amax; each local crowd in the Amax-neighborhood has >z other original active tags;
- if the two horizons are within D_0, both waiting-horizon groups have >m_occ tags;
- if both selected labels >=R_0, horizons within D_h and scheduled ticks within D_t, both groups have >m_occ tags;
- if labels are identical and horizons within J_0 p, both groups have >m_occ tags.
These are conditional thick-group conclusions when the specified geometric/arithmetic alignment holds. They do not establish that most simultaneous times have close horizons or near exit ticks, nor that the two label histories match. In particular pairs with large horizon differences, distinct labels, and separated exit ticks can evade these tests even in thin exact groups. The statement that a pair spends most common time outside G is a restriction on the charge's original segments, not a bound on the total number of physical states. Lower-band overlapping pairs also obey the exact density failure but need not have J close to full I.

Joint OPEN sufficient condition: the inherited slow actual medium residual (large physical formations, lower-band disjoint, lower/upper overlapping after new occupation exclusion) is o(NT), and previous high proxy E_phys,admitbad+E_async,bad=o(T²Bu) on the same unbounded dyadic windows. No proof of the entire residual or twin prime infinitude. Next targets: derive time-integrated bounds for thick active groups via first physical meeting (waiting-state formation vs selected-state formation), and estimate concurrent pairs with widely separated horizons/exit ticks or mismatched labels. In particular one can attempt a transfer to a new physical waiting-state merger forest, but the existence of a common waiting horizon before E is already impossible for the far pairs in this note.

## 6. Reproducible audit

Standalone ECMAScript research/min_prime_root_concurrent_occupation_audit.mjs, exact remote readback at a702b8a0ff2036c5fbc36f9ccba0a283629074c4, blob 5688bc6a5e10a3e990e6dde7f60fc776234ddb7c (initial audit b104b8cff18cd1e5e9f74628ef73e8340c0904b2). Run:
    node research/min_prime_root_concurrent_occupation_audit.mjs 256 1024 4096 16384 65536 262144
All final 42 runs (seven modes x six X) passed by executing the function in the available ECMAScript runtime, not a separate Node process. Starts from c9054d2 actual clock cover, retains exact original SPF/literal comparator, LOW/actual quota, original phase allocation, physical first merger checks and actual fast interval cover. New tests sample clock times in slow overlapping far residuals, build full original active root groups in their fixed source cells, verify common horizon deterministic exit and distinct waiting horizons for async common segments, same-label modular differences, degree bounds for near ticks/near horizons and same-label groups, oriented/symmetric tag-count bounds, crossing implication, exact accepted/kept partition, per-directed-pair endpoint actual-relative transfer (1), same-union depth-two time cover, actual E-block disjoint cost envelope, and global sampled occupation charge inequality. Sampled good time unions are bounded by full good ordered pair count over sampled cells/times, with root-time sum <=W_all. The full asymptotic degree/sum bound follows from sections 3-4, not numeric extrapolation.

Analytic parameters as stated, fixed finite y3,L6 and inherited finite quota/phase guards. Analytic slow far residual empty, so new concurrent tests are vacuous in that mode. New concurrent diagnostic is broad phase width 4H, quota3, deliberately smaller actual fast cutoff rho=.25, occupation crowd8, thin mass4, D_0=6, R_0=5, D_h=30, D_t=2, J_0=2, eta_occ=.25. Existing stress also has one nonempty overlapping residual. These diagnostic values do not satisfy limiting savings (finite floors and degree coefficient can be much larger than 1); the tests concern exact ledgers, not asymptotic performance.

- Stress X262144: one residual overlapping directed charge2, 24 common clock-time checks, 216 group degree checks, no good occupation within that pair; unchanged.
- Concurrent X16384: 102 residual overlapping charges of total30.9393939, 2884 pair-time checks in160 cell-times,1239 degree checks. Good pair incidences102, distinct good directed pair-times96; sampled total symmetric tag-pair-time1764 (oriented1217), root-time3576. No charge met eta_occ.
- Concurrent X65536: 52 overlapping charges total12.8333333. Twenty accepted, cost4.1666667, remaining8.6666667; 1192 pair-time checks in61 cell-times,456 group degree checks, 386 good pair incidences,346 distinct good directed pair-times. Accepted good times340 (40 test B,300 test C). Twenty pair covers, union length1200, good-union time340, distinct endpoint actual time100. Sampled root-time1000, total symmetric/oriented pair-time892. Final actual residual 1771.8062197 vs1775.9728864.
- Concurrent X262144: 152 overlapping charges total44.1111111, 1928 pair-time checks in112 cell-times,1021 degree checks,40 good incidences,30 distinct good pair-times; sampled total symmetric976 (oriented754), root-time3099. Maximum active tags48 and maximum waiting group13 in these snapshots. No charge met eta_occ, final actual residual7979.6908397 unchanged. No positive interior clock-order crossing in these sampled far pairs. This audit does not establish prevalence of new exclusions or asymptotic decay.

No cumulative optional masks, no full growing source ladder or Lean compilation. Main and other branches unchanged by this checkpoint.
