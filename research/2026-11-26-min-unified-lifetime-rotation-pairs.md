# Lifetime-depth area and high-product rotation bounds for boundary-targeted matches

2026-11-26 JST. Continues [2d1f1cf5e180](https://github.com/tara-sooo/A166944-Lean/blob/2d1f1cf5e180a11eff2628bfd60e2339ac9571ea/research/2026-11-26-min-unified-targeted-recycle-pairs.md), integrating the earlier [rational rotation return lemma](https://github.com/tara-sooo/A166944-Lean/blob/533da8c915345b919e386426d40b5eb961e14024/research/2026-11-26-min-unified-rotation-return.md). Independent original heads checked unchanged: prime-root 1a4005f2f336 and stable-heavy e1ad9e2b434c. New all-mass lifetime/depth charge deletion (including stronger macroscopic lifetime bounds), and completes the thin short-pair support treatment through pq close to B² using rotation instead of the short progression sieve. Exceptional rational ratios permit a nearly B-sized effective mass cap. No bound on all remaining heavy pairs or boundary flux, no twin-prime proof or Lean compilation.

## 1. Setup and exact matched-level stock

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root gain-stopped completed MIN prefixes unchanged; each event selected odd p<=B, gain g=p-1, wait w<=2r<=3g, deficit d=2t-C>=0, initial 6, total gain <H and d<=6+5H. Under finitely many twins all roots reach T eventually. Parent grid P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1). Bad sinks q>=kappa P, r<(q-1)/u, with negative increment D_j and boundary charge weight gamma_j=P n_j/D_j<=cstar. Other sinks gamma_j=0. F is original admissible crossing flux.

Use the exact frozen LIFO source-sink matched level intervals L_ij from the parent. Source event i has positive increment; sink j>i pops levels born at i. Exclude initial stock from matched charge. Each level of a given source is popped at most once; at any intervening recorded state the currently active source intervals occupy disjoint actual deficit levels. The weighted target charge of a subinterval is gamma_j times its length. Per source all target charge <=5cstar(p-1), also <=2cstar w; per sink charge <=cstar(q-1). Put e_ij=C_pre,j-C_post,i, the intervening gain, equal to the sum of completed gains g_k over i<k<j. Adjacent endpoints have e=0. At every intervening event k, every level in L_ij is <=min(d_pre,k,d_post,k), since the level has not yet been popped at either recorded endpoint. Thus for any nonnegative integrable level weight f and any frozen subintervals E_ij of L_ij, finite Fubini gives exactly
    sum_(i<j) gamma_j e_ij integral_(E_ij) f(lambda) d lambda
      = sum_k g_k sum_(i<k<j) gamma_j integral_(E_ij) f(lambda) d lambda
      <= cstar sum_k g_k integral_0^min(d_pre,k,d_post,k) f(lambda) d lambda.   (1)
Use f with suitable cutoffs when singular at zero. This counts actual original tag-event gain, not time or projected pair multiplicity. Overlapping lifetimes at the same level cannot occur on the same tag; the stack makes (1) valid even with arbitrary merges between tags. Sum over original tags after applying the per-tag identity. It is not necessary to assume the different tags' active levels are independent.

## 2. All-mass lifetime-depth payments

First keep only levels >q/ell as in the parent shallow sink mask, so lambda>=1 eventually (since q>=kappa P). For f(lambda)=1/lambda on lambda>=1, (1) gives
    A_log=sum_(tags,i,j) gamma_j e_ij integral_(E_ij) d lambda/lambda
           <=cstar NH log(6+5H)=O(NH u).
Here E_ij can be any subintervals remaining after fixed earlier charge payments; in particular use the parent shallow/disparate masks. Pay all levels with e_ij>=u ell lambda. At each such level 1<=e_ij/(u ell lambda). Thus their total charge <=A_log/(u ell)=O(NT/ell). The remaining levels satisfy lambda>e_ij/(u ell), besides the previous lambda>q/ell. The possible equality cases in these continuous level intervals have measure zero.

A second, stronger absolute cutoff is available: for any positive D,Z, use f=1 on [0,Z] and zero outside. By (1) the total charge of levels <=Z with intervening gain e>=D is
    E(D,Z)<=cstar NH Z/D.                                  (2)
No number-of-source bound or lifetime overlap assumption. Thus for any chosen D, pay levels lambda<=D/ell on e>=D at cost O(NT/ell). One may not sum this same bound over an unbounded number of D without accounting for the sum.

For a fixed A>0, consider only macroscopic lifetimes e>=H/u^A. Split e into dyadic ranges [D,2D), with the smallest D comparable to H/u^A and largest <=H. There are O_A(ell) ranges. In each, pay levels lambda<=e/ell², which are contained in lambda<=2D/ell². By (2), cost O(NT/ell²) per range; total O_A(NT/ell). Hence surviving macroscopic matches obey the stronger lambda>e/ell², not merely e/(u ell). This result holds even if every cohort is huge and even on tags not reaching T. For such a surviving level every recorded state between source exit and sink prestate has d>=lambda, also every intervening occupied true tick, since d increases within waits. A necessary deep-deficit span for macro matches is therefore d>=H/(u^A ell²). This does not bound the charge of matches at much higher levels, which may still be long-lived. The macro proof uses a finite number O_A(ell) of dyadic bands and is not a pointwise claim that lambda<=e/ell² is globally payable across all lifetime scales.

All these payments concern TARGETED level charge, not actual waits or all recycled levels. Sum their union by priority, with the old shallow/disparate and source-tick masks. No path or matching changes.

## 3. Remaining short-pair regime at high products

Retain L=floor(sqrt u), rho=ell, the parent short-gap comparable sector e<=L, p/rho<q<rho p. By the parent disparate all-mass deletion all surviving short pairs are comparable. Define
    R0=B exp(-u^.75).
The parent used two-form upper sieves on spatial CRT progressions for pq<=B^1.8 and B^1.8<pq<=B² exp(-u^.75). We now treat the remaining range pq>B² exp(-u^.75), so p,q>R0. In particular log p,log q=Theta(u), p,q>>L and distinct: if p=q, the congruences p|(C+sigma), q|(C+p-1+e+tau) would force divisibility of a nonzero odd integer of magnitude <=L+3<p. Here signs sigma,tau are determined by eligibility. The source has positive drift, hence r(C)>(p-1)/4. The inherited fixed-p two-form support sieve gives O(X/(p u²)) initial C for these p (no restriction on the final q needed). For each such C,p,e the sink prehorizon A=C+p-1+e is fixed; at most four distinct primes q>R0 divide A±1, since R0³>>X. This permits a spatial count even when the joint CRT progression length is too small for a useful upper sieve.

The actual source and sink exit times v,V have h=V-v satisfying
    0<h<=3e+2(q-1)/u<=3q/u
eventually, using the original bad sink predicate. As before alpha(p,-1)=0, alpha(p,+1)=p+2,
    v=alpha(p,sigma) mod 2p,
    v+h=alpha(q,tau) mod 2q.
The full original time slab at fixed C has length O(H), by the deficit envelope. Since the h window has length <2q, each candidate v determines at most one h and V. In the near-maximal product range the elementary CRT count can have a harmful +1 term, which we replace below. No averaging over unknown physical paths.

## 4. Rational rotation and exceptional ratios with a growing approximation cutoff

Choose K=floor(B/u), A0=ceil(u). This K is much larger than the earlier polylogarithmic cutoff but still K=o(H/p) uniformly for p<=B. By Dirichlet approximation there exist coprime integers a,b with 1<=a<=K and |a p/q-b|<=1/K; if a nonreduced pair is obtained, reduce it. Define exceptional prime pairs to be those having ANY such approximation with a<A0. Otherwise select any approximation, necessarily a>=A0.

For a fixed nonexceptional spatial key, write v=alpha(p,sigma)+2p n, with n in an interval of length O(H/p+1). The sink congruence and the h interval restrict a translated rotation n p/q mod 1 to a circular interval of length at most 3/(2u). In each block of a consecutive n, relative to its start, these points differ from the equally spaced rotation b/a grid by at most 1/K. Thus at most
    a(3/(2u)+2/K)+2
of the block can be accepted, including wraparound. A shorter last block is bounded by a full block. Summing gives
    # (v,V) << (H/p+a)(1/u+1/K+1/a)=O(H/(p u)).             (3)
This is a uniform count of exit-slot pairs, not occupied ticks and not the count of actual matching tags. No additional factor for possible arrivals is needed for the charge cap below.

Exceptional pairs: for fixed p and a<A0, b is positive and <=O(a rho+1), by comparability (p/q>=1/rho>>1/K). Each q lies in [ap/(b+1/K),ap/(b-1/K)]. For q>=R (R=R0 or Q on the extra high-high sector), the sum of reciprocal INTEGERS in this interval is O(1/(bK)+1/R), by relative interval length and one endpoint error. Sum over a,b to get
    sum_(exceptional q>=R) 1/q
       << A0 log(2 A0 rho)/K + rho A0²/R
       = O(u² ell/R),                                      (4)
uniformly in p. The bound includes nonprime integers on the right, so no short-interval prime lower bound is used. The separate spatial CRT gives O(X/(pq)+1)=O(X/(pq)) possible C per p,q,e,signs, since pq<=B²=O(X); no roughness sieve is needed for this exceptional count. Per C at most O(H/p) candidate source exits, each at most one sink exit in the h-window. This exceptional counting with K of order B/u, rather than a power of log B, is responsible for the large new mass cap. It is valid because the block estimate (3) still absorbs K within H/p.

## 5. Summed weighted support and thin charge caps

Group remaining actual short matched charge by pair key (C,p,v,A,q,V). Each original tag contributes at most 5cstar p units, so n_eff=A_pair/(5cstar p) is at most the count of actual contributing tags. Sum candidate keys weighted by p, which is the scale of this per-tag bound.

Nonexceptional general top range: fixed-p C support O(X/(p u²)), O(L+1) offsets, O(1) q per C,p,e, O(H/(p u)) time pairs by (3), then multiply by p. Since
    sum_(R0<p<=B) 1/p = O(u^(-1/4))
by dyadic prime upper bounds over O(u^.75) intervals with log p=Theta(u), get
    S_ord << XH (L+1)/u^(13/4).                             (5)
On its subrange p,q>=Q, use sum_(p>=Q)1/p=O(ell/u) instead, giving
    S_ord,HH << XH (L+1) ell/u^4.                           (6)
These are bounds with multiplicity of distinct candidate pair keys, not merely source horizons.

Exceptional general top range: spatial CRT O(X/(pq)), time count O(H/p), then multiply by p. Sum with (4) and the same reciprocal p bound:
    S_exc << XH (L+1) u^(7/4) ell/R0.                       (7)
On p,q>=Q, use R=Q in (4) and the shorter p range:
    S_exc,HH << XH (L+1) u ell²/Q.                          (8)

Pay an entire remaining actual pair charge if its n_eff does not exceed the appropriate cap:
    m_ord = u^(9/4)/[(L+1)ell],
    m_ord,HH = u³/[(L+1)ell²],
    m_exc = R0/[(L+1)u^(11/4)ell²],
    m_exc,HH = Q/[(L+1)u² ell³].
Use the larger of the applicable general and HH caps. Multiplying the respective weighted support by its cap and 5cstar shows each of the four summed payment costs is O(XH/(u ell))=O(NT/ell). Their union is also O(NT/ell). This is a linear charge payment, independent of how many relaxed keys are unrealizable. Frozen charge may be restricted by earlier masks before computing the effective mass, with the same cap budget. No multiplication by the square of cohort mass.

For L=floor(sqrt u), general ordinary cap is Theta(u^(7/4)/ell), high-high ordinary cap Theta(u^(5/2)/ell²). General exceptional cap is B^(1-o(1)) since R0=B exp(-u^.75); high-high exceptional cap is Theta(B/(u^(7/2)ell³)). Both exceptional caps eventually exceed ordinary ones by unbounded factors. The results do not say all exceptional pairs are paid; their actual effective masses could still be larger.

Together with the two earlier product regimes, all possible short-gap products pq<=B² now have a thin-charge estimate. There is NO unhandled short-product interval in this particular support calculation. Surviving heavy short pairs still have >their applicable cap distinct original contributors sharing the source departure, deterministic intervening path and sink departure. The actual level intervals need not all coincide across tags. The proof is a mass cap, not an upper bound on the whole short-pair charge. It covers q bad and p positive drift, not arbitrary pairs of large events.

## 6. Residual criterion

Parent exact F+R_target=P n_all-I, I<=6cstar per tag, gives under finitely many twins F_all+R_target,all>=NT-N(P+6cstar). Previous and new payments, with priority, total o(NT). Therefore the same sufficient condition
    liminf_(dyadic X->infty) (F_rem+R_target,rem)/(NT)<1
now has a smaller residual. The long-life masks control shallow long intervals at every mass; the rotation masks remove thin short pairs including the previously uncovered pq near B² sector. Heavy short pairs, deep longer pairs, and heavy admissible projected boundary flux are still unbounded. Neither the area identity nor the improved short-pair support by itself supplies an independent upper contraction of the total. The raw targeted identity is close to actual gain, so rewriting it without arithmetic control cannot prove infinitude. Original clock and canonical-target sufficient conditions remain separate routes. No external novelty claim or Lean verification. Main and independent source branches unchanged.

## 7. Reproducible finite audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/12c4d008b3d7e42e3f172e5cc1517f844716806f/research/min_unified_lifetime_rotation_audit.mjs), exact content verified on remote readback at 12c4d008b3d7e42e3f172e5cc1517f844716806f. Executed eight runs in available ECMAScript tool runtime, not a separate Node process. Reproduce:
    node research/min_unified_lifetime_rotation_audit.mjs 256 1024 4096 16384 65536
Derived from parent targeted recycle audit, same original trajectories and finite P,T,rho,cstar. Diagnostic lifetime ratio Rlife=3 normal or 2 focus; macro e>=floor(B/4), level<=e/1.5 after lifetime trim; absolute-area cutoff Z=floor(B/8) (minimum 1). These finite substitutes are not analytic e>=H/u^A, nor do they numerically test the macro dyadic summation. Checks exact harmonic and truncated ordinary lifetime area by independent difference-array accumulation on every intervening event, active stock ceiling from both deficit endpoints, per-tag long charge <=harmonic area/Rlife, and parent LIFO matching, source domination, targeted flux identity. The area is computed on layers remaining after shallow/disparate masks, before lifetime and macro deletions. Rotation finite K=12,A0=3, product pq>=B²/8, p>L+3, h<=floor(q/2), comparable labels; this is a deliberately different diagnostic high-product cutoff, not the asymptotic R0 range. Checks actual CRT hits, exact integer Dirichlet approximations and exceptional intervals, rotation block counts versus independent direct time-slab census, actual h membership, effective pair mass. Normal cap B/p and focus .02B/p are diagnostic, not the four analytic caps. The finite diagnostic counts only observed qualifying matched keys, not an exhaustive relaxed arithmetic support census. Does not apply the earlier two short-product masks cumulatively, so new finite residual should not be directly compared as a monotone extension of the prior audit. No literal gcd oracle repeated; no analytic prime sieve constants tested.

| X/mode | targeted charge | lifetime paid | macro paid | high-product pair charge | pair paid | residual after diagnostic masks |
|---:|---:|---:|---:|---:|---:|---:|
|256|0|0|0|0|0|0|
|1024|213|1.842105|13.263158|0|0|118.054581|
|4096|3202.808969|3.342857|52.006950|71.920635|71.920635|1089.351067|
|16384|35569.539464|208.619487|1052.579482|1909.632484|1909.632484|17879.063053|
|65536|202728.986045|947.885775|6379.539423|2381.401046|2381.401046|105047.240365|
|4096 focus|466.563707|0|11.413127|0|0|129.514046|
|16384 focus|3727.934388|4.452055|6.164384|145.283019|0|1216.261780|
|65536 focus|54700.323711|732.988656|263.118479|1001.222209|514.534709|20266.661413|

Largest normal: 5709 roots,140255 completed events, none reach T, 55557 exact matched layer intervals,261018 persistence checks. 3084 lifetime-integral matches and 140255 active stock checks. Harmonic area53997.326653 vs ceiling43170653.488604; truncated ordinary area584250.014363 vs ceiling1037893920. 770 macro checks. Five qualifying spatial keys, three exceptional and two ordinary, 77 rotation blocks and 43 relaxed exits in their finite slabs;12 actual matched incidences, all five pair keys thin at finite cap. Exceptional charge1487.030557, ordinary894.370489, both diagnostic labels>=B/3 charge1129.523220. Largest focus: 2886 full reaches,75256 events,762 integral matches,59 macro checks, three qualifying spatial keys (two exceptional, one ordinary),12 rotation blocks,10 relaxed exits, four actual matched incidences, two thin and one heavy pair. In normal and focus some support tests are vacuous at smaller scales. Observed harmonic area upper bounds are deliberately coarse, not evidence of an asymptotic contraction. Remaining values in table are targeted charge only, not F+target; no inference of the conjectural sufficient inequality.
