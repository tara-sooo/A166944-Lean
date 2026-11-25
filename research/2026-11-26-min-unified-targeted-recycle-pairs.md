# Boundary-targeted recycled levels and short birth-consumption pair sieve

2026-11-26 JST. Continues [26afc6c22b41](https://github.com/tara-sooo/A166944-Lean/blob/26afc6c22b41bfe11caff113b7ba21cec618d786/research/2026-11-26-min-unified-recycled-flux-certificate.md). Independent heads at preflight unchanged, 1a4005f2f336 and e1ad9e2b434c. New exact boundary-targeted subledger of recycled levels; two all-mass deletions (shallow consumed levels and short gaps between disparate labels); joint spatial and time CRT plus two-form upper sieve for comparable-label short matched pairs. New sufficient inequality dominated by the previous flux condition for identical original masks. No full contraction, twin-prime proof or Lean compilation.

## 1. Target only recycling that pays missing boundary flux

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Original prime-root MIN completed prefixes, first gain crossing T or earlier original stop; each event selected odd p<=B, gain g=p-1, wait 1<=w<=2r<=3g, deficit d=2t-C>=0, initial 6, total gain <H. Under finitely many twins all original tags reach T eventually. Use prior P largest even primorial <=B^.25, kappa=u^.25, cstar=(1+2/kappa)/(1-4/u)=1+o(1). Strict crossings count n_j=# multiples K of P in [C_j,C_j+p_j-1), each crossing uses p_j not dividing P. Admissible flux F=P times crossings on events with p<kappa P or r>=g/u. Bad sinks are completed events q>=kappa P and r<g/u (include zero-crossing events with zero weight). Their negative deficit increment D_j=g_j-2w_j>0 and P n_j<=cstar D_j by the parent proof.

Represent deficit levels on each original tag as a stack: initial interval (0,6] labelled initial stock; at positive event i push levels (d_pre,i,d_post,i] labelled i; at negative event j pop (d_post,j,d_pre,j], always from the highest remaining level. Intersect these popped levels with their existing source intervals. Let L_ij be the resulting interval(s) of length l_ij, where i<j, or i=0 for initial stock. Each source has one contiguous interval initially; its remaining portion shrinks from above. For a fixed pair the intersection is an interval, perhaps empty; each source level is popped at most once. For every lambda in L_ij the recorded deficit is >=lambda from source poststate through sink prestate, and also at every occupied tick between them (deficit rises by 2 between jumps). No fictitious state or independent pair matching. Total l_ij over j>i equals previous recycled b_i. Total l_0j<=6; sum_i l_ij=D_j for a negative sink.

For bad sinks set gamma_j=P n_j/D_j, 0<=gamma_j<=cstar; all other negative sinks have gamma_j=0. Target charge c_ij=gamma_j l_ij for i>=1; I=sum_j gamma_j l_0j<=6cstar on a tag. Thus exactly
    F + R_target = P n_all - I,    R_target=sum_(i>=1,j>i)c_ij.     (1)
In particular R_target<=cstar R_rec, and the charge assigned to any source event i is <=cstar b_i<=2cstar w_i and <=5cstar(p_i-1). At a source with positive charge r>(p_i-1)/4. Since P n_all differs from actual gain G by at most P,
    G-P-6cstar <= F+R_target <=G+P.                              (2)
This new raw objective is close to actual gain, not a bound on actual wait. Its use requires independent arithmetic upper estimates of its two ledgers. In particular the exact identity by itself is not a proof.

Assign every c_ij uniformly to original occupied ticks of its source event if using earlier clock masks. Then the total target tick weight is pointwise <=cstar times previous recycled tick weight b_i/w_i. Keep all memberships and matches frozen before any deletion. Previous thin boundary masks apply to F; old recycled-tick masks apply to this subledger with at most factor cstar in cost. Previous actual-clock masks cost at most 2cstar times original paid wait. Pair payments below are further deletions of these exact charges (not deletion of actual events); use priority to avoid double counting, including partial source-tick payments.

## 2. Shallow levels and recent disparate labels: all-mass payments

Let rho=ell (eventually >2). For every bad sink with label q pay the matched target charge on levels lambda<=q/rho. At most q/rho level length per sink regardless of its number of sources. Sum over original sink events: sum q<=1.5 sum gain<=1.5 NH. Thus
    E_shallow<=cstar sum_(bad sinks) q/rho = O(NT/ell).
In particular a surviving level satisfies lambda>q/rho, hence every recorded/physical state from source poststate to sink prestate is above q/rho. This is NOT the earlier terminal-persistent deep level clipping; it uses large consuming jumps and can apply to arbitrarily many repeated excursions at low levels.

For a source p at prehorizon C and sink q at A define intervening gain e=A-(C+p-1)>=0, even. Excludes BOTH endpoint gains. After shallow payment, pay either of the following two sectors:
    q>=rho p and e<=q/rho;
    p>=rho q and e<=p/rho.
For the first, fix one original sink. All indicated source gain intervals lie in [A-2q/rho,A], since p-1<=q/rho and source posthorizon >=A-q/rho. They are pairwise disjoint on that tag. Their entire positive increments <=5 times their gains, so their matched target charge <=10cstar q/rho. For the second, fix one original source with posthorizon J. All indicated sink intervals are inside [J,J+2p/rho], since q-1<=p/rho and A-J<=p/rho. The sink negative increment <=its gain; the total matched charge from the fixed source is <=2cstar p/rho. Summing over the original events, both sectors together cost O(NT/ell). These are all-mass bounds, with no constraint on full or effective cohort sizes.

Consequently any remaining pair either has comparable labels p/rho<q<rho p (strict at boundaries) or has an intervening gain exceeding max(p,q)/rho when the labels are disparate. In particular if e<=L=floor(u^.5), every surviving pair is comparable, since q>=kappa P and max(p,q)/rho>>L. Shallow and disparate payments may overlap, but mark in order. This is a statement about gain between endpoint jumps, not total clock lifetime.

## 3. Joint spatial/time CRT for comparable short pairs

Consider 0<=e<=L and rho^-1 p<q<rho p, source p, bad sink q, actual exits v,V. Both labels >=kappa P/rho >>B^.2 and <=B. Since p>L+3 eventually, p=q is impossible: the initial and final congruences would require p dividing p-1+e+tau-sigma (p plus a nonzero odd integer of magnitude <p). Here sigma,tau in {-1,+1} are eligibility signs, p|(C+sigma), q|(A+tau), A=C+p-1+e. As p,q distinct, C occupies at most one progression modulo 2pq. Write a=(C+sigma)/p; source r>(p-1)/4 implies a and C-sigma avoid every odd prime below (p-1)/4 other than possible p itself. On the C progression these two forms are affine in the progression parameter, with slopes 2q and 2pq; for odd primes below min(p,q) they have distinct roots (their relation is multiplication by p and shift -2sigma). Hence the standard two-form Selberg upper sieve used in earlier notes applies. Count relaxed candidates even if no actual intermediate trajectory or no layer match.

Two disjoint ranges:
    range 1: pq<=B^1.8,
    range 2: B^1.8<pq<=B² exp(-u^.75).
For range 1 choose sieve cutoff z=floor(B^(1/100)); log z=Theta(u), progression length O(X/(pq)) with available enclosing interval size comparable to X/(pq)>>B^.2, and square expansion error O(z^8)=O(B^.08) absorbed by the main bound. For range 2 choose z=floor(exp(u^.75/40)); progression length >>exp(u^.75), error O(exp(u^.75/5)) absorbed. As all p,q>>B^.2, z lies below both labels and the source roughness threshold in both ranges. Thus per fixed (p,q,e,sigma,tau) number of C is
    O(X/(pq u^2)) in range 1,
    O(X/(pq u^(3/2))) in range 2.                               (3)
The latter range may be empty at finite scales. No lower sieve assertion. The earlier explicit quadratic upper-bound sieve with g(l)=2/l and squarefree weights suffices; only good odd primes <=z are used, so its denominator is >>log² z by the product/Markov argument and Mertens. The progression is counted in the full original O(X) horizon domain, not a short realized cohort interval.

For each spatial candidate let h=V-v. Actual intermediate total wait <=3e, and bad sink wait <=2r<2(q-1)/u. Therefore 0<h<=3e+2q/u=O(q/u). Actual departure phases are v=alpha(p,sigma) mod 2p and V=alpha(q,tau) mod 2q, alpha(p,-1)=0, alpha(p,+1)=p+2. For each integer h the two congruences on v are compatible in at most one class modulo 2pq. For fixed C, v belongs to an interval of length O(H) from 0<=d<=6+5H. In BOTH ranges pq=o(H), so number of possible (v,V) is
    O((q/u)(1+H/(pq)))=O(H/(pu)).                              (4)
This is a time bound, separate from the spatial sieve. It counts actual source and sink exit slots, not just projected horizons, and uses only the intervening gain, not a specified intermediate word.

## 4. Short-pair charge caps

Group all remaining original tag matches by (C,p,v,A,q,V), with e and signs determined. In each pair key, each tag supplies at most 5cstar p charge, since source positive increment <=5(p-1); total A_pair/(5cstar p) is effective mass <=number of contributing original tags. Count all relaxed keys using (3),(4). For fixed p in the above range, sum of reciprocals of q satisfying p/rho<q<rho p is O(log(2rho)/u) by dyadic prime upper bounds, because all labels have logs Theta(u). Sum of reciprocals of p>=B^.2 is O(1). Thus the weighted key support sums (weight p per key) obey
    sum_keys p << XH (L+1) log(2rho)/u^4    in range 1,
    sum_keys p << XH (L+1) log(2rho)/u^(7/2) in range 2.       (5)
For example the first follows by multiplying (3) and (4), multiplying p, and summing reciprocal p,q, signs and offsets.

Pay full remaining pair charge when its effective mass is at most
    m1=u^3/[(L+1)ell²] in range 1,
    m2=u^(5/2)/[(L+1)ell²] in range 2.                         (6)
The cost in each range by (5) is O(XH log(2rho)/(u ell²))=O(NT/ell), since rho=ell and log(2rho)=O(ell). In fact this is o(NT/ell). These budgets do not rely on the charge being an integer multiple of a tag count. With L=floor(sqrt u), the thresholds are Theta(u^(5/2)/ell²) and Theta(u²/ell²). The initial range reaches medium-large labels, and the second extends to products B^(2-o(1)). Neither covers products close to B²; in particular both labels >=B/u lie outside the second product cutoff for large X. No claim of a bound on that sector.

A surviving short comparable pair in either range has >m_i distinct original contributors, all using exactly the same source departure and sink departure (actual poststates and actual deterministic intermediate events agree). Its initial recorded arrival times may differ. Each contributing tag carries at least one matched level >q/rho across that intermediate actual interval. This implies the whole common intermediate path maintains deficit>q/rho, but not a common exact layer interval of large length. A large effective mass is not a lower bound on every individual charge. Longer intervening gaps and products above B² exp(-u^.75) remain. The exact birth-sink decomposition and all-mass payments apply to every label, not just those in the short-pair sieve.

## 5. New sufficient criterion and comparison

Under finitely many twins eventually all original tags reach T, so (2) implies F_all+R_target,all>=NT-N(P+6cstar). Apply old admissible boundary and source recycled-tick payments, and the new charge payments of sections 2 and 4, once by priority. All total o(NT). Consequently a new sufficient condition for twin-prime infinitude is
    liminf_(dyadic X->infty) (F_rem+R_target,rem)/(NT)<1.
It is implied by the preceding F_rem+R_rec,rem criterion for identical frozen old masks: target source-tick weights dominated by cstar times old recycled weights; cstar=1+o(1) and R_rec<=5NH. Further pair and shallow payments only reduce the new residual. This is an implication of sufficient inequalities, not a strict separation claim on actual MIN paths. This new route does not need the canonical exposure budget, persistent deficit control or total wait control. A large remaining projected admissible boundary mass, long matched intervals and high-product pairs are still unbounded. The exact identity (2) cannot produce the needed upper contraction by itself. No new assertion of twin-prime infinitude.

## 6. Audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/223ee3d007fb9fce74a6f27750a608d15c992385/research/min_unified_targeted_recycle_audit.mjs), exact remote content verification at 223ee3d007fb9fce74a6f27750a608d15c992385. Five normal and three reach-focused tests passed in ECMAScript runtime, not a separate Node process. Focus cap adjusted to exercise heavy pairs and all three focus tests repeated. Reproduce:
    node research/min_unified_targeted_recycle_audit.mjs 256 1024 4096 16384 65536
Finite T=min(8B,floor(X/2)) normal, floor(B/2) focus; P=6 normal,30 focus; kappa=2, alpha=1/8,cstar=4,rho=3; short L=16 normal,8 focus, both labels <=floor(B^.95) and initial p>L+3; cap B/p normal,.02B/p focus. These are diagnostic substitutes, not analytic parameters or a test of the two analytic sieve cutoffs. Tests exact LIFO layer intervals, recorded persistence, independent suffix-min recycled totals, initial-stock charge, bad boundary density, exact targeted flux, source domination, shallow clipping, disparate gain packing, joint spatial/time congruences and deterministic phase, effective pair mass and reached-tag lower bound. No literal gcd oracle repeated, no analytic support census, no cumulative historical masks.

| X/mode | recycled R | targeted charge | shallow paid | disparate paid | pair paid | target remaining |
|---:|---:|---:|---:|---:|---:|---:|
|256|548|0|0|0|0|0|
|1024|1830|213|46.562378|33.277778|0|133.159844|
|4096|17860|3202.808969|682.576511|1303.610949|397.035663|819.585846|
|16384|120990|35569.539464|6158.883247|8360.761711|4977.738555|16072.155951|
|65536|676070|202728.986045|36177.000927|51795.918510|17298.145235|97457.921374|
|4096 focus|6782|466.563707|124.010791|201.625742|63.802423|77.124750|
|16384 focus|39172|3727.934388|1205.032842|1296.023327|62.872340|1164.005878|
|65536 focus|285458|54700.323711|16099.015518|16824.004936|1773.479179|20003.824077|

Largest normal: 5709 roots,140255 completed events,1716 positive-flux bad sink incidences. F=2873142, all grid flux3077514, bad flux204372, initial charge1643.013955, target202728.986045. 55557 source-sink layer matches (including nonbad),261018 actual persistence checks,140255 independent suffix-min stack checks;291 short-pair spatial/time CRT checks,70 groups all thin at finite cap. Largest focus: 2886 full reaches,75256 events,383 bad sinks,26480 layer matches,103628 persistence checks,75256 stack checks,38 short-pair CRT checks;18 groups,13 thin and5 heavy. Reached-tag score1268884.725124 >= diagnostic lower bound822510. The remaining value in table is only the target charge, not F plus target. Many original trajectories stop before T; these finite ratios do not imply the conjectural upper bound. Main and independent source branches unchanged. No Lean verification.
