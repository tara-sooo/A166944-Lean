# Recycled-deficit and rough-boundary flux certificate

2026-11-26 JST. Continues [079d71c41767](https://github.com/tara-sooo/A166944-Lean/blob/079d71c41767f447397b2e3c9152ffdf795c6e7f/research/2026-11-26-min-unified-future-witness-transport.md) and [ad9a99e4a2c8](https://github.com/tara-sooo/A166944-Lean/blob/ad9a99e4a2c82efb66f5ba5f41985797d1a717e3/research/2026-11-26-min-unified-global-deep-record.md). Independent branch heads 1a4005f2f336 and e1ad9e2b434c unchanged at preflight. New alternative full-trajectory sufficient condition not requiring control of terminal persistent deficit, improved arithmetic count of rough primorial crossing keys, and mixed transport of earlier deep positive record charges to either rough/short boundary flux or actual recycled positive drift in their future suffix. No claim of a full contraction or of strict implication between this and the earlier actual-clock condition on realized MIN paths. No Lean compilation.

## 1. Recycled positive increments: an exact local identity

Keep original dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Original prime-root MIN paths through first gain crossing T or earlier original stop; no trajectory changed. Each completed event with selected odd p has gain g=p-1<=B, wait w<=2r<=3g and deficit increment delta=2w-g. All recorded and true tick deficits d=2t-C are nonnegative, root d=6. Total gain <H and total positive drift <=5H per tag. Under no twins all tags reach T for sufficiently large X.

On ANY finite actual recorded segment, index deficits d_0,...,d_n (renumber within segment), and use LOCAL suffix minima m_i=min_(i<=j<=n)d_j. Define
    b_i=(d_i-d_(i-1))_+ - (m_i-d_(i-1))_+.
This is nonnegative and <=positive increment <=2w_i and <=5g_i. The second term measures levels created at i and retained to this segment's end. Since m_(i-1)=min(d_(i-1),m_i), that term equals m_i-m_(i-1), so
    sum_i b_i = V_plus - (d_n-m_0)
              = V_minus - (d_0-m_0),                     (1)
where V_plus=sum(delta_i)_+, V_minus=sum(-delta_i)_+. Equivalently take a stack of initial d_0 level units, push new positive increments, pop on each negative increment: b_i is exactly the amount pushed at i that is later popped before the segment ends. Initial units popped total d_0-m_0. This holds for actual original segments independently of their global observed suffix minima. In the full trajectory d_0-m_0<=6. In the adaptive future suffix below, d_0-m_0<=5B. If b_i>0 then delta_i>0, hence r>(p-1)/4. A positive increment that is retained all the way to the segment end receives zero recycled charge. RESET endings can have small positive drift but are not excluded by label alone.

## 2. A full-trajectory flux certificate without terminal persistent deficit

Take P the largest even primorial <=B^(1/4), with largest prime factor y=Theta(u). By the next-prime bound P>=B^(1/4)/O(u), log P=Theta(u), P=o(T). Set kappa=u^.25, alpha=1/u, and
    cstar=(1+2/kappa)/(1-4/u)=1+o(1)
for sufficiently large X. For an actual completed jump A -> A+p-1 count n_i multiples K of P in [A,A+p-1), i.e. strict crossings. Each K is crossed only once on an original tag. Such a crossing requires p not dividing P: K-A is nonnegative even, congruent to +/-1 mod p if p|P, and its least possible value is then >=p-1, contrary to strict crossing.

Call the boundary key (K,A,p) admissible for the flux ledger if either p<kappa P (short-label sector S) or p>=kappa P and r(A)>=alpha(p-1) (rough sector R). These are disjoint. All other crossings use p>=kappa P and r<g/u. For such an event delta_- = g-2w >= (1-4/u)g, while P n_i<=g+P<=(1+2/kappa)g. Thus P n_i<=cstar delta_-. This is true even if many boundaries are crossed by one jump.

On a tag let F=P times number of admissible crossings over its completed path, and Rrec=sum_i b_i. Total boundary count times P is >=G-P for total actual gain G. Summing the previous inequality and applying (1) gives the exact lower bound
    F+cstar Rrec >= G-P-cstar(d_0-m_0).                  (2)
For the full original trajectory d_0-m_0<=6. Under no twins sum G>=NT and hence
    F_all+cstar R_all >= NT-N(P+6cstar).
This does NOT require d_n=o(T), nor a bound on positive drift that persists to the terminal. Full raw clocks, all low/nonhigh waits, and all deep persistent excess need not be estimated by this route. In particular recycled increments are not the positive last-upcross increments used in the preceding deep-charge certificate.

The two objective components are nonnegative exact original ledgers. F uses P per original tag per admissible boundary key. For Rrec, assign b_i/w_i to each original occupied tick of event i; this is <=2 and gives exact sum Rrec. Do not identify projected crossings with physical tick meetings. Freeze all data before payments.

## 3. Stronger arithmetic support for rough boundary keys

S sector: at fixed K,p, A even in [K-p+2,K] satisfies p|A+sigma, sigma=+/-1. At most one possible A per sign since interval length <p. K ranges over O(X/P) boundaries in the original O(X) horizon domain. Thus
    #S << (X/P) pi(kappa P) << X kappa/u.                 (3)
Here log(kappa P)=Theta(u). Ignore impossible or unobserved keys for an upper bound.

R sector: p>=kappa P so log p=Theta(u), and p/u >> y. Write a=K-A, even, 0<=a<p-1. Roughness r>=g/u implies that a-1 and a+1 avoid all odd primes <=y, because K is divisible by them. The uniform elementary dimension-two upper sieve for the two forms in a (use sieve cutoff floor(y^(1/40))) gives
    #a << p/log²(2+y).
The sieve error O(y^.2) is absorbed uniformly, since p>=kappa P. Both signs allowed. Fix a,p,sigma. K lies in one CRT class modulo Pp, because p not dividing P and p|K-a+sigma. Its interval parameter has length O(X/(Pp)), at least order B^.75 on the full enclosing O(X) range. For primes l not dividing Pp the two integer forms (K-a+sigma)/p and K-a-sigma in this parameter have distinct roots modulo every odd l: the quotient and second form are related by multiplication by p and shift -2sigma. Their coefficients are invertible modulo l. Actual roughness implies avoidance for all such l<=p^(1/40), below (p-1)/u for large X.

Apply the same explicit Selberg upper bound as the earlier two-form positive drift support, now with good sieve primes y<l<=z=floor(p^(1/40)). The main upper density is O((log(2+y)/log p)^2), because the omitted small primes divide P. For clarity: with g(l)=2/l, h(l)=1/g(l)-1, the quadratic weight denominator is G=sum_(squarefree d<=z, good) prod_(l|d)1/h(l). Restrict to good primes <=z^a0 for a sufficiently small absolute a0; the product expansion normalized to a probability measure has independent inclusion probability 2/l. Its expected log d is O(a0 log z), so at least half its product mass has d<=z. Mertens product then gives G >> (log p/log(2+y))². The Selberg square expansion error O(z^8)=O(p^.2) is absorbed by X/(Pp) times that density, since P<=B^.25 and p<=B. The analogous two-form proof with all odd primes <=y^(1/40) supplies the first a-count. This argument uses only standard upper sieve and prime sum bounds inherited from the preceding notes, not a prime tuple lower estimate.

Multiplying the a-count and progression count, summing the two signs, gives O(X/(P log² p)) possible (K,A) for each such p. Summing p<=B yields
    #R << XB/(P u³).                                    (4)
The factor u² saving relative to the unrestricted projected count O(XB/(Pu)) is obtained by both the residue sieve in a and the sieve along K; neither alone supplies the full factor. The change of P from the earlier B/u^4 scale to B^.25 is needed to absorb the progression sieve error. No claim that the same proof works at the earlier larger P.

## 4. Linear flux and recycled-charge payments; new sufficient condition

For each admissible boundary key, full flux = P times distinct original tag count. Pay all its flux if that count <=m_S=H/(kappa P ell) for S or <=m_R=H u²/(B ell) for R. By (3),(4) the summed cost of each sector is O(XH/(u ell))=O(NT/ell). These caps concern PROJECTED crossing counts, not synchronous physical cohort size.

For recycled tick charge, use the inherited positive drift support: at fixed selected p, possible C number O(X/[p log²(2+p)]), since b_i>0 implies r>(p-1)/4. At each horizon O(H) possible occupied ticks, from 0<=d<=6+5H+4B. Group aggregate recycled tick weight, divide by 2 to define effective mass <=number of contributing tags. Pay entire weight if effective mass <=max applicable cap
    m_t(p)=log²(2+p)/(u ell²),
    m_t,high(p)=u²/ell² for p>=Q.
As in 079d71c, sum support times cap using sum_(p<=B)1/p=O(ell), high reciprocal sum O(ell/u). Both costs O(NT/ell). Earlier absolute actual-clock masks can pay at most twice their actual cost in this recycled tick ledger, but do NOT automatically transfer to the boundary flux ledger (a quick jump can cross many boundaries). Combine by priority, not duplicate payments. The two different ledgers are summed with the coefficient cstar.

Denote the remaining original flux and recycled drift by F_rem,R_rem. Since cstar=1+o(1), R_all<=5NH and P=o(T), under no twins
    F_rem+R_rem >= NT-o(NT).
Therefore a NEW sufficient condition for infinitely many twins is
    liminf_(dyadic X->infty) (F_rem+R_rem)/(NT)<1.         (5)
This is independent of the canonical-target normalization, no lower-exposure requirement or a-parameter. It does not require an estimate of the terminal persistent deficit, and does not simply subtract half-gain from one side of the earlier clock inequality. It counts admissible boundary flux and actual recycled positive increments only. For comparison, in an abstract clock ledger that stops at G=T/4 with w=3g at every jump, d_n=6+5G, total elapsed=3T/4, recycled R=0 and F<=G+P. The old constant-margin clock criterion fails while (5) succeeds, before any payments. This is an abstract example only, not an assertion that such a path is realized by MIN. Conversely (5) may be harder on highly oscillatory trajectories. No pointwise dominance of the old absolute criterion or previous normalized criterion on actual MIN paths is established. Their disjunction with (5) is a weaker sufficient requirement than insisting on either old route alone. No proof of (5) yet.

## 5. Refined mixed future witnesses for deep persistent charge

Keep the previous global deep record intervals L_i=(max(D0,d_pre),mu_i], D0=floor(H/u), and their original charge c_i (section 1 of 079d71c). Pay terminal-near charges as before, then use actual suffix after a surviving source until first completed crossing of z_i=floor(d_i/ell²). Its gain in [z_i,z_i+B), birth slack d_i-mu_i<=5B and all suffix recorded deficits >=mu_i. Uniformly z_i>>B. Compute LOCAL recycled b for this suffix, not the global persistent level ledger. All initial units popped in the suffix total d_i-m_0<=5B by (1). Restrict its boundary crossings to K in [C_post,i,C_post,i+z_i) (do not count extras from final overshoot), and classify them by sections 2-3 on the new P. Equation (2), with z_i in place of G, gives a mixed witness denominator
    L_i^w=P #admissible suffix crossings + cstar sum_suffix b
        >= z_i-P-5cstar B >= z_i/2
for sufficiently large X. It is also O(z_i) by total gain and positive drift bounds. This denominator does NOT require all future expensive ticks to be positive drift. Instead a crossing with small r must consume a deficit level; all but <=5B of these consumed levels originated within the suffix.

Route each c_i to the disjoint UNION of its admissible boundary keys and its recycled positive tick keys, proportionally to weights P and cstar b_j/w_j, normalized by L_i^w. This is a single exact partition (unlike the previous product of two independent witness families). No charge duplication. Positive tick weight is <=2cstar, zero for un-recycled positive increments. At a fixed tag/key, all contributing source d_i are comparable to the witness deficit by the preceding narrow relative band lemma, z_i comparable to d/ell², and source gain intervals disjoint in a strip of width O(d/ell²+B). Sum source c_i<=5 times this width; divide by L_i^w>=z_i/2. Thus per-tag marginal load O(P) at a boundary and O(1) at a recycled positive tick, uniformly. Same slot contributors have identical actual suffix when they survive the late trim; no extrapolation.

Apply sections 3-4 caps to the new effective marginal masses (divide by fixed absolute congestion constants times P or 1 instead of the baseline constants). All payments O(NT/ell); previous actual tick masks also transferable by bounded congestion. If desired pay residual portions <=eps c_i with eps=1/ell², total O(NT/ell²). Any remaining source has >=eps c_i remaining; since denominator >=z_i/2, its combined heavy-boundary/recycled-tick witness weight >=eps z_i/2. Consequently either >=eps z_i/(4P) distinct heavy admissible crossings or recycled positive drift >=eps z_i/(4cstar) at heavy tick keys (at ticks integrate b_j/w_j). These alternative witness sets can be used alongside the earlier product witnesses by an additional product partition, not by adding duplicate charges. This stronger selection discards neutral expensive ticks as witnesses in the recycled alternative. It does not assert a bound on the total remaining mass. New charge payments and previous late payments are o(J_a) under prior primorial exposure rate conditions; even small remaining deep excess alone does not prove the earlier normalized clock criterion. The new independent full-trajectory criterion (5) avoids that baseline issue via boundary flux.

## 6. Finite diagnostic audit

[Source](https://github.com/tara-sooo/A166944-Lean/blob/d975107e38c0b173ce2ad2838cffb618cd531be7/research/min_unified_recycled_flux_audit.mjs), commit d975107e38c0b173ce2ad2838cffb618cd531be7, remote readback and largest focus rerun. Derived from 336c270, standalone script:
    node research/min_unified_recycled_flux_audit.mjs 256 1024 4096 16384 65536
Eight ECMAScript runtime tests (five normal, three reach-focused) passed. Finite P=6 normal,30 focus, kappa=2, alpha=1/8, cstar=4; these satisfy the elementary flux inequality but are NOT analytic parameters. Deep routing uses diagnostic z=max(2P,floor(d/4),4 slack), excludes sources if actual suffix too short OR conservative lower bound z-P-4 slack<=0, since analytic z>>B is not valid at finite scales. Diagnostic key caps: baseline boundary aggregate<=2P, tick aggregate<=8 (coefficient already included); mixed boundary<=P,tick<=1. No analytic sieve constants tested, no fresh old-mask union, no literal gcd oracle repeated. Independent stack simulation matches each recycled increment from suffix-min calculation on every whole path and each routed suffix. Tests include strict crossing, cheap crossing deficit bound, actual lower bounds, positive drift support, exact marginal/paid/remaining charge, actual common global minima inherited from parent. Finite per-tag loads observed, not proof of asymptotic constants.

| X/mode | total gain | total positive drift | terminal retained positive increments | recycled drift | baseline score F+4R |
|---:|---:|---:|---:|---:|---:|
|256|2844|2646|2098|548|4952|
|1024|9434|7414|5584|1830|16260|
|4096|84476|68722|50862|17860|151678|
|16384|503474|392920|271930|120990|948102|
|65536|3088970|2396570|1720500|676070|5577422|
|4096 focus|38344|29656|22874|6782|63728|
|16384 focus|232780|185028|145856|39172|382618|
|65536 focus|1588558|1191684|906226|285458|2661272|

Largest normal: 5709 roots, no full T reaches, 34062 bad boundary incidences, 423050 rough,55807 short. F=2873142, baseline diagnostic paid860345.548877. 153109 stack checks,549889 grid checks; deep9694.615680, routed8801.184813 from1131 sources, boundary5678.477140 plus recycled3122.707673; remaining7177.692189 after mixed masks. Largest focus: 2886 full reaches, F=1519440, 1846 bad,33526 rough,17122 short. Reached-tag score2147310 >= diagnostic lower bound822510. 105811 stack and64546 grid checks,58311 mixed tick checks. Deep206206.143161, late/finite-exception120562.741083, routed85643.402079 from5376 sources, boundary69957.683384 plus recycled15685.718695, mixed remaining74492.660421. Maximum observed per-tag boundary load/P=2.923408, tick load11.402473. Finite ratios are not evidence of asymptotic contraction; many original targets unreached. Main and original independent branches unchanged. No external novelty claim or Lean verification.
