# Short boundary close-label halos, graded roughness, and weak-r temporal-pair caps

2026-11-26 JST. Continues [8008fbc06831](https://github.com/tara-sooo/A166944-Lean/blob/8008fbc06831c7c4db24a77248cd2e7cde0c60c2/research/2026-11-26-min-unified-discounted-boundary-support.md) and integrates the prime-root [close-prime sieve](https://github.com/tara-sooo/A166944-Lean/blob/1a4005f2f336ede61cca1a9656c158a559338b72/research/2026-11-26-min-prime-root-small-phase-diamond.md). Preflight independent heads unchanged: prime-root 1a4005f2f336, stable-heavy e1ad9e2b434c. New all-mass projected close-label crossing halo, graded least-factor cap that covers nonrough short labels, and weak-r physical predecessor pair cap for medium-short labels. Controls only additional specified parts of the discounted boundary objective; no full contraction or twin-prime proof. No Lean compilation.

## 1. Setup

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, original gain-stopped prime-root MIN completed paths and terminal snapshots. Each completed event at even C has selected odd prime p<=B, gain g=p-1, wait w<=2r(C)<=2p and w<=3g, deficit d=2t-C>=0 starting at 6. Eligibility sign sigma=+/-1 means p|(C+sigma); exit v=0 mod 2p for sigma=-1, v=p+2 mod 2p for sigma=+1. Total gain <H. All roots reach T eventually under finitely many twins.

Use P largest even primorial <=B^.25, y its largest prime, y=Theta(u), P>=B^.25/O(u), kappa=u^.25, kappa'=u^.125. Strict boundary atom (K,C,p) has K multiple P and C<=K<C+p-1. Necessarily p>y. In the discounted history-free objective J_star of 8008fbc each original tag contributes <=5P/4 per atom; the short part p<kappa'P is assigned [max(0,P n-(g-4r)_+) + P/4]/n for n crossed boundaries. The long weak-r trim, old thin payments and threshold liminf J_star,rem/(NT)<1/4 remain as before. All new masks below are on these frozen original atoms, not actual trajectory deletions. Apply by priority to avoid double counting. The proof uses only the O(P) per-tag atom bound, hence also works on the previous actual discounted and projected cell objectives for the corresponding eligible short atoms.

At any fixed C, a tag visiting it has origin 2M-2 in [C-H,C], since its gain <H. Distinct prime roots M therefore lie in an interval of length O(H); the uniform upper bound on primes in an interval gives at most O(H/log H)=O(H/u) such tags, independently of physical coalescence. This is an upper bound only; it needs no hypothesis that all roots reach T.

## 2. All-mass short close-label boundary halos

Let J=max(1,floor(ell^(1/8))). Mark a short crossing p<kappa'P if on its actual original tag there is another completed event with label q, before or after it, such that |p-q|<=J and intervening gain 0<=e<=J (exclude the two endpoint gains). This condition does not impose any lower bound on r(C), q's roughness or actual waits. If needed choose one actual witness in a deterministic order; an upper count may include all witnesses.

The other prehorizon E=C+h, with h=p-1+e for later witness, h=-(q-1+e) for earlier. The labels cannot be equal for large X: for p=q the congruences require divisibility by p of a nonzero odd integer of absolute value <=J+3, since e is even. But p>y>>J. Also q>=y-J, q comparable to p.

Fix p,q,e, order, eligibility signs sigma,tau. Put a=K-C, even, 0<=a<p-1. The congruences are p|(K-a+sigma), q|(K-a+h+tau), K=0 mod P. Two cases:
* q>y, so p,q are distinct and coprime to P. For each a there is at most one K progression mod Ppq. Since p,q=O(kappa'P), Ppq=O(kappa'^2 P³)=o(X), there are O(X/(Ppq)) K in the full original O(X) horizon interval. Sum O(p) offsets.
* q<=y, so q|P. The q congruence restricts a to one class mod q, hence O(1) offsets since q comparable p. Then K has one class mod Pp, giving O(X/(Pp)) keys.

Both cases give O(X/(Pq)) possible projected crossing keys for these fixed labels and offsets e. No restriction on actual intermediate word or source signs beyond these congruences. Counting q|P separately is necessary; using modulus Ppq in that case would be incorrect.

By the two-form prime-pair upper sieve in 1a4005f2f336, for each 1<=d<=J and Y=y-J,
    sum_(p>=Y, p+d prime, p prime) 1/p
       << log²(2+J)/log Y.
This follows by dyadic intervals V<=p<2V, removing primes <=max(2,J) from the dimension-two sieve, cutoff V^(1/16), with uniform bound O(V log²(2+J)/log² V) on prime pairs, then summing reciprocal contributions. The omitted-prime density loss is log²(2+J), and the square-sieve error is absorbed uniformly since log(2+J)=o(log Y). This is an upper bound, not a prime-pair asymptotic or twin-prime assumption. Sum signs, order, e and d, using comparability of p,q. The union projected support is
    O((X/P)(J+1)² log²(2+J)/log y).
Each key has total original atom weight O(P H/u) by the root interval bound. Hence the full marked charge, with NO cap on mass, is
    O(NT (J+1)² log²(2+J)/log y) = o(NT).               (1)
For the chosen J and y=Theta(u), this rate is O(NT (1+log ell)²/ell^(3/4)). This is a new grid-adapted application of the earlier close-prime halo. The older all-event gain/wait halo bound alone would not pay an O(P) short boundary atom. It includes nonrough short crossings and witnesses with q|P, but does not claim every short crossing has such a witness.

## 3. Graded least-factor sieve, without a rough/nonrough dichotomy

For any 3<=R<=p and fixed p>y, count relaxed projected keys with least eligible odd factor r(C)>=R. The two-stage sieve of 8008fbc works with z=floor(R^(1/40)) and z0=min(y,z). Indeed small odd primes <=z are absent from C±1 (for bounded R use trivial estimates with enlarged constants). In the offset a=K-C the forms a±1 avoid primes <=z0; count O(p/log²(2+z0)) even offsets, with Selberg error O(z0^8) absorbed since z0<=p^.025. For fixed a,p,sign, K in one progression mod Pp; the two quotient forms (K-a+sigma)/p and K-a-sigma have two distinct roots for each odd sieve prime y<l<=z. The progression has length O(X/(Pp)) in a containing interval of comparable length, at least order B^.75. Upper density O((log(2+z0)/log(2+z))²), also when z<=y where the ratio is 1. The error O(z^8) is uniformly absorbed. The proof of the lower bound on the Selberg denominator with missing small primes is identical to 8008fbc section 4; the d=1 term handles a bounded ratio. Hence
    S_p(R) << X/[P log²(2+R)]                           (2)
uniformly in R,p, including p just above y. This counts all projected candidate keys, not distinct actual times.

One could stratify R, but repeatedly applying a whole-budget rough cap would incur a summation loss. Instead use the summable layer-cake weight
    a(r)=log²(2+r)/(1+log log(2+r))².
For t=log²(2+r), a=t/(1+.5 log t)² is increasing on t>=log²5. The tail from (2) for t>=t0 is O(X/(P t)). Integrating a'(t) times this tail, and including the bounded endpoint contribution, gives
    sum_(keys at p) a(r(C)) << X/P [1+integral_(t0)^infinity dt/(t(1+.5 log t)²)]
                             = O(X/P).                (3)
This is a uniform bound on the WHOLE weighted support, not a separate claim about each r-bin. The integral is finite; it avoids an extra ell loss from a bare log² r moment. A least factor r exists at every selected event; relaxed keys in (2)-(3) have p eligible, so r<=p.

Aggregate remaining atom weight A at key (K,C,p), effective mass n_eff=A/(5P/4). Pay when n_eff<=
    m_grade(p,r)=H a(r)/(p u ell²),
or, for p>=sqrt P, the stronger
    m_grade,mid(p,r)=H a(r)/(p u ell).
By (3), the first costs O(XH/(u ell²) sum_(p>y)1/p)=O(NT/ell); the second costs O(XH/(u ell) sum_(p>=sqrt P)1/p)=O(NT/ell). The latter prime reciprocal sum is O(1), since log P=Theta(u). These cap formulas apply even when r<g/log(2+p), unlike the previous rough-only caps. Their ratio to the old plain cap H/(p u ell²) grows as a(r) when r tends to infinity (and the mid range gains the extra ell). For bounded r there is no unbounded a(r) improvement. For previously rough labels retain the stronger old log² p caps rather than replacing them by these graded caps. Union by maximum/priority, cost O(NT/ell). No claim of strict realized-path separation.

## 4. Small-r medium-short physical predecessor pairs

A different payment handles some very small-r crossings, for which the graded cap is weak. Use
    L=floor(sqrt u), R0=ceil(u²).
Consider p in [sqrt P,kappa'P), r(C)<=R0, and an actual earlier completed event with label q in [p/2,2p] and intervening gain e<=L. For large X both labels exceed y and L+3, q!=p by the equal-label congruence obstruction in section 2. This is a genuinely nonrough crossing sector because R0=o(p/log p) uniformly here. Freeze one such actual predecessor (e.g. the most recent). Its prehorizon A=C-(q-1+e) and exit V; the crossing exits at v. Then
    0<h=v-V<=3e+2r(C)<=3L+2R0,
by actual intervening waits and the weak crossing's wait bound. This uses the crossing's small r even if the predecessor itself had large r.

For fixed p,q,e and signs, the spatial count of (K,C) is O(X/(Pq)) as in section 2 (both labels coprime to P). For fixed such spatial key and integer h, the two exit-time congruences determine at most one class for V mod 2pq. The time slab at a fixed prehorizon has length O(H), from the original deficit envelope. Here pq=O(kappa'^2 P²)=o(H), so the number of (V,v) is O((R0+L)H/(pq)) for each spatial key. No assumption of independent prime or phase distributions is needed. Group original tag-atom charge by (K,C,p,A,q,v,V), with one chosen predecessor per original atom, not by just the two horizons. Each original tag contributes at most 5P/4.

For fixed p the count of relaxed joint keys, weighted by P, is at most
    O(XH (L+1)(R0+L)/p * sum_(p/2<=q<=2p)1/q²)
      = O(XH (L+1)(R0+L)/(p² u)),
since log p=Theta(u) and the prime upper count in the dyadic interval is O(p/u). Pay all remaining charge of each joint key if its effective mass (aggregate/(5P/4)) is <=
    m_pair(p)=p/[(L+1)(R0+L)ell].
The total over p>=sqrt P is O(XH/(u ell) sum 1/p)=O(NT/ell). This is a physical-pair cap of order p/(u^(5/2) ell), which grows faster than any fixed power of u throughout the stated range. It is NOT directly comparable to the old projected-key cap: one projected key may contain many physical predecessor/exit pairs, and the old projected cap can pay some keys first. No strict realized-path improvement or claim that every weak short crossing has such a predecessor. A residual joint key with positive charge above cap contains more than m_pair(p) distinct original contributors at common actual predecessor and crossing departures; by MIN determinism they share the intervening completed suffix. Their incoming arrival times before the predecessor may differ. This is only for actual predecessors and not arbitrary pairs of events at nearby horizons.

## 5. Resulting sufficient condition

Use the discounted projected objective J_star of 8008fbc with the prior long weak-r and cap masks, then the all-mass close-label mask, graded caps and physical predecessor caps, all on frozen original atoms. Their total cost o(NT), by (1) and the explicit linear budgets above. Under finitely many twins the remaining objective is still >=(1/4-o(1))NT. Thus the residual sufficient inequality
    liminf_(dyadic X->infinity) J_star,rem/(NT)<1/4
is at least as weak as the previous one on identical old masks. The residual includes bounded-r short crossings without close-label witnesses and without a qualifying recent comparable predecessor, as well as heavy physical pairs and other heavy projected keys. None of the new bounds establishes the needed total upper contraction. No claim of a complete proof, strict separation on realized asymptotic MIN ensembles, or external novelty. Main and independent branches unchanged.

## 6. Audit

[Standalone source](https://github.com/tara-sooo/A166944-Lean/blob/2b539fe7b43d549699262978172d6a09a1251523/research/min_unified_short_boundary_pair_audit.mjs), exact remote readback verified at 2b539fe7b43d549699262978172d6a09a1251523. Eight finite runs (five normal and three reach-focused) passed in ECMAScript runtime, not a separate Node process. Initial execution had a Set method typo, corrected before final eight runs. Reproduce: node research/min_unified_short_boundary_pair_audit.mjs 256 1024 4096 16384 65536.
Finite T=min(8B,floor(X/2)) or floor(B/2), P=30 normal or 210 focus, short p<2P, J=4,L=8,R0=max(3,floor(sqrt B)); finite joint cap p/(R0+L+1) normal or .02 times that focus. These are diagnostic substitutes, not analytic thresholds. Checks actual completed paths, strict boundary and original root range, close witness order and distinct-label congruences, q|P case, observed spatial-key counts against explicit relaxed CRT progression cardinality envelopes, weak actual predecessor time congruences and h bound, effective mass aggregation. The audit counts relaxed eligible projected keys in the whole even horizon slab [2X-2,7X) for the finite short labels, tabulates nested r tails at 3,5,11,23 and the graded moment. It does not test analytic sieve constants, prove a uniform asymptotic bound by those finite counts, or independently census all temporal pair slots; the slot count is a paper CRT deduction. No cumulative historical masks, literal gcd oracle or full J_star upper inequality tested.

| X/mode | short objective | close-label paid | nonrough part of close payment | remaining qualifying temporal-pair charge | finite pair cap payment |
|---:|---:|---:|---:|---:|---:|
|256|3225.5|1050|262.5|0|0|
|1024|8783|1456.5|219|230.5|55|
|4096|63527.5|7353|738|3170.5|278.5|
|16384|286172|29401|1891|19009|552.5|
|65536|1152099.5|137034|13899|123948.5|1745.5|
|4096 focus|43114.5|4725|787.5|0|0|
|16384 focus|272579|18112.5|1575|4995|0|
|65536 focus|1642044.5|84471|4713|64012.5|106.5|

Largest normal: 5709 roots,140255 completed events, no reaches of T, 32215 short tag-boundary atoms,3694 close witnesses (1737 forward,1957 backward),886 distinct close projected keys,164 relaxed CRT cardinality checks. 3488 physical pair congruence checks,1047 joint keys (61 finite thin,986 heavy),843 distinct projected keys; max diagnostic effective pair mass42. Graded tail census14 labels. Largest focus: 2886 roots reach T,75256 completed events,6514 short atoms,322 close witnesses (62 with q|P,260 coprime),141 close projected keys and84 CRT groups;250 pair time checks,120 joint keys (2 thin,118 heavy),101 distinct projected keys, max effective mass8; graded census77 labels. Finite ratios are not asymptotic estimates; the short objective omits other sectors and many roots stop before T.
