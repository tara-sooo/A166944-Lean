# Rough target phase split: RESET drop transfer and near-neutral LOW entry arithmetic

2026-11-25 JST. Continues 01297e90920780c6a6821bd364843ca947d143e8. New paper deductions: exact survival of anchor high levels through the LOW tail and common recorded rough target; coefficient-one RESET drop transfer with absolute O(XBL) tail error; quantitative positive, strong nonreset descent and near-neutral nonreset sectors; an upper sieve for near-neutral joint incoming/outgoing phase keys giving a further absolute quota. Heavy near-neutral keys, full positive energy and descent moments remain open. No Lean compilation, twin infinitude OPEN.

## 1. Actual ensemble and level survival

Keep dyadic X, odd roots M in [X,2X), B=ceil(sqrt(7X)), u=log B, H=4B, s=M+2, C_initial=2M-2, gate K(M)=floor((7M-1)/4). Fixed-cap MIN, actual completed waits including crossing at/beyond nominal cutoff, endpoints e_M<=s+6B or earlier twin. True deficit d=2t-C in [0,12B+6]; total horizon gain <=12B+6. Each completed wait w<=2r<=2p with r the least eligible prime and p the actual selected prime. Use long-age LOW nonreset donor anchors g and normalized rows x_i(g) in [0,1] as in 24bfe41, a068c67, 01297e9. Even primorial L<=u^1/16 largest, y largest prime, rough target r>=R=cB/u² for fixed c>0. The final LOW incoming prime into the target is denoted q<=y here; it is NOT the earlier last nonLOW anchor label denoted q in previous notes.

For an anchor g, its two distinct supporting donor tags share the same actual recorded arrival b at target C and completed outgoing event (v,J=C+p-1,p). Put w=v-b, d_b=2b-C, d_v=2v-J, delta=(d_b-d_v)_+, d_g>6, D_g=d_g-6, x=x_i(g)x_j(g)<=1. Their contribution to the offdiagonal moment M_off=S^sharp+I^sharp is c_ijg=(r/B)x D_g. Each pair/target slot occurs at most once among anchors, and for a fixed unordered pair sum_g r/B<=27 by actual completed target gain. The same anchor fixes its entire deterministic LOW tail and final incoming label q. No occupation outside original endpoints.

Let C_g be the post horizon of the anchor. Its LOW tail total gain G=C-C_g satisfies 2<=G<L. Its true deficit can drop by at most G below d_g, even if it has intervening positive changes, since clock increments are nonnegative. In particular d_g-d_b<=G. Let mu be the minimum of d_g and all actual recorded post deficits on the LOW tail through arrival b. Then the exact integer high-level count decomposition is
    D_g = l_low + l_target + l_surv,
    l_low = d_g-max(6,mu),
    l_target = min(max(0,mu-6), max(0,mu-max(6,d_v))),
    l_surv = min(max(0,mu-6),max(0,d_v-6)).
Equivalently l_target=max(0,mu-6)-l_surv. Here l_low<=G, l_target<=delta, all nonnegative. These are originally present levels that survive continuously, not levels that disappear then reappear. The minima of true d occur at actual post-states (stationary ticks increase d). The formulas hold also for positive target drift. Multiply by (r/B)x and sum over pairs/anchors to get an exact weighted decomposition. The total LOW-tail loss is at most 27 L per distinct supporting pair, hence O(XBL) since O(XB) possible internal donor pairs (source difference<=6B).

## 2. RESET transfer and post phase

For the outgoing event side s=v mod2, the exact MIN congruences are
    C+2s-1=0 mod p, v=rho(p,s) mod2p,
    rho(p,0)=0, rho(p,1)=p+2,
    d_v=6s+2p k, k>=0.
In particular k=0 is RESET with d_v<=6; k>=1 implies d_v>=2p>=2r. If RESET, then d_g-6<=delta+G, so
    c_ijg <= x delta + (r/B)x G.
This uses r/B<=1; a stronger drop multiplier r/B is available. Consequently
    M_reset <= D_target,reset + O(XBL),                  (1)
where D_target,reset sums x delta over actual DISTINCT supporting donor pair/recorded target waits with RESET. This includes zero or positive drift if such cases occur (the bound remains valid and D_g<=G for positive RESET). In the audit RESET classification is among nonpositive waits only; any positive RESET is instead in the positive sector. All anchor high levels surviving the tail disappear at the RESET target. This is a coefficient-one transfer, not a bound on D_target,reset. The O(XBL) term is o(XB u³). The exact weighted l_target at RESET is at most (r/B)x delta, not an assertion that the complete negative drop is all originally charged.

For nonRESET nonpositive waits, d_b=d_v+delta and d_v>=2p. Therefore d_g-6<=d_v-6+delta+G. In contrast to RESET, the post phase can preserve a large high-level moment even if delta is small. This is why net descent alone at the actual target is insufficient for this class. The phase k is bounded by (12B+6)/(2p), O(u²) for r>=R, but need not be uniformly bounded.

## 3. Quantitative nonRESET split and improved constants

Let A_R=1-1/R, so p-1>=A_R r on all rough targets. Define e=w²/(2r). For positive net drift w>(p-1)/2, e>=A_R² r/8. As D_g<=12B,
    M_pos <= 96/A_R² E_target,pos <= 96/A_R² E_+^full.
For nonRESET nonpositive waits and 0<eps<1, classify strong if delta>eps(p-1), near-neutral otherwise, including zero drift. The strong sector satisfies
    c_ijg <= 12/(eps A_R) x delta.
In the near-neutral sector
    (1-eps)(p-1)/2 <= w <= (p-1)/2,
    v-(p-1)/2 <= b <= v-(1-eps)(p-1)/2,              (2)
so
    c_ijg <= 96/[A_R²(1-eps)²] x e.                 (3)
These sharper rough-target constants use the actual R, not the all-prime bound p-1>=2r/3. The finite code tests the weaker universal constants 18/eps and 216/(1-eps)²; the sharper constants follow directly from the displayed inequalities and are paper-only. The strong descent coefficient grows as eps shrinks. No assertion that either controlling moment is little-o. Positive sector, nonpositive RESET, strong nonRESET and near-neutral nonRESET are disjoint. No addition of previous alternative raw transport bounds.

## 4. NEW joint phase support of near-neutral LOW arrivals

For fixed final incoming LOW q<=y and outgoing p>=R, p<=B, actual near-neutral tuple K=(C,b,v,p,q) satisfies the two sides s0=b mod2, s=v mod2:
    C+2s0=0 mod q, b=rho(q,s0) mod2q,
    C+2s-1=0 mod p, v=rho(p,s) mod2p,
    r(C)>=R, d_v>=2p, d_v<=12B+6,
and (2). Both primes odd, distinct eventually since y<R. We count relaxed tuples, not source multiplicities. For each q,p and both sides, C even in an O(X) interval belongs to one CRT progression of step 2pq, of length O(X/(pq)); enlarge a short boundary interval to a comparable length at least c'B/y. Apply the established uniform dimension-two upper sieve (see 2026-11-24-min-growing-cutoff-sieve-weighted-reset.md, earlier applications in 6852f2c and 24bfe41). One sieved form is (C+sigma)/p, with sigma=2s-1, the other C-sigma. For odd primes ell<=z0=B^1/64 excluding q, p>z0 eventually; both forms have invertible linear coefficients in the progression parameter, and their roots are distinct because their difference after multiplying the first by p is -2sigma. Omitting q changes the Mertens product by at most an absolute constant. True roughness of C ensures both forms avoid these small primes (p is large). CRT errors O(z0 log(2z0)) are negligible since y<=L<=u^1/16 and X/(pq)>=c B/y. Thus the number of C for fixed p,q,s,s0 is O(X/(p q u²)). This uses the actual outgoing p as the conditioned large divisor, not the possibly different least r(C). No third independent divisor condition is imposed.

For fixed C,p,side the number of outgoing v is O(B/p), since d_v in O(B), and b in the narrow interval (2) has O(1+eps p/q) candidate incoming phase times. Summing over p in [R,B], and the two sides each,
    S_q(eps) <= O((XB/(q u²)) sum_(R<=p<=B)1/p²
                  + (eps XB/(q² u²)) sum_(R<=p<=B)1/p).
Chebyshev partial summation gives sum 1/p²=O(1/(R log R)), and reciprocal sum O(log u/u) for this near-top interval. Hence
    S_q(eps)=O(X/(q u) + eps XB log u/(q² u³)).          (4)
The first term is essential: for a very narrow interval the phase progression may still have one valid b. The result holds uniformly 0<eps<1; extra actual MIN selection, LOW-tail origin and recipient age constraints only reduce support. For finite diagnostics thresholds R=ceil(B/16) etc differ from the asymptotic R and are not used to infer constants in (4). The support counts tuples including b, not just C,v or earlier nonLOW anchor keys. One tuple can carry multiple anchor cohorts; pair/target contributions are unique and all actual charge at that tuple is aggregated before applying a quota.

Choose eps=u^-1/4 (eventually <1) and assign capacity q u^6 per actual near-neutral tuple. Pay min(actual remaining M_off weight at tuple, capacity). The total is at most
    O(X y u^5 + eps XB u³ log u sum_(q<=y)1/q)
      =O(X y u^5 + XB u^(11/4)(log u)^2)
      =o(XB u³).                                      (5)
Here y<=u^1/16 suffices for the first term, and the elementary bound sum 1/q<=O(log u) suffices for the second. This is an absolute arithmetic payment on the normalized offdiagonal donor moment. It is compatible with previous quota payments only on actual remaining weights. It does NOT establish that the raw near-neutral sector is negligible. Heavy tuples retain mass beyond q u^6. A corresponding strong-descent transfer at this eps has coefficient O(u^1/4); (3) remains bounded as eps tends to zero. Can use fixed eps instead if a bounded strong-descent coefficient is needed, with cap q u^23/4 and the same little-o budget.

Together, on disjoint sectors, (1)-(5) give the alternative reduction
    M_off <= (96/A_R²) E_target,pos
             + D_target,reset
             + (12/(eps A_R)) D_target,strong
             + M_neutral,res + O(XBL) + P_neutral.
The residual M_neutral,res can alternatively be transferred to E_target,neutral with (3). For the shrinking eps above, P_neutral=o(XB u³). This reduction is not a proof of the needed small-o on M_off and is not a direct payment of original cross charge W_g. The diagonal O(XB), cross-to-donor coefficient chi, recipient reuse, and other original unresolved sectors remain.

## 5. Finite verification

Standalone research/min_clock_rough_target_phase_audit.mjs, source commit 60eb9c375daa57ab2b5ecb1b3611f2f3825cea0d, exact remote blob e8ea566b49e2b8042426122762f5fd217f595d23. Extends 01297e9 audit, same actual original masks and 12 sampled rough origin/levels per X; same donor anchors and row weights. Adds checks of both actual recorded target arrivals/departures, LOW tail gain and minimum, phase congruences, canonical pair/target uniqueness, exact low/target/survivor decomposition, coefficient-one RESET inequality and finite near-neutral/strong transfer. For each realized near-neutral q,p pair independently enumerates the full relaxed C range with roughness and both clock progressions, tests actual tuple count against relaxed support, and aggregates actual weight per tuple before diagnostic quota. No sieve constant estimated from these finite counts. All assertions passed.

Run:
    node research/min_clock_rough_target_phase_audit.mjs 4096 16384 65536
Actual functions executed in available JS runtime, not separate Node. Twelve original window/occupation/LOW modes; each three diagnostic eps=1/16,1/4,1/2 =36 bands, four original modes nonempty. R=max(y+1,ceil B/16), diagnostic cap 8q, L30/y5 or L6/y3 (independent, not combined). The quota is an independent comparison of the near-neutral sector, not added to previous exit token payments. Code verifies universal constants (see section3) and finite phase support, not the asymptotic sieve bound. The new arithmetic support proof (4)-(5) is paper-only. No Lean compilation.

| X / LOW | M_off | positive targets | nonpositive RESET | nonRESET nonpositive |
|---|---:|---:|---:|---:|
|4096 L6 (either occupation)|10175.29412|0|0|10175.29412|
|65536 L30 full|1169082.55457|1156101.58112|0|12980.97345|
|65536 L6 full|1511912.58407|1496831.75811|2021.84366|13058.98230|

X65536 L6 RESET 47 distinct pair/target incidences, 5 physical target tuples. Weighted reset drop5388, weighted tail gain allowance34.47493; all originally present high levels disappear at target. The sampled RESET tuples (C,b,v,p,drop) are (202380,101226,101420,461,72), (201660,100920,101040,421,180), (164700,82380,82404,109,60), (164868,82488,82490,113,108), (164502,82284,82340,179,66). No positive RESET or zero drift observed in these samples. All LOW-tail original high-level losses zero; total target-consumed and surviving weights for largest L30=1990.41593/1167092.13864, L6=4014.16224/1507898.42183. The latter differs from future-through-end exit partition (4090.26844 matched) because additional drops can occur after target. This is not a contradiction or duplicate payment.

At eps=1/4:
| X / LOW | strong nonRESET | near-neutral nonRESET | near quota paid | near residual |
|---|---:|---:|---:|---:|
|4096 L6|0|10175.29412|24|10151.29412|
|65536 L30|12980.97345|0|0|0|
|65536 L6|12980.97345|78.00885|24|54.00885|

All actual near-neutral labels q=3. X4096 key (C,b,v,p,q)=(14850,7488,7502,31,3), r31,w14,delta2,post phase2,465 actual pairs, near support1011; at eps1/16 it instead belongs to strong. Largest L6 near key (164820,82458,82474,43,3), w16,delta10,phase1,15 pairs, near support19129. At eps1/2, larger key (165480,82896,82933,127,3), w37,delta52,phase1,231 pairs, charge12980.97345 enters near-neutral. At eps1/16 all nonRESET nonpositive in these nonempty modes are strong; finite near support zero because no realized labels. Largest actual positive target (203040,101862,102215,p277,q3), w353, 4186 pairs, charge1156101.58112, phase2. This further focuses the empirical obstacle on the actual positive rough targets, but is not a general limiting statement. Main and other branches unchanged.

## 6. Next

Try the rough positive target moment directly: distinguish actual recorded arrival cohorts (including common last LOW predecessor), estimate their earlier shared ancestry at large r and exploit the exact phase k and actual duration. For near-neutral heavy tuples exploit the additional prior nonLOW anchor and recipient age, or use phase k to refine support; no general multiplicity bound yet. For strong/RESET sectors retain the actual descent accounting and its earlier high-birth debit; neither can simply be declared small. Full positive energy, original cross-to-donor linkage/recipient reuse, and all previous residuals remain. No twin infinitude claim.
