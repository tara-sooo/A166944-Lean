# Deficit-divisor count for close asymmetric high anchors before same-label mergers

2026-11-25 JST. Continues f68d30207d956f9ad45f7a1b3ecf7eaf78a804a9 (local predecessor-clock potential), e15eb81dd0e0e1fe2b98086421b9c5023fd2f313 (rough reset sieve), 4580e75ba854faf268cd3f48335dac94ea2d17af (direct partner quotas), and earlier close physical last-high anchor CRT work. NEW polynomial saving for nonreset close physical anchors, allowing asymmetric incoming thresholds, by factoring an integer of size O(B) rather than independently summing both large primes. Does NOT prove the general local heavy-branch bound; no Lean compilation or full twin proof.

## 1. Setup and clock identities

Dyadic X, N=X/2 odd original roots M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a_slab=2B,G=2H+B+6. Assume H+2B<=min(K-s_M) eventually. Full original MIN prefixes include crossing state at/beyond relative H or twin terminal. C strictly increases, t strictly increases, C<=2t, total gain<=G, post-state deficit 0<=2t-C<=12B+6. At pre-horizon D, selected p has wait<=2r(D)<=2p<=3(p-1), r least eligible odd prime<=B. All horizons in [2X,7X). At final C, w_M(C) is original wait duration clipped to relative [a_slab,H)/(2r(C)) or any smaller nonnegative sector/mask weight, hence <=1. R=sum r U<=NB, E=sum r U². Histories are never thinned for first contact.

A physical incoming anchor (J,t,q) consists of the actual post-state and its incoming selected prime q>0. Let s=t mod 2. The MIN clock congruences give

    q | J+2s,
    t = 0 mod 2q if s=0, q+2 mod 2q if s=1,
    2t-J = 6s+2qk, integer k.

For q>=7, k>=0 by the deficit strip and k<= (6B+3)/q. Call k=0 RESET (not identical to root); otherwise NONRESET. The condition is arithmetic and does not assume the anchor itself has a rough predecessor. A fixed physical state may have several possible incoming labels; count labeled anchor keys.

## 2. NEW close-anchor rigidity and divisor count

Let 7<=Q<=P<=B, A,Z>=0, with

    Q>A+2, Q>Z+A/2+3.

Consider ORDERED pairs of DISTINCT PHYSICAL anchors (J,t,q),(J',t',q') with q>=P,q'>=Q, |a|=|J'-J|<=A (a even), |b|=|t'-t|<=Z. Anchor physical distinctness excludes a=b=0 even if labels differ. The same conclusions hold when the first anchor is chosen by swapping the two labels if needed. Let s,s' be arrival parities. Subtract the two deficit identities:

    q'k'=qk+b-a/2-3(s'-s)=n.                            (1)

**Rigidity.** If q=q', their horizon divisibility gives q|(a+2(s'-s)), so a=-2(s'-s). Equation (1) then gives q(k'-k)=b-2(s'-s). Its magnitude is <q, hence k'=k and b=2(s'-s). But b mod 2 = s'-s mod 2; this forces s'=s, a=b=0, contrary to distinct physical states. Thus q!=q'. Further, if k=0 then |n|<Q; since k'>=0 and q'>=Q, necessarily n=0,k'=0. The converse is identical. So either both reset or both nonreset. If both nonreset, n>0, n=O(B) by the deficit strip.

**Nonreset enumeration.** Fix q>=P,k in [1,(6B+3)/q], even offset a, signed b, s,s'. Equation (1) forces q'>=Q to be a prime divisor of the particular nonzero integer n=O(B). At most O(log B/log Q) such divisors, even if prime q' is not in [P,B]. Each q' fixes k'=n/q'. Then J satisfies
    J=-2s mod q,
    J=-a-2s' mod q'.
The primes are distinct, so CRT gives O(X/(q q')) possibilities for J in [2X,7X), including endpoint rounding because q q'<=B²=O(X). The clock t is fixed by J,q,k,s, and t',J' are then fixed. Additional parity and actual next-event conditions only decrease the count. Using the elementary Chebyshev bound sum_{p>=P}1/p²=O(1/(P log P)) (dyadic summation), we obtain

    A_non <= O( X B (A+1)(Z+1) log B /
                   [P Q log P log Q] ).                (2)

This is a bound for possible ordered labeled physical anchor pairs, not a count of root pairs. It uses no roughness, no assumption about common labels after anchors, no independent clock distribution. The important saving is that for each nonzero deficit, q' is a divisor of n, rather than a freely chosen prime; n has only O(log B/log Q) prime factors >=Q.

**Reset enumeration.** Here k=k'=0, hence b=a/2+3(s'-s), determined by a and parity. Fix distinct q,q', a, s,s'; CRT gives O(X/(q q')) choices. Therefore

    A_reset <= O( X(A+1)
                 (sum_{P<=q<=B}1/q)(sum_{Q<=q'<=B}1/q') ). (3)

No Z factor is needed in this term. The two classes are disjoint. Equation (2) cannot be applied to reset anchors because n=0 is divisible by every prime. Both reset and nonreset envelopes include candidates not visited by any original tag.

## 3. Application to actual first physical mergers

Fix an actual pair of distinct original tags with a first physical meeting v strictly AFTER a chosen incoming anchor on each of the two paths. The anchors must be physically distinct: if equal, they already met there. One anchor has label >=P and the other >=Q. Impose the bounds |J'-J|<=A, |t'-t|<=Z above. Use any fixed single assignment of an eligible anchor pair per original root pair (e.g. both latest >=Q post-states strictly before v, one label >=P; orient by the qualifying label, ties by source order). The assignment is fixed independently of final evaluation C. If both immediate predecessor states of a same-label first merger at (t_v,J_v) have such incoming anchors, their projected horizon is the same D, and their lag is <2r(D)<=2p, where p is the common label entering v. In particular all such pairs with 2r(D)<=Z are covered even if p itself is much larger than Z. This replaces the earlier near-B assumption on p by a condition on the preceding incoming labels and actual lag.

More generally if each chosen anchor is followed by a suffix to v of gain <=A, then |J'-J|<=A and |t'-t|<=3A by the wait/gain bound. This holds for a maximal LOW-only suffix after a nonLOW anchor with L_y=product_{p<=y}p<=A, using the primorial barrier (LOW gain<L_y); v may be a first merger strictly inside the block. Both incoming anchors must meet the specified P,Q thresholds. The conclusion does not require identical intermediate LOW labels or common projected history. We can also cover arbitrary short gain suffixes with nonLOW labels; no LOW restriction in (2).

For a fixed ordered labeled anchor pair alpha, the two forward continuations are deterministic, independent of original source cutoff until each stops. Their first common physical state, if both reach it, is unique. For all original pairs assigned to alpha, every occupied evaluation state C AFTER this first meeting lies on the same deterministic suffix of that state. Their union is a prefix of the longest actual continuation; sum_C r(C)<=sum selected labels<=1.5 G. No multiplicity factor for the number of distinct evaluation C or final sectors.

At each alpha,C let V(alpha,C) be ordered pair product 2 sum_{i<j assigned alpha} w_i(C) w_j(C) after optional arbitrary prior fractional pair exclusions, restricted to common states after their first physical meeting. For reset/nonreset cap K_0,K_1, pay min(V,K_c) of actual ordered product (proportional fractional allocation possible). Then

    E_paid <= 1.5 G ( K_0 A_reset + K_1 A_non ).          (4)

This upper bound on actual synchronous energy applies even if all anchors have large raw ancestors and the pair products vary between final C. It is independent of earlier clock-cell or direct-partner budgets and can be applied after them. It does NOT pay asynchronous earlier overlaps or unrestricted large products at covered anchors. Positive remainder in class c implies actual assigned ordered product >K_c before cap. In particular the product of the full final-weight anchor-group masses exceeds K_c/2 (the assigned cross products are a subset). If label order could be chosen both ways, count ordered anchor keys separately as in (2)-(3).

## 4. Parameter examples and polynomial caps

Write u=log B, l=1+log u. Take P=ceil(B/u^(1/8)), Q=ceil(B^(3/4)), A=2 floor(u^(1/8)), Z=3A (eventually P>=Q and short geometry). Chebyshev/partial summation gives sum_{q>=P}1/q=O(l/u), sum_{q'>=Q}1/q'=O(1). Hence

    A_reset = O(X(A+1) l/u),
    A_non = O(X B^(-3/4) (A+1)^2 / u^(7/8)).            (5)

By contrast the direct two-prime CRT envelope need not give a power of B for these offsets. The polynomial saving is for NONRESET only. Take cap K_0=u^(7/2), K_1=B^(3/4) u²/(1+A)². Equation (4) gives
    E_paid,reset = O(XB u^(21/8) l),
    E_paid,non = O(XB u^(9/8)),
both o(XB u³). Thus actual nonreset pair products can be polynomial in B, not just polylogarithmic, without exceeding the sufficient energy target. This is a stronger threshold at the same-label first merger when BOTH preceding anchors are recent and high. It neither bounds how many roots have those histories nor implies all products satisfy the cap.

For the MED sector from 2c5f5f0 (z largest prime cutoff L_z<=B^1/16,T=ceil B^1/4, natural MED E=o(XB^(13/8)u³)), multiply caps by B^5/8, as in the audit. The corresponding nonreset cap is B^(11/8)u²/(1+A)². Paid terms are still little-o of MED target. HIGH retained E=o(XB u³) with valid o(XB) linear deletion remains the other sufficient condition. No change to LOW-destination accounting.

For NONRESET alone much larger offsets are allowed: A=floor(B^1/16), Z=3A, same P,Q, gives A_non=O(X B^(-5/8)/u^(7/8)). Choose K_1=B^(5/8)u², still paid O(XB u^(9/8)). This covers any two large anchors followed by suffixes with gain<=B^1/16, including LOW-only blocks at the logarithmic primorial cutoff. The reset count with that A has a polynomial A factor and does NOT yield the corresponding large reset cap. At the largest A this is a nonreset-only extension, not a uniform improvement of the reset bound. Not separately audited at these asymptotic parameters.

More generally (2) is polynomially sparse whenever P Q/(B(A+1)(Z+1)) grows by a positive power of B (and log P,log Q comparable to log B); this permits substantially smaller preceding labels than requiring both near B. However small labels on one or both branches, or high anchors far away, are not controlled by this estimate. No assumption that most residual pairs have such anchors.

## 5. Actual finite verification

Standalone research/min_clock_deficit_divisor_audit.mjs, exact readback b0b42d855862453e3c1b5626a9689eebae40ebb2, blob 04b1cf484698f3be4c3519b07ab5e7ff367b1f7f. Run

    node research/min_clock_deficit_divisor_audit.mjs 1024 4096 16384 65536

12 successful final runs, four X windows x three modes, actual JS function in available runtime. Uses independent inherited parity-GCD MIN simulator, including final vertices, 4658 literal comparisons per X1024 mode. Initially direct arithmetic envelope disagreed because divisor enumeration included same physical state with two different labels; corrected exclusion of a=b=0, then independent D-first enumeration matches exactly at X1024 and 4096 for all modes. Enumerate q,k,a,b,parities and factor n, exact CRT mod q q' and parity mod4; reset enumerate labels separately. Check actual original pair prefix first physical meeting, last >=Q anchors strictly before same-label meeting, rigidity and exact equation, CRT membership, unique meeting per ordered anchor pair, actual sum r along used future suffix and exact capped energy partition. Floating tolerances for fractional weights. No earlier masks, quota unions or rare-state caps imposed; ledger is independent RAW sector energy. This is not a cumulative residual improvement. All three modes have the same natural paths at a fixed X. Analytic A=2,Z=6 throughout finite range; no asymptotic growing regime or positive eligible pair. Diagnostic P=ceil(B/4) or >=Q,Q=max(19,ceil(B/8)), A<=12, caps16/64; stress P=ceil(B/8) or >=Q,Q=max(19,ceil(B/32)), A<=12 subject to short geometry, caps8/16. The diagnostic and stress caps not the asymptotic ones.

At X4096 diagnostic P43,Q22,A4,Z12, independent candidate counts reset6739/nonreset43247. Actual nonreset same-label first-merger raw MED408.84,HIGH872.31 all from immediate predecessors and subsequent selected p<=5, fully within cap64. Stress P22,Q19,A2,Z6 independent counts2304/40996; raw nonreset515.65/907.13 includes earlier anchors106.81/34.82 and fully paid by cap16.

At X16384 diagnostic P85,Q43,A8,Z24, arithmetic envelopes37804/246352; actual raw nonreset MED714.10,HIGH1831.74 (all earlier rather than immediate, fully paid cap64), reset raw6049.93/6408.97. Thus nonreset terms are nonvacuous in smaller windows.

Largest X65536,B678,N32768,794415 events,R402074. Analytic P537,Q133,A2,Z6, candidate envelopes1828/1424, 11476 nonzero divisor tests, maximum one allowed factor; no actual eligible positive pair. Standard P170,Q85,A12,Z36, candidate envelopes177925/833397, 1718724 nonzero divisor tests, maximum one allowed factor. Actual only reset raw MED1670.96,HIGH2210.05 (one key each), paid582.19/2064.18; no nonreset pairs.
Stress P85,Q22,A4,Z12: candidate envelopes203174/1479961,354516 nonzero divisor tests,346234 CRT calls,max two allowed factors. Natural MED E2733359.93,HIGH15313316.11. Same-label raw first physical energy2456804.73/13817252.16. Among them both latest >=Q anchors with one >=P, before proximity restriction, raw962405.16/6485971.76. Close eligible raw25033.34/926634.36:
| sector | reset raw | nonreset raw | reset paid | nonreset paid |
|---|---:|---:|---:|---:|
| MED |19280.61|5752.73|827.00|2014.36|
| HIGH |893760.88|32873.48|8857.69|10434.15|
Reset pairs are immediate predecessors and both suffixes use p<=5; nonreset all earlier anchors. Nonreset one actual ordered anchor pair in each sector, max actual ordered product98/70.40, max used suffix sum r190/822; reset keys4/5, max raw product2016/1518.76. Nonreset portion after finite caps3738.36/22439.33, reset remainder18453.62/884903.19. These are raw cap checks, not comparison to previous quota/clock residual, not evidence of asymptotic convergence. Actual arithmetic candidates are far more numerous than realized pair keys in finite runs.

## 6. Remaining problem

The divisor argument gives a power saving for closely spaced nonreset anchors and extends the arithmetic control to small same-label mergers with two preceding large, possibly asymmetric incoming labels. To use it on the main same-label residual identified at f68d302, need control of pairs with reset anchors, one/both smaller earlier incoming labels, or longer gain since large anchors. It does not directly give an unconditional upper bound on the local heavy predecessor branch mass. Next can exploit the reset geometry (both physical clocks on one of two lines) or transfer medium/small incoming history into a suitable earlier nonreset anchor, but such a transfer has not been established here. Main untouched; Lean compilation and full twin-prime proof remain open.
