# Reset-anchor ancestry: long entry waits and short nonreset predecessor excursions

2026-11-25 JST. Continues 01a2afcdf80c128207aab767c50619ece5025d6f (close asymmetric deficit divisors), e15eb81dd0e0e1fe2b98086421b9c5023fd2f313 (rough merger sieve) and f68d30207d956f9ad45f7a1b3ecf7eaf78a804a9 (local predecessor weights). New: distinguish actual long and short entry waits into a RESET anchor. Long waits imply rough predecessor; short waits imply a previous nonreset deficit near the incoming prime, permitting a divisor count if another high anchor occurred recently. A short high reset also requires a long gain excursion since the last reset. These estimates do not bound arbitrary reset ancestor masses, and do not prove the remaining energy targets.

## 1. Setup and geometry

Use all-odd canonical MIN short-clock prefixes with X dyadic, N=X/2, B=ceil(sqrt(7X)), H=4B, a_slab=2B, G=2H+B+6, initial C0=2M-2,t0=M+2, original K=floor((7M-1)/4). Same cutoff assumption H+2B<=min(K-t0) as previous notes. Include the first post-state at/beyond relative H or twin terminal. C and t strictly increase, C<=2t, gain<=G, deficit delta=2t-C in [0,12B+6]. Each selected p has actual wait<=2r(D)<=2p<=3(p-1), D pre-horizon. Full selected weight per root<=1.5G.

For an incoming labeled anchor (J,t,p), s=t mod2, p>=7, we have p|J+2s, delta=6s+2pk with k>=0 integer. Also J=2k mod4: from t=(J+6s)/2+pk and t mod2=s, since p odd. RESET means k=0, hence J=0 mod4 and t=J/2+3s. The two reset lines therefore have a discrete common horizon grid, and at each horizon each line admits at most O(log B/log Q) labels p>=Q by factor counting. For two reset anchors with |J'-J|<=A, their time gap automatically <=A/2+3. Under the previous short geometry Q>A+2 and Q> Z+A/2+3, distinct physical close anchors have distinct labels. We will only use pairs with |t'-t|<=Z, but for counting neighbors it is enough to impose the horizon condition.

Let u=log B, ell=1+log u, P=ceil(B/u^1/8), Q=ceil(B^3/4). More generally use P>=Q>=7 with log P, log Q comparable to u. Fix wait threshold V>=1 and previous-anchor gain threshold Dmax>=0 satisfying P>2V+5Dmax+7. Denote current high reset anchor alpha=(J,t,p), p>=P, its actual predecessor horizon D=J-p+1 and entry wait w. Distinct original tags arriving by the same labeled anchor may have different entry waits and preceding histories. Classify individual tag incidences, not every tag at the anchor identically.

## 2. Long entry waits: one-anchor roughness suffices

If w>V then r(D)>V/2. For fixed p and s put J+2s=pm, m even. The two predecessor neighbors are p(m-1), p(m-1)+eta, eta=2-4s. Thus m-1 and p(m-1)+eta avoid odd prime divisors <=V/2 (up to integer endpoint). For V=floor(B^1/16), choose sieve cutoff B^1/32, eventually below V/2 and p. In variable m/2 the two forms exclude two distinct residues modulo every odd prime in that range, because eta=+-2 and p is invertible. The elementary dimension-two Selberg upper bound already used at e15eb81 gives O(X/(p u^2)+B^3/16)=O(X/(p u^2)) candidates for J (parameter interval length O(X/p); error absorbed). The allowed t is unique for each s. For P=B/u^1/8 up to rounding, sum_{P<=p<=B}1/p=O(ell/u). Therefore

    N_long = O(X ell/u^3).                            (1)

This is an arithmetic upper bound on labeled high reset anchors with a possible long-wait predecessor; it does not depend on actual visit multiplicity. In particular a long-wait anchor on only ONE branch is enough, the other close reset anchor need not have a rough predecessor. Long here means absolute actual wait>V, much weaker than relative roughness r(D)>=p/u^1/8.

## 3. Short entry waits: recent high ancestor divisor

If w<=V, then

    delta_D=2(t-w)-D=p-1+6s-2w.

Suppose there is a previous incoming anchor beta=(E,t_E,q) on this same actual source path with q>=Q, E<=D and e=D-E<=Dmax. Allow E=D (the immediate predecessor itself). Put l=(t-w)-t_E. Then 0<=l<=3e. If s0=t_E mod2, its deficit is

    delta_E=p-1+6s-2w+e-2l,
    n=(delta_E-6s0)/2=q k0.                           (2)

From the threshold condition, 0<n<p. In particular k0>=1: the recent earlier high anchor MUST be nonreset. Also q!=p. This conclusion is independent of the intervening labels and does not require an actual long-wait lower bound at beta.

Fix p, s, s0, even e in [0,Dmax]. All possible n lie in the integer interval

    ceil((p-1+6s-2V-5e-6s0)/2)
         <= n <= floor((p-1+6s-2+e-6s0)/2).

There are O(V+Dmax+1) possibilities. For each n, its prime divisors q>=Q number O(u/log Q). Each such q determines k0. Since q|E+2s0 and E=J-(p-1)-e, the two congruences are
    J=-2s mod p,
    J=p-1+e-2s0 mod q.
Distinct p,q give O(X/(pq)) possible J. Parity and actual MIN transitions only reduce this count. Sum p reciprocals, and use q>=Q. Thus number of possible current high reset anchors with a short wait and a recent high ancestor satisfies

    N_recent <= O( X (Dmax+1)(V+Dmax+1) (u/log Q)
                     (sum_{P<=p<=B}1/p) / Q ).        (3)

At the stated P,Q this becomes O(X(Dmax+1)(V+Dmax+1) ell/(Q u)). This counts even reset states where the same physical anchor is reached by a different long-wait path. The witness can vary per tag. We do not count arbitrary short resets with no recent high ancestor by (3). Divisor enumeration is on a nonzero integer of size O(p), not the vanishing current reset deficit.

## 4. Excursion from last reset, also for short-old class

Let F be the last reset vertex strictly before the current high reset, where reset in this statement means delta=6(t mod2), including original root (even if a small incoming label or no incoming label). The root has delta=6, so F exists. Let g=D-F be the intervening gain before the final high jump. The deficit at D is at least p-1-2V. Since delta_F<=6 and elapsed<=3g,

    delta_D-delta_F <= 5g,
    g >= (p-2V-7)/5.                                 (4)

With V=o(P), every short high reset requires gain Omega(p) since the preceding reset, BEFORE its own high jump. In particular, if all the intervening selected labels are <Q, it requires Omega(p/Q) such events (if Q large). The gain intervals from last reset to predecessor for distinct short-reset entries of the same source are disjoint, so their total g<=G and sum (p-2V-7)<=5G. This latter inequality is an excursion budget, not stronger in order than the full per-root high gain budget. It is useful because it excludes short reset-to-reset LOW blocks as a mechanism for cheap high entries when the LOW gain barrier is o(P). A recent high ancestor in (3) cannot itself be the last reset. A short entry not covered by (3) has either no earlier high anchor or all earlier >=Q anchors more than Dmax gain before D. (4) does not imply that the last high is nonreset or that any high occurred in the excursion.

## 5. Pair envelope and actual future energy

Consider distinct original pairs whose first physical meeting occurs after two chosen distinct close reset anchors, one incoming >=P, the other >=Q. Fix a deterministic assignment of anchors and orientation per pair, independent of final C; e.g. latest >=Q anchors strictly before first physical meeting, then orient by label>=P, tie by original source order. Audit restricts to same incoming label at the first physical meeting. Classify the oriented first anchor by that original tag's entry wait and recent ancestor (long, short-recent, short-old); if multiple tag pairs at the same anchor keys give different classes, treat them separately. Each anchor key has O((A+1)u/log Q) possible neighbor keys from the reset geometry. Thus for the first two classes, when log Q comparable to u, possible ordered pair key counts satisfy

    A_long = O((A+1) N_long),
    A_recent = O((A+1) N_recent).                      (5)

This multiplies by an upper bound on neighboring large factors, not an assumed independent prime density. This is why one-sided long/short-recent conditions suffice.

Fix a final C and weights 0<=w_M(C)<=natural relative-slab occupation (fractional or masked), R<=NB,E=sum_C r(C)(sum w)^2. For each ordered anchor pair key and class, take the actual assigned ordered product of tag weights at C, optionally after any prior fractional pair exclusions. Pay up to cap K_c of this product at that C (proportional allocation allowed). The deterministic first common physical state after the anchors is unique. All later occupied horizons for this key, across root cutoffs, lie in the longest realized common suffix. Sum r over these horizons<=1.5G=O(B). Hence

    E_paid,c <= 1.5 G K_c A_c.                         (6)

No uniform bound on raw visit mass is used, and no extra factor for #evaluation horizons. Only synchronous overlaps after first physical meeting are included. For long class set K_long=u^5/(1+A); for short-recent class K_recent=Q u^2/[(1+A)(1+Dmax)(1+V+Dmax)]. With V=floor(B^1/16), Dmax even of order B^1/16, A=2floor(u^1/8), Z=3A, (1),(3)-(6) give respectively

    E_paid,long=O(XB u^2 ell)=o(XB u^3),
    E_paid,recent=O(XB u ell)=o(XB u^3).

Here K_long has order u^39/8; K_recent has order B^5/8 u^15/8, a polynomial allowance even though BOTH current anchors are reset. Compare the previous unrestricted reset cap u^7/2 at the same A. For the MED target o(XB^13/8 u^3) one may multiply both caps by B^5/8, with the same savings. The previous natural MED and retained HIGH sufficient conditions, and the LOW destination-loss accounting, are unchanged. No cap for short-old pairs is asserted. Nor do the estimates prove that arbitrary actual products at long or short-recent anchors are below the stated caps. The audit takes class caps only for the first two classes; it does not combine the older unrestricted reset cap or other prior energy masks. These are independent upper bounds on portions of energy, not additive cumulative finite savings.

## 6. Verification

Standalone research/min_clock_reset_ancestry_audit.mjs, exact remote readback 6b118889cf9ff9a62d2e532757a9414a7ca9ae30, blob e684969a25aaa54f6052f70c330c56a380363efe. Run node research/min_clock_reset_ancestry_audit.mjs 1024 4096 16384 65536. Actual JS function executed in available runtime: 12 final successful runs (4 X windows x3 modes). Reuse independent canonical simulator and literal parity-GCD comparisons at X1024 (4658 per mode), raw sector occupation and actual first physical meeting. Independent relaxed short-recent envelopes: divisor n and CRT including mod4, versus direct horizon and prior anchor factor scan, exact agreement at X<=4096 all modes. Long envelope by factor enumeration and r>V/2, two-form identities checked. Actual tag entry classification, deficit equation, previous reset excursion, close pair keys and deterministic suffix sum, raw energy and cap partition checked. First version of arithmetic neighbor loop stepped by four from -A even if A was not divisible by four; corrected to -4 floor(A/4) before final runs. No limiting sieve inference from finite counts. In finite envelope current high anchor is additionally required to have pre-horizon >=2X, unlike previous relaxed all-anchor count, so totals need not match older arithmetic count.

Analytic P,Q,A as paper, V=1 and Dmax=0 at tested sizes; no eligible positive-energy pairs, growing asymptotic regime not reached. Diagnostic/stress use finite P=ceil(B/4) or ceil(B/8), Q=max(19,ceil(B/8)) or max(19,ceil(B/32)), V and Dmax adjusted to satisfy nonzero deficit condition, caps16/64 or8/16. Largest X65536,B678,N32768,794415 events,R402074. Analytic P537,Q133,A2,V1,Dmax0: actual high reset incidences1455 (long1439, short-recent0, short-old16); candidate close pairs1827, long1827, short-recent2. Diagnostic P170,Q85,A12,V8,Dmax12: reset incidences11949 (long10876, short-recent162, short-old911); arithmetic close-pair total177732, long59313, recent45035; these envelopes overlap. Eligible actual reset raw MED1670.96/HIGH2210.05 entirely long, paid582.19/2064.18. Stress P85,Q22,A4,V7,Dmax10: reset incidences19706 (long17374,recent930,old1402); 2332 short excursion checks, min observed gain/p=0.28037; arithmetic pair total203017, long67548,recent145360, overlap allowed. Independent short envelope shortKeys42441, 52800 divisor tests, max one allowed factor, 73250 CRT insertions before dedup. All these are counts of keys or incidences as indicated, not distinct roots. Actual close reset pairs raw MED19280.61/HIGH893760.88; long raw19150.33/893692.03, paid824.94/8857.69; short-old raw130.29/68.85, short-recent raw0 in all tested windows. Thus short-recent entry condition is directly exercised but no positive close-pair energy exercises its cap in these finite runs. Previous reset cap was not cumulatively applied; no new numeric reduction of previous quota residual claimed. At X4096 diagnostic independent short keys540 exact; actual recent entries10. At X16384 diagnostic recent109; stress143.

## 7. Remaining

Reset pairs with one long entry have two extra logarithms in candidate count up to factors from neighbor enumeration. Short-recent entries have a polynomial factor from the prior nonreset deficit even when current anchors lie on reset lines. Short-old entries require a long excursion since last reset, but neither its actual multiplicity nor the large products at these pairs are bounded. Need a separate argument on large group formation along those excursions (or alternative linear budget transfer). No complete energy estimate, no Lean compilation, main unchanged.
