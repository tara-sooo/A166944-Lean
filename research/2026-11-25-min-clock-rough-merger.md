# Rough incoming merger sieve and pointwise rare-state energy caps

2026-11-25 JST. Continues 4580e75ba854faf268cd3f48335dac94ea2d17af (direct partner quotas), 2c5f5f0b1852ada0bc0837ab279a302e92981ff5 (destination-weighted formation), and bc057caad390631a6a94b6bcab5ca3bb690c0fb6 (wide LOW transfer). Uses the elementary Selberg calculation already developed in parallel note 711a0db7df0d2920f15f6f071718f924ce4938f2, research/2026-11-25-min-prime-root-local-repeat.md. NEW arithmetic bounds for mixed near-B incoming reset states with one or both rough predecessors, and for same-label physical mergers preceded on at least one branch by another near-B label. These bounds pay capped actual future pair energy, not just rare-vertex counts. Neither full sector bound nor twin infinitude proved. No Lean compilation.

## 1. Setup

Dyadic X,N=X/2 odd roots M in [X,2X), B=ceil(sqrt(7X)), H=4B,a=2B, s=M+2,C0=2M-2,K=floor((7M-1)/4). H+2B<=min(K-s) eventually. Original MIN prefixes through first state at or beyond relative H or twin terminal. Strict C and t growth; C<=2t, deficit 0<=2t-C<=12B+6; total gain <=G=2H+B+6. A selected p costs gain p-1 and wait<=2r(C)<=2p, where r(C) is least eligible odd prime <=B dividing (C-1)(C+1). All horizons in [2X,7X); selected weight <=1.5G per source. Fractional weights w_M(C) are original waits clipped to relative slab [a,H) divided by 2r(C), or any smaller nonnegative mask. R=sum r sum w<=NB, E=sum r(sum w)^2. At a final occupied C, first physical meeting of two synchronized tags occurs at a unique (t,J) with J<=C, including root/final states. All histories are natural prefixes, even under masks.

Put u=log B, ell=log u, l=1+ell, P=ceil(B/u^(1/8)), A=u^(1/8). Here HIGH incoming means selected p>=P, not the high-sector final label cutoff T=B^1/4. Call a HIGH incoming edge ending at J ROUGH if r(J-p+1)>=p/A. This is a condition on its predecessor horizon, NOT the occupied final horizon C, and NOT a lower bound on actual wait. Its predecessor neighbors have no odd prime factors <p/A. We do not delete all nonrough incoming edges; their later common suffix may be long.

## 2. Uniform elementary sieve used below

For an integer parameter range of length V and d in {2,3,4} linear forms, suppose each prime l0 in a chosen set <=Z excludes exactly d residues. For all sufficiently large B take Z=floor(B^1/16). The dimension-d Selberg quadratic upper bound is O(V/G_d(Z)+Z^6), G_d(Z)=sum over allowed squarefree n<=Z of product_{l0|n} d/(l0-d). For completeness, restrict primes to >d; take g(n)=product d/l0, h(n)=product (l0-d)/d. Main quadratic term diagonalizes as sum h(j)Y_j², Y_j=sum_{j|n}lambda_n g(n). Choosing Y_j=mu(j)/(h(j)G_d(Z)) gives lambda_1=1 and main term 1/G_d. Inversion gives |lambda_n|<=product (1-d/l0)^(-1)<=n. CRT residue error bounded by O(Z^6) using d^omega(lcm(n,m))<=nm and sum_{n<=Z} n²=O(Z³).

If the allowed primes are all u²<l0<=Z except divisors of a nonzero integer of logarithm O(u), the missing primes above u² have reciprocal sum O(1/(u ell)). Mertens' product estimate yields G_d(Z)>> (u/l)^d: restrict the Euler product to primes <=Z^c for fixed small c>0, use probability d/l0 of including each prime, and Markov on log n (expectation O(c log Z)) to retain at least half of product mass on n<=Z. If d=2 and all odd primes <=Z are allowed, then G_2(Z)>>u² by the same argument. Hence survivor counts O(V(l/u)^d+ B^3/8), or O(V/u²+B^3/8) for the latter case. The parameter intervals below have lengths bounded above by V=O(X/(kp)) or O(X/q), or dyadic length R>=P/2; in each case the chosen upper bound V is >=c B/u^1/4, so the error is absorbed. Shorter true intervals are bounded by enclosing intervals of those lengths. No trajectory independence used.

## 3. Mixed high incoming reset states: three nested envelopes

Suppose distinct p,q>=P enter the same physical state v=(t,J). Write s0=t mod 2, eps=6s0. The exact MIN clock congruences give p,q | J+2s0 and 2pq | (2t-J-eps). Since 2P²>12B+6 eventually, delta=2t-J=eps. Thus t=(J+6s0)/2, J+2s0=kpq, integer k>0 (even in actual horizons), k<=K0=(7X+2)/P²=O(u^1/4). No extra factor B/P for t in this mixed case. Count candidate vertices by ordered labels and k, allowing overcount.

(A) No roughness assumption. For each p,q, O(X/(pq)) possible J, including endpoint rounding since X/(pq)>=c>0. Elementary prime reciprocal bound sum_{P<=p<=B}1/p=O(l/u) (split dyadically). Therefore number A0 of possible mixed-high reset states is O(X l²/u²).

(B) At least one rough incoming label. Fix that label p, cofactor k and side s0; write eta=2-4s0, D_p=J-p+1. The predecessor neighbors are p(kq-1) and p(kq-1)+eta. Necessarily the three forms in variable q

    q, kq-1, p(kq-1)+eta

avoid all odd primes <=Z, eventually Z<P/A. For primes l0>u² exclude divisors of k p (p-eta); all three roots are distinct otherwise (eta=+-2). The excluded nonzero integer has logarithm O(u), uniformly k,p. Section 2 gives O((X/(kp))(l/u)^3) candidates q in the enclosing range q<= (7X+2)/(kp); bound q<=B as well but do not need it. Sum over k<=K0 using sum 1/k=O(l), then p>=P using sum1/p=O(l/u). Consequently

    A1=O(X l^5/u^4).

This improves the basic envelope by two logarithms up to l factors, not merely one.

(C) Both incoming labels rough. Also q(kp-1) and q(kp-1)+eta avoid small factors. In the q-sieve add the fourth form (kp-1)q+eta; the constant kp-1 is itself rough. Four residues are distinct after additionally excluding primes dividing
    (kp-1)(kp-1+eta*k)(kp²+eta-p).
All factors nonzero for sufficiently large p. The determinant of third and fourth is kp²+eta-p, and substituting q=1/k in fourth gives (kp-1+eta*k)/k. The omitted product has log O(u). The four-form count is O((X/(kp))(l/u)^4).

Moreover the fixed p is prime and kp-1 is rough (from the other predecessor). For each k apply dimension two to p and kp-1 on dyadic subintervals of [P,B], with primes >u² (k<=O(u^.25)). Uniformly each such subinterval of scale R has O(R(l/u)^2) candidates, so the reciprocal sum of these p is O(l³/u²) instead of O(l/u). Summing the four-form upper bound against this restricted reciprocal sum and sum_k1/k gives

    A2=O(X l^8/u^6).

This is a double sieve, not a product of assumed independent event probabilities. The envelopes are nested A2 subset A1 subset A0. They count possible physical vertices, not actual source mass or pair count. The extra p-sieve is essential for the u^-6 exponent.

## 4. Same incoming label: two-step rough envelopes

Consider first physical merger at (t,J) with common incoming p>=P, rough at D=J-p+1. The two preceding physical states are distinct times at the SAME D (otherwise they physically met earlier). Suppose at least one predecessor was itself entered by a high q>=P; then q | D or D+2. No requirement q labels differ between branches.

Fix q and side s1 in {0,1}; D=q n-2s1, n even. The neighbors D+-1 avoid odd primes <=Z by roughness of outgoing p. For n=2m the two forms have distinct roots at all odd primes <=Z because q>Z. Section 2 full two-prime-residue sieve counts O(X/(q u²)) such D. Sum q>=P gives O(X l/u³) possible D, overcounting choices of q. At any D, the number of high p dividing D+-1 is O(1) by product bound and log P~u. For fixed D,p, output J determined, t in deficit strip and single allowed residue mod 2p; at most O(B/P)=O(u^1/8) times. Thus candidate physical state count

    A3=O(X l/u^(23/8)).

If the earlier high q is ALSO rough at its own predecessor E0=D-q+1, then E0+-1 equal q(n-1) and q(n-1)+eta1, eta1=2-4s1. We have four forms in n (or n=2m)
    qn-2s1-1, qn-2s1+1, n-1, q(n-1)+eta1.
They have distinct roots except primes dividing q, 2, or pairwise differences among constants -2s1-1,-2s1+1,-q,-q+eta1 after multiplying the third form by q. All such differences nonzero eventually, their product has log O(u). Section 2 using primes >u² gives O((X/q)(l/u)^4) admissible D. Again sum reciprocal q and count O(1) p and O(u^.125) output times. Thus nested envelope

    A4=O(X l^5/u^(39/8)).

This covers the same-label merger even if only one of its incoming histories has the earlier rough high q. The other history is arbitrary. It does not require the two steps to be consecutive on both branches, only actual q immediately preceding p on at least one. The full enumeration may include vertices with no actual merge. All bounds count physical states, not root tags, and no actual cap on their mass follows.

## 5. NEW capped actual future energy from rare physical states

For each final horizon C and each actual first physical merger v, let B_c(v,C) be the ordered sum of w_i(C)w_j(C) over distinct pairs with first physical merger v belonging to class c, optionally reduced by arbitrary prior fractional pair exclusions. Thus this is twice the sum over unordered pairs. Class partition: mixed distinct high labels, neither rough (c0), exactly one rough (c1), both rough (c2); same rough high label with earlier high q on at least one branch, no such q rough (c3), at least one such q rough (c4). Distinct classes may have candidate state envelopes overlapping, but pair assignments are disjoint. Count by A0..A4 above (nested envelopes suffice for exact classes).

For any cap K_c>0 at each v,C pay min(B_c(v,C),K_c) of that ordered pair weight, for example proportionally within that cell. The energy paid is r(C) times this amount. For a fixed v, all tags visiting it share one deterministic continuation until their individual cutoffs. Their union of later occupied states is a prefix of the longest such actual continuation, because time cutoff is the only source dependence until the original prefix crossing or common twin. Sum r(C) over this union <=sum selected p<=1.5G=O(B). This applies even if previous exclusions or final sector masks make arbitrary holes in the occupied subset. Consequently

    E_paid,c <= K_c sum_{v in A_c} sum_{C after v} r(C)
             <= 1.5 G K_c |A_c|.                       (1)

No raw mass cutoff, no lower tail threshold, and no need to multiply by number of evaluation horizons. The proof is for synchronous pair energy AFTER first physical meeting only; projected asynchronous overlaps are not included.

Use caps K0'=u^(19/4), K1'=u^(27/4), K2'=u^(35/4), K3'=u^(23/4), K4'=u^(61/8). (K0' denotes cap, not cofactor maximum.) By (1) their respective paid energy bounds are
    O(XB u^(11/4) l²),
    O(XB u^(11/4) l^5),
    O(XB u^(11/4) l^8),
    O(XB u^(23/8) l),
    O(XB u^(11/4) l^5),
all o(XB u³). Valid for either final MED or HIGH sector, indeed any fractional mask, and can be combined with previous quota union by applying caps to the remaining pair weights. For the covered classes a positive unpaid contribution at v,C now requires aggregate actual ordered pair product (before this new cap, AFTER any applied prior exclusions) >K_c. It does not require each individual predecessor group large, nor imply that the full residual energy is negligible. In particular both-rough mixed incoming mergers admit a much larger cap than the no-rough case. There is no estimate here for generic smaller incoming p or for all pairs at a rare vertex with arbitrarily large product.

For MED, using the polynomially relaxed target from 2c5f5f0, z largest cutoff with L_z<=B^1/16,T=ceil(B^1/4), the bounds just obtained are more than sufficient for the paid terms (the same logarithmic caps used in audit for both sectors). One can also increase MED caps by B^5/8, preserving o(XB^(13/8)u³) by (1); not numerically tested. Joint residual targets remain natural E_m,rest=o(XB^(13/8)u³) and retained E_h,rest=o(XB u³), with correct LOW destination-loss accounting. This is not a new independent bound on MED or HIGH.

## 6. Verification

Standalone research/min_clock_rough_merger_audit.mjs, final exact readback 14e5337531665db6423aa8a76ffe537de73c5c9a, blob 40ce1e7d5f074da1644a241d54383ca460b87df6. Run:
    node research/min_clock_rough_merger_audit.mjs 1024 4096 16384 65536
All 16 final runs (four windows x four modes) executed in available ECMAScript runtime in batches, not a separate Node invocation. Reuse previous direct-quota independent pair-prefix intersection and cohort union, now record first physical time, incoming p,q and immediately prior incoming labels. Enumerate all arithmetic reset candidate states by factoring J or J+2; enumerate same-high candidate states via D,D+2 and exact output clock residue in deficit strip. Check actual first pairs belong to correct envelope, exact three/four forms and distinct residue counts at finite nonexceptional primes, two-step forms, cap per vertex/C, sum of r over actual used suffix states, independent raw cap partition and prior-quota residual partition. Floating tolerance used. These finite tests do not prove asymptotic sieve cardinalities. Analytic P near B, no positive-energy pairs in these five new classes in tested windows; analytic quota residual already zero. Diagnostics P=ceil(B/4), A=2; wide P=ceil(B/8), A=2; stress P=ceil(B/32), A=4, same previous quota parameters as standard diagnostic. These are finite stress choices only, not asymptotic thresholds; reset-only mixed classification in all modes, nonreset mixed pairs if any left unpaid. No other cumulative prior root/energy exclusions. The two-step test checks residue rank using the equivalent scaled form q(n-1), not a separate numerical Selberg implementation.

Largest X65536,B678: standard candidate state counts (nested) [4009,237,6,7835,692], 2772 mixed residue tests, 17067 two-step tests. Only actual class c4 positive (raw MED 8007.39, HIGH88491.07); already entirely paid by prior cohort and quota union. Wide [10294,746,28,29676,2471], 8857/28618 tests; same result, no incremental saving (raw c4 MED9866.11,HIGH92046.55). Analytic [0,0,0,29,0].

Stress largest P22: candidate state counts [34765,5728,416,622907,143602]; 37681 arithmetic mixed label pairs, of which 6121 at least one rough and 420 both; 26448 mixed and 48397 two-step residue tests. All actual mixed-high pairs reset in these finite runs, but proof only requires eventual reset at analytic P. Stress prior residual identical to standard diagnostic, 72644.62 MED and 884732.13 HIGH. Extra only c4: MED raw547477.15, residual before cap35787.20, paid2471.22, unpaid within c4 33315.98; HIGH raw3592187.77, residual before cap318806.18, paid10656, unpaid within c4 308150.18. Overall residual MED70173.40, HIGH874076.13, additional 3.40% / 1.20% of previous respective residual. Stress c4 cap12 in ordered pair-weight units, not an asymptotic cap. Other stress mixed classes positive raw (MED1259.36/2268.47/1792.74, HIGH4705.28/4198.53/2344.67), all prior paid. Max actual raw c4 ordered product4555.37 MED /9300.75 HIGH, max used suffix sum r265/1619, respectively. The sharper both-rough sieve cap is a paper result not a finite large-cap improvement, because analytic cases are empty. Standard and wide have no additional finite saving; do not claim otherwise.

## 7. Next step

The main new arithmetic saving is A2=O(X l^8/u^6), versus O(X l²/u²) for unrestricted mixed near-B incoming resets; A4 improves A3 when the previous high incoming edge is also rough. The energy caps can be much larger without losing the cubic-log saving. Finite data indicate that the next substantial residual is not near-B mixed high incoming: same-label mergers with smaller labels and repeated attachments on low/medium clock histories remain. Need a bound on actual mass products or dense arrival sequences, not a further count of already covered near-B mixed reset states. Main untouched; no Lean compilation; full proof open.
