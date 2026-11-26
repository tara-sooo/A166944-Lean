# Hypothetical infinite MIN worlds X: cofactor transition capacity and large-denominator diversity

2026-11-26 JST. Independent continuation of [9733fd2](https://github.com/tara-sooo/A166944-Lean/commit/9733fd234d882609b87ad2cef1fba038f93b5935). Sources: [III clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), [V semiprime entry sieve](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md), [IX rational clock](https://github.com/tara-sooo/A166944-Lean/blob/9733fd234d882609b87ad2cef1fba038f93b5935/research/infinite-orbit/rational_clock.md). Sibling preflight direct [d422023 causal recycling](https://github.com/tara-sooo/A166944-Lean/blob/d422023036a9cb61ebe6e87890fa28dcecf21ae9/research/2026-11-26-min-direct-causal-recycling-scale-and-stratum-transport.md), unified [9737845 residence and matched-pair capacity](https://github.com/tara-sooo/A166944-Lean/blob/973784527ec9195ff4b74e891032ea5bbaab0eb2/research/2026-11-26-min-unified-matched-residence-return.md). The complementary large-denominator regime of IX is examined without imposing a small multiplier, a small deficit, or a long clock. The new support is the actual selected-neighbor cofactor, not the prime label support or the ending-height support. Paper deductions plus actual finite diagnostics; no Lean verification or external novelty claim.

## 1. Cofactor coordinate and denominator

In an actual contiguous adaptive MIN block with pre-horizons H in [X,lambda X), lambda>1 fixed, choose ANY ordered list of complete events with T<=p<=B, where T>=eta sqrt X, eta>0 fixed, B=floor sqrt(lambda X+1). No restriction on waits. Use g=p-1, e=1-2s, post (J,n)=(H+g,t+w), s=n mod2. Define
    a=(J+2s)/p = (H-e)/p+1.
This is an even positive integer. It is the selected-neighbor cofactor PLUS ONE. Adaptive eligibility p²<=H+1 implies (H-e)/p>=p: if e=1, H-1>=p²-2 and its divisibility by p>=3 excludes any smaller multiple; if e=-1 this is immediate. Therefore
    p+1<=a,   (X-1)/B+1<=a<=Lmax=floor((lambda X+B+2)/T).
In particular a=Theta_(lambda,eta)(sqrt X). If mu=(n-2s)/(J+2s) has reduced denominator b, write
    m=gcd(J+2s,n-2s)/p,    a=b m.                    (1)
Here m is a positive integer, not the earlier adjusted-deficit multiplier h. A large denominator b>=beta T for fixed beta>0 leaves only O_(lambda,eta,beta)(1) possible m, because Lmax/T is bounded. In this range b is close in order of magnitude to the largest possible denominator. The case Q in IX (small denominators) and this large-denominator case are not exhaustive; intermediate denominators are retained via the exact weighted count below.

## 2. Cofactor transitions and the odd nonzero shift

For consecutive selected events with prime labels p,r, cofactor coordinates a,b0 (b0 is NOT the reduced denominator), and arrival sides s,t, let E be total intervening UNSELECTED horizon gain. It is a nonnegative even integer. The physical post-horizon difference is E+r-1. Hence
    (b0-1)r-a p = E-1+2(t-s).                         (2)
The right-hand side is odd and never zero. This is true for short, positive-drift, long and reset events alike, including arbitrary actual relays.

For fixed a,b0 and sides, write d=gcd(a,b0-1). It is odd. If E<=K, any solution must have d<=K+3 since the nonzero right-hand side has absolute value <=K+3. Also admissible E are in one residue class mod d, giving at most floor(K/d)+1 values, even before imposing their even parity. At fixed E, the solutions of (2) in integer p,r form one affine lattice with p-step (b0-1)/d. The p-interval has length <=B. Since b0-1 >=(X-1)/B, B²/(X-1)<=2lambda for all sufficiently large X. Thus at most (1+2lambda)d solutions for each E. Multiplication yields
    # candidates <= (1+2lambda)(K+d) <= 3(1+2lambda)(K+1).
If no solution, the bound is trivial. Sum the four side choices to obtain a uniform constant C_lambda=12(1+2lambda) such that
    N_(a,b0)(K) <= C_lambda(K+1).                    (3)
Here N_(a,b0)(K) counts actual consecutive selected pairs with the indicated ordered cofactor pair and E<=K on ONE physical ray. Every integer candidate (p,r,E,s,t) specifies the first physical pre-horizon H=p(a-1)+1-2s, which cannot recur along a strictly growing ray. The bound is therefore valid on actual pairs even without checking time or primality of candidates. This is not an independent-product assumption or a probabilistic model. It is different from a fixed-prime-pair CRT estimate: p,r are both allowed to vary over the full band; the fixed coordinates are the cofactors. No assertion that every lattice candidate is feasible.

The parity in (2) matters. If the right side could vanish, d could have square-root size even at E=O(1), allowing a whole diagonal family. It cannot vanish for actual MIN gains and sides.

## 3. Global transition moment and cofactor diversity

Let k be the number of selected events, n=k-1 when k>=1, F their total gain, U full complementary gain in the block, S the number of distinct selected cofactors, P the number of distinct ordered cofactor pairs actually appearing consecutively (P<=S²). If n=0 the bounds with n² are trivial. All n relays are disjoint, with sum E<=U. From (3), for any integer K>=0,
    n <= C_lambda P(K+1)+U/(K+1).                   (4)
A useful sharper integrated statement does not need to choose K. For a single ordered cofactor pair with N occurrences, sort their relay gains E_1<=...<=E_N. Equation (3) gives i<=C_lambda(E_i+1). Therefore
    sum E_i >= N(N+1)/(2C_lambda)-N.
Sum once over the actual ordered pairs, then apply Cauchy-Schwarz:
    U+n >= sum N_pair²/(2C_lambda)
        >= n²/(2C_lambda P).
Consequently
    n² <= 2C_lambda P(U+n) <= 2C_lambda S²(U+n).       (5)
This is a paid transition-capacity bound independent of the number or values of selected prime labels, time phases, deficit variation, or adjusted multiplier. In particular, F<=k(B-1), n>=F/(B-1)-1. In a macroscopic block F>=rho X with rho>0 fixed, n=Theta(sqrt X) because T=Theta(sqrt X), U=O(X), and (5) implies
    U >= c_(lambda,eta,rho) X/S² - O_(lambda,eta)(sqrt X).
If S stays bounded, a macro selected population requires macro complementary gain. If U=o(X), the actual ordered cofactor-pair support must diverge, even for an all-fast deep population. If U=O(sqrt X (log X)^A) for fixed A>=0, then
    P=Omega(sqrt X/(log X)^A),
    S=Omega(X^(1/4)/(log X)^(A/2)).
No bound on actual S or P is forced by finite twins. Large cofactor diversity remains compatible with all these inequalities.

There is also an original-tag version. For arbitrary nonnegative weights on actual lists, sum (5) in square-root form:
    sum_i w_i n_i <= sqrt(2C_lambda (sum_i w_i P_i)
                                         (sum_i w_i(U_i+n_i))).
This is Cauchy-Schwarz with the actual per-tag quantities, not a count of physical states multiplied by source multiplicities. It permits shared physical paths; it cannot automatically charge the same gain a second time to a different selected list on that tag. For short lifetimes H_life with F_i on order H_life, the exact count lower is n_i>=F_i/(B-1)-1, not Theta(sqrt X) unless H_life=Theta(X). The bound then scales with H_life²/B² in place of X. It does not automatically imply a macroscopic missing-wait estimate in unified.

## 4. Transfer to large reduced denominators

Let D be the set of distinct actual reduced denominators in the selected list (not slopes). By (1),
    S <= sum_(b in D) floor(Lmax/b) =: D_weight.     (6)
This weight is only an upper bound on cofactor support; repeated cofactors across different denominators can reduce it. Insert D_weight for S in (5). When all selected denominators b>=beta T,
    S <= floor(Lmax/(beta T)) |D| = O_(lambda,eta,beta)(|D|).
Thus a macroscopic population of high events with large denominators and bounded denominator support cannot have U=o(X), regardless of the numerator/slope diversity or fast/long mixture. More quantitatively under U=O(sqrt X (log X)^A) it requires
    |D| = Omega(X^(1/4)/(log X)^(A/2)).
The weighted form remains valid when denominators are smaller; e.g. at b>=T/(log X)^L the lower on |D| weakens by at most O((log X)^L). Unlike IX, the argument does not constrain motion between nearby rational slopes by Farey spacing. It constrains repeated use of the integer denominators themselves at large scale. A model using many different denominators can evade it.

## 5. Repeated same cofactor and upward label price

Fix one actual cofactor a. Its successive visits have strictly increasing p: the post corrected horizon J+2s grows strictly between high post-states because their horizon difference is at least T-1>2. Therefore on a ray the same (a,p) cannot recur, and for two visits with the same a the later r>=p+2. If these are consecutive in the selected list (any intervening physical events are counted in E), (2) gives
    E=a(r-p)-r+1-2(t-s)
       >=2a-r-1 >=2T-B+1.                           (7)
In a narrow band B<=(2-eps)T this is at least eps T+1. Hence successive selected high events cannot share the same cofactor by a fixed bounded low-only relay for large T. Repetition with other selected cofactors between is not excluded; the interval then includes their gains and cannot be charged to U. For adjacent same-cofactor pairs all relays are disjoint, so their count times the positive part of 2T-B+1 is <=U. This result applies even when the two selected clocks are fast, unlike the earlier long-to-unit return charge. The constant can be sharpened using the actual a,r,s,t.

## 6. Additional positive-clock cofactor sieve

For every actual square-root-scale high event with strictly positive ordinary drift 2w>g, any prime factor f<(p-1)/4 of H-1 or H+1 would be eligible and have a future clock <=2f<(p-1)/2<w. Thus all neighbor factors are >=(p-1)/4. At sufficiently large X, if the selected cofactor q=a-1 were composite, H-e=pq>=p((p-1)/4)^2 would exceed lambda X+1. Hence q is prime, q>=p>=T, and the opposite neighbor pq+2e is rough.

Fix one a with q=a-1 prime and one side e. For varying p in [T,B], both forms p and q p+2e avoid every odd prime f<=z=floor(T^(1/24)), eventually. Their roots modulo f are distinct because q>z and e=+-1. Apply the translated two-form upper Selberg bound used in V and the direct localized supply estimates: pad the p-interval to O_(lambda,eta)(sqrt X) integers, the error z^6 is absorbed by the main O(sqrt X/log² X). Thus per cofactor and both sides there are O_(lambda,eta)(sqrt X/log² X) possible positive-clock occurrences on one strictly increasing ray, each gain O(sqrt X). If q not prime, none for sufficiently large X. The total positive-clock gain among any actual selected cofactor support S_up satisfies
    F_up <<_(lambda,eta) X |S_up|/log² X.            (8)
This is the cofactor analogue of the direct fixed-label rough-clock supply bound; in (8) labels may vary arbitrarily. At the large-denominator scale (6), macro positive-clock gain requires Omega(log² X) distinct reduced denominators supporting those positive events, WITHOUT a small-U hypothesis. If all selected high gain is macro, U=o(X), and the cofactor support is bounded, (5) already rules it out even if all selected clocks have nonpositive drift. If the cofactor support grows, (8) requires more diversity specifically on the positive-producing population when that population is macro. No claim that the actual cofactor or denominator support is small, or that this new support bound and previous label/height supply bounds add as independent resources.

## 7. Finite diagnostics

Final [cofactor_support_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/1c4e7f300bf9d8ed968bcffaae83652ea12e5f2f/research/infinite-orbit/cofactor_support_audit.mjs), blob261abefd13efb79abe2ef0253f7b73beccc3d8ae, exact remote readback. Run node research/infinite-orbit/cofactor_support_audit.mjs. Actual ECMAScript in available tool runtime, not separate Node. Final assertions pass. The first draft erroneously applied the high-only Lmax to ALL small-prime events; restrict that test to p>=T, retaining exact decomposition for every event. No change to the paper hypothesis.

Windows X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1), lambda=4,C_lambda=108. All 64,512 canonical roots in these windows plus 16,702 targeted intermediate starts obtained from feasible high clocks at sparse horizons, using shortest and longest waits and five arrival-position samples. Targeted starts are actual valid states in the necessary envelope but not known canonical ancestry. Total 81,214 start incidences, 80,858 finite stops, 356 upper exits, zero cap-unresolved; 1,761,174 actual events. High visits 99,339, including 45,367 positive-drift and 34,783 with x>=X/4. Large denominator b>=T/2: 72,243 visits. 141,060 factor roughness tests and 37,441 prime-cofactor tests under the explicit finite cube-exclusion hypothesis; the other finite positive events are not claimed to have prime q by that test. 176 independent literal tick gcd controls.

Separate denominator distributions (source-incidence counts, not distinct physical states):
| X | canonical high | canonical b>=T/2 | targeted high | targeted b>=T/2 |
|---:|---:|---:|---:|---:|
|4096|3911|2604|6200|5421|
|16384|12317|8196|10273|8859|
|65536|48328|31398|18310|15765|
At largest X the canonical counts for b<=2, 2<b<T/2, T/2<=b<T, b>=T are respectively 16894,36,516,30882; targeted counts 0,2545,1011,14754. The targeted construction is deliberately not representative of canonical root probabilities. These are finite sample distributions, not asymptotic estimates.

Five actual selected lists per path (all high, b>=T/2, positive drift, fast 4w<=g, narrower p<=1.5T). Across the 166,941 nonempty lists/configurations, 122,013 consecutive pair checks of (2), odd shift and gcd; 122,013 ordered relay-cost controls, 834,705 tail checks at K=0,4,16,64,256, 67,888 nontrivial moment checks, 166,941 denominator-support checks. Maximum observed multiplicity of a fixed ordered cofactor pair within one list is 1, so the repeated-pair asymptotic regime is not exercised by these finite actual paths. Independently enumerate ALL integer p,r in the high band for 120 sampled fixed (a,b0,s,t,K) lattice problems (including nonprime candidates) and verify (3) and its single-side upper bound. This verifies a finite necessary-candidate count, not exact MIN realization or the asymptotic constant. 152 repeated cofactor visits on full high lists have upward label, 22 adjacent same-cofactor incidences across the five lists, 2 within narrower band; all meet (7). Counts overlap across configurations and shared physical states.

Representative canonical large-denominator consecutive pair at X4096: pre H=4398,t=2202,p=53,w=79,s=1, post J=4450,n=2281, cofactor a=84, denominator84; next selected pre H=4452,t=2286,p=61,w=95,s=1, post J=4512,n=2381, cofactor74, denominator74. Relay E=2 and 73*61-84*53=1=E-1. Both events actually have positive drift; source canonical. Representative deep fast large-denominator state from arbitrary intermediate start: pre H=4208,t=9212,p=61,w=1,s=1, post J=4268,n=9213, cofactor70, denominator70, adjusted deficit14152. Thus the large-denominator regime genuinely contains local deep fast events; the theorem constrains their repeated supply, not their individual feasibility. Representative same-cofactor pair from intermediate start: a=90, p=71 then r=73, sides1 then0, E=110; the reduced denominators differ (90 then3). This shows why a and the reduced denominator are not interchangeable without (1).

## 8. Remaining obstruction

The high-deficit survivor of VI/IX is further constrained by a cofactor transition moment valid for all clock types, and large-denominator concentration at a bounded support is incompatible with macro high gain and negligible complement. Positive ordinary drift has an independent rough semiprime cofactor diversity condition. These are new necessary conditions, not a forced exclusion of large-denominator trajectories. The unrestricted support case remains large: the inequalities allow both p and a to vary over square-root-scale sets, with arbitrary many denominators. A next direction is to use the coupled label/cofactor graph and the same-label/same-cofactor repetition costs to find joint restrictions when both coordinates change, or construct a relaxed integer model that satisfies these new pair budgets alongside the earlier scalar constraints. No full all-constraint infinite model, general uncapped run bound, Lean verification or finite-twin contradiction. Main and sibling branches unchanged by this work.
