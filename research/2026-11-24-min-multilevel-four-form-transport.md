# Multilevel projected concentration and four-form transport budget

2026-11-24 JST. Continues 3161a8e895e32debd3842053c2c5fb62db3fc610 on the SAME research/min-cycle-forest-2026-11-24 branch. New paper deductions using the standard dimension-four upper-bound sieve and exact finite audits. No Lean compilation. The final concentration bound and twin-prime infinitude remain open.

## 1. Setup

Use the canonical MIN sources, odd M in [X,2X), dyadic X divisible by four, N=X/2, B=ceil(sqrt(7X)), original start t0=M+2, C0=2M-2, cutoff K(M)=floor((7M-1)/4). All actual pre-event horizons are even in [2X,7X); r(D) denotes the least eligible odd factor <=B of D-1 or D+1, zero if none. Fix LOW7, L=210. Consecutive high selected keys (q,D) and (p,C), with p,q>7, satisfy
    C=D+d, d=q-1+g, 0<=g<L even,
    q | D-1 or D+1.
All source tags and original cutoffs are retained; keys group different clock times of the same selected prime at the same horizon. The LOW-only barrier gives gain <L and cost <3L/2 per low block. Use the preceding note's arithmetic S_key=sum_{p,D eligible}r(D)=O(XB/log^3 B) (also for the high-key restriction). The sum of actual r-costs prior to any stops is R_pre.

## 2. New uniform four-form arithmetic transport estimate

Define A_min by summing min(r(D),r(C)) over every odd prime 7<q<=B, even eligible D in [2X,7X), even 0<=g<L with C=D+q-1+g<7X. There is NO factor counting possible current p; when r(C)=0 the summand is zero. This overcounts all possible actual consecutive high-key transitions. For a fixed q,g, sign sigma, write D+sigma=q h, D restricted to one even progression of step 2q, so the available integer variable interval is of length O(X/q) and can be embedded in an interval of length comparable to X/q>=cB. The shift d=q-1+g is fixed and >2.

If min(r(D),r(C))<=q^(1/4), the total contribution for fixed q,g,sign is O(X/q^(3/4)). Otherwise all four neighbors D-1,D+1,C-1,C+1 avoid primes <=q^(1/4). On the progression, omit primes dividing 2q d(d-2)(d+2) and primes <=5. For each other prime ell<=z with z=q^c, fixed sufficiently small c>0, the four forbidden residues are distinct. This follows because the four affine expressions have common invertible slope mod ell before dividing any by q, and their pairwise differences are in {+/-2,+/-d,+/-(d-2),+/-(d+2)}. It is equivalent to divide the known q-neighbor by q; q is omitted anyway.

Use the standard upper-bound sieve in dimension four (the general upper-bound sieve used in the previous two-form estimates, now with rho(ell)=4 off the omitted primes and zero at the omitted primes). For clarity, its dimension bound is uniform by Mertens since rho<=4 and ell>5. Take a sieve level D_sieve=q^(1/4), with z=D_sieve^(1/s) for a sufficiently large fixed s depending only on dimension four. The upper-bound fundamental lemma (or a Selberg upper-bound sieve with suitably small z) gives O(N0 prod_{ell<=z}(1-rho(ell)/ell)) plus remainder bounded by a standard weighted divisor sum; the CRT errors are O(4^omega(m)), and the usual upper-bound combinatorial coefficients are bounded by 1. Thus O(D_sieve log^3(2D_sieve)) is sufficient for the error, negligible against N0/log^4 q since N0 comparable to X/q>=c q. This is the standard upper-bound sieve, not a lower-bound prime tuple assertion.

The omitted-prime product costs at most O_L((log log(3q))^4). Indeed the product of the exceptional primes divides a nonzero integer O_L(q^4), and for ell>5, (1-4/ell)^(-1)=(1-1/ell)^(-4)(1+O(ell^-2)). Splitting exceptional primes at log(3q), Mertens bounds the small-prime part by O((log log(3q))^4), and the sum of reciprocals of the larger exceptional primes is O(1) by the bound on their product. Fixed small q are absorbed in the constant. The number of large-min candidates is therefore O_L(X (log log(3q))^4/(q log^4(2q))). Each costs <=q, because r(D)<=q. Summing fixed g and signs and then q gives
    A_min = O_L(X sum_{q<=B} q^(-3/4)
                 + X sum_{q<=B prime} (log log(3q))^4/log^4(2q))
          = O_L(XB (log log B)^4/log^5 B).
For the second equality, split at sqrt B, bound the small range trivially and use pi(B)=O(B/log B) for the large range. The first sum is O(B^(1/4)) even over all integers. This is two extra logarithmic factors, up to the exceptional-prime product, compared to the single-key cost S_key. No claim that every four-form shift is admissible: the sieve upper bound allows even inadmissible tuples, and omitting bad primes is a valid relaxation.

## 3. Uniform source-preserving transport bound

Consider any absorbing process in which each executed high key has mass strictly below U. The set of tags using a particular consecutive-key predecessor (q,D,g) is a subset of those executing (q,D). Even if those tags split by current prime p or clock time, each such tag contributes only once to this triple. Therefore, summing across all executed consecutive high transitions,
    sum_tags min(r(D),r(C)) <= (U-1) A_min.
This applies to previously marked, highly concentrated groups just as to new marks. It uses the cap on the PRECEDING key; no replacement of source multiplicity by a count of unweighted keys.

Fix a factor F>=1. Call a high-key arrival transported if it has a preceding high key and r(C)<=F r(D); otherwise call it rising (initial high arrivals included). For transported arrivals r(C)<=F min(r(D),r(C)), so their actual high-key cost is
    R_trans <= F(U-1) A_min.
The classification is on each tag, not the whole group. Two tags in one group can have different prior costs. This notion of transport refers to cost comparison, not physical non-splitting or a claim that the current mass equals the previous mass.

## 4. New two-tier first-heavy stopping process with a much larger transport cap

Take a lower threshold T=ceil(B log^2 B), upper threshold U=ceil(B log^4 B), and F=max(1, sqrt(log B)). Process horizons in increasing order with original clocks/cutoffs. At a proposed high group G(p,C), let m be its original-tag mass and a its rising-tag mass from section 3. Stop ALL tags of this group before its high event if either
    m>=U OR a>=T.
Otherwise execute all of them. All low events execute. This rule is deterministic given the prior history; every tag stops at most once. It preserves the original trajectories up to their stops, even though the second condition depends on the previous high key. The same final-stop-set interpretation as in the first-heavy process holds by induction in horizon; no reweighting.

For every executed high key, total mass <U and rising mass <T. Hence
    R_rise <= (T-1) S_key = O(X^2/log B),
    R_trans <= F(U-1) A_min
             = O(X^2 (log log B)^4/sqrt(log B)) = o(X^2).
The total cost of all LOW-only blocks is <=(3L/2)(N + (U-1)*#eligible_high_keys). Here #eligible_high_keys=O(X log log B) by summing O(X/p), L fixed. Thus this low cost is O_L(X + U X log log B)=o(X^2). In total
    R_pre=O(X^2/log B + X^2 (log log B)^4/sqrt(log B)
                      + X B log^4 B log log B)=o(X^2).
The same no-twin clock argument from the previous first-heavy paper gives #unstopped non-twin roots=o(X). If all original terminals are non-twin, N-o(X) roots must stop. Sufficient open target: prove that a fixed positive proportion of roots escape these two-tier stops on unbounded dyadic X.

This genuinely permits continued execution of some keys with mass between T and U, and rising arrivals are now only those with cost increase by a growing factor F, or initial high arrivals. The large cap U is two log powers larger than the old uniform cap. It does NOT prove that stopped mass decreases monotonically for every possible parameter change: allowing more earlier executions changes later groups. It does not by itself give a contradiction for hypothetical no-twin windows. The remaining obstructions are keys reaching the larger U and keys with at least T rising tags; the latter might include already concentrated incoming groups. For initial arrivals alone the mass <=floor(L/4)+1, far below T.

More generally U=B log^(5-epsilon) B and F=log^gamma B with 0<gamma<epsilon give the same little-o transport estimate. T may independently be B log^(3-eta) B for fixed eta>0 with positive exponent. The choice above is one explicit instance.

## 5. Improved multilevel first-mark theorem for rough-to-rough arrivals

For the exact first projected mark at ANY level k>=2, each newly marked tag's preceding high key had mass <k (previous note); initial tags have no preceding high key. For each (q,D,g) charge at most k-1 such newly marked tags across current p. If BOTH r(D),r(C)>=Z, q>=Z and the four-form sieve can use fixed z=Z^c, D_sieve=Z^(1/4) as in section 2, since X/q>=cB>=cZ. The uniform exceptional factor is O((log log B)^4). Thus the total number A_Z of candidate triples with both rough satisfies
    A_Z = O_L(X (log log B)^4/log^4 Z * sum_{Z<=q<=B prime} 1/q).
For Z=ceil(exp(sqrt(log B))), this is O(X (log log B)^5/log^2 B).
For Z=B^theta with fixed 0<theta<1, this is O_theta(X (log log B)^4/log^4 B), since the prime harmonic mass of [B^theta,B] is bounded depending on theta.

Hence at level k the number of first-mark tags whose OWN preceding and current keys are both rough is <=(k-1) A_Z. For dyadic levels k=2^j<=K, the total number of tag-level incidences of this type is <=2K A_Z (geometric sum, no extra log K). Taking K=log^(2-epsilon) B for the subpolynomial Z, or K=log^(4-epsilon) B for the power Z, gives o(X) total tag-level incidences, for any fixed epsilon in (0,2) or (0,4) respectively. This is stronger in the double-rough case than the previous one-rough theorem, which required kappa~log^(1/4) B. It does NOT cover new tags from cheap preceding keys just because another incoming class is rough; that would require additional congruences and source accounting. Nor does it make the high mass hierarchy up to U disappear.

There is also a weighted version valid at all levels: first marks at level k in the transported class have total current r-cost <=F(k-1)A_min, independent of previous concentration at smaller levels. Summing dyadic levels k<=U gives <=2F U A_min=o(X^2) for section 4 parameters, even including proposed stop groups. This is a sum over tag-level events, not elapsed time or distinct stopped roots. It gives a rigorous multilevel cost bound all the way to the larger threshold, without assuming equal size merges. The complementary rising-class marks remain to be controlled.

## 6. Exact finite audit

Executed the saved Node.js function body on X=256,1024,4096,16384,65536,262144:
    node research/min_multilevel_transport_audit.mjs 256 1024 4096 16384 65536 262144
Fixed LOW7, original cutoff tags. Four finite diagnostic modes (T,U,F) with b=max(2,floor(B/8)):
    (b,b,1), (b,2b,1), (b,4b,2), (max(2,floor(B/4)),B,2).
These are deliberately much smaller caps than the asymptotic choices. At every proposed high group, mark every newly reached dyadic mass level (levels through 2048 where applicable), checking previous mass <level and counting own preceding/current rough tags. Verify all selected-key congruences and LOW bounds, exact original-source conservation, exact split R_pre=R_low+R_rise+R_trans, both caps on executed keys, rising cost <=(T-1)*S_key, transport cost <=F*min-cost <=F*(U-1)*sum_min over distinct observed triples, and low-cost bound. For X<=16384 independently enumerate the entire candidate A_min universe with every even g<L; verify actual observed triples' summed min-cost <=A_min. For X<=1024 each mode independently verifies literal parity-GCD event and terminal decisions. The literal totals across four modes at X256 are 629+677+889+1064=3259, at X1024 3029+3478+3534+4127=14168, combined 17427 comparisons. Exact arithmetic in tested ranges. The baseline uniform cap (T=U) matches earlier first-heavy results. Full script and JSON read back exactly at ce21ebc528e05a01024f0cf4cc83b4ab4cdf6828.

At X262144, B1355, N131072, the diagnostic results:

|T|U|F|stopped tags|actual twin terminals|stop keys|executed high groups with m>=T|
|--:|--:|--:|--:|--:|--:|--:|
|169|169|1|32914|98158|167|0|
|169|338|1|28629|102443|142|144|
|169|676|2|25527|105545|123|256|
|338|1355|2|8124|122948|21|46|

All four have 0 non-twin terminals. At T169,U676,F2 all 25527 stopped tags are in groups stopped ONLY by the rising-mass rule, none by U. There are 51438 tag incidences executing high groups with m>=169 (not distinct roots). R_pre=81513577, R_rise=59097430, R_trans=13905719, R_low=8510428. At T338,U1355,F2 all 8124 stopped tags likewise stop only by the rising rule. This is a useful finite diagnostic of the remaining obstruction, not an asymptotic proof.

For T169,U676,F2, exact first-mark levels (tag-level incidences):

|level|first marks|rising|transported|both r>=31|both r>=ceil(exp(sqrt(log B)))|
|--:|--:|--:|--:|--:|--:|
|8|112500|86641|25859|4903|13145|
|32|95971|56509|39462|10663|26028|
|128|51184|24407|26777|9360|20354|
|256|6130|3225|2905|754|2198|

The levels count the same root at multiple thresholds, as intended. Rising and transported exhaust first marks; the rough columns overlap them, not separate categories. The finite table does not establish the analytic sieve constant or asymptotic rarity. Main unchanged, no new branch, no Lean proof.

## 7. Next proof task

The four-form estimate now controls transport COST for already concentrated masses and permits a much larger cap, but the two-tier process still needs an upper bound on the total stopped population. The actual missing estimate is for the T rising mass in a single proposed key, possibly transported intact from much cheaper keys, and for total mass reaching U. A direction is to exploit the mandatory large cost ratio in each rising arrival and the exact previous-key partition; study first upward cost crossings at high mass, preserving the prior key's source tags, rather than reapplying the low-level fresh-tag cap to already marked roots. One must not infer a monotone increase in cost along an arbitrary trajectory; decreases can occur, so simple telescoping of positive log-ratios alone fails. No final anti-concentration theorem is obtained.
