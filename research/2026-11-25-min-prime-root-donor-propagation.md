# Long-return removal and iterative donor-interval propagation on actual MIN trajectories

2026-11-25 JST. Continuation of edffc2452cd543b45008a75db94da45f7314b244 on research/min-prime-root-repeat-energy-2026-11-25. Paper deductions, no Lean compilation, no external novelty claim. Uses the previous light-background support sieve, dense-return actual-source theorem and LOW absorption; does not assume the remaining moments, the far-coalescence bound, or ghost independence. Twin-prime infinitude remains OPEN.

## 1. Gain intervals and exact long-return deletion

Keep the actual canonical MIN prime-root ensemble M in [X,2X), N prime roots, B=ceil(sqrt(7X)), individual original cutoffs K(M), and r(C) the minimum eligible odd prime <=B. Write p_i for the selected prime at event i of a fixed root, g_i=C_i-C_initial for its PRE-event gain, and G for its total final gain. The intervals [g_i,g_i+p_i-1) are disjoint and adjacent in gain, irrespective of waiting time; their total length is G. The horizon invariant gives G=O(X) uniformly, so sum_M G=O(XN). The selected weight p_i is at most 3/2 times its gain and r(C_i)<=p_i. All sums of weights below count original source tags, including after physical coalescence.

For a nonfirst occurrence i of p=p_i let j(i) be the immediately preceding occurrence of the same label in its ORIGINAL event list. Its return span S_i=g_i-g_j includes the earlier p jump. The intervening donor interval is [g_j+p-1,g_i), with gain E_i=S_i-(p-1). For p>=5, endpoint signs give S_i+sigma_i-sigma_j a positive even multiple of p, hence S_i>=2p-2 and E_i>=p-1.

For a FIXED prime p, the intervals [g_j,g_i) of consecutive returns are disjoint (half-open), so their lengths sum to <=G. Consequently for arbitrary positive thresholds h_p,
    sum_{i:S_i>h_p p, p_i=p} p_i <= G/h_p.
Summing over labels gives total selected-prime weight <=G sum_p 1/h_p. This is a pathwise inequality, not a probabilistic estimate; a donor interval may overlap many different labels but there is no overlap loss within a label.

Take H=ceil(B/sqrt(log B)) and l=log log B, F=ceil(l^2) for large B. Mark every return with S_i>H p_i. Its weight summed over all sources is O(XN/sqrt(log B)), by pi(B)=O(B/log B). Also mark every return with S_i>F p_i^2; their weight is O(XN/l) by the prime reciprocal sum bound. These two tests remove both macroscopic gaps for high labels and much shorter absolute gaps for medium labels. No distributional assumption. The remaining return spans satisfy
    S_i <= min(H p_i,F p_i^2).

## 2. Bounded multiplicity of short donor intervals

A short return has p>=5 and S_i<=K p, where K>=2 is a separate integer span parameter, not K(M). Fix one actual donor event d of label q and pre-gain g_d in a source. Consider all short return endpoints i whose donor interval includes that event, i.e. j(i)<d<i.

For p_i in a dyadic band [U,2U), U a power of 2, their earlier endpoints g_{j(i)} lie in [g_d-2KU,g_d]. Earlier endpoints are distinct because an occurrence has at most one next occurrence of its own label. Consecutive such earlier endpoints are spaced at least U-1 in gain, since the earlier of them makes a jump at least U-1. Thus at most 4K+1 such short intervals of one band can cover a donor. This does not count the later endpoint as a donor.

For Q<=p_i<=B let b_top=3+ceil(log_2(B/Q)). At most A_top=(4K+1)b_top short intervals in these bands cover any one donor. The bound is valid for a donor of ANY size. Alternatively require comparable donors p_i<=D q, D>=1. Since q-1 is part of the donor gain E_i, q<=K p_i, so p_i in [q/K,Dq]. There are at most b_comp=3+ceil(log_2(KD)) bands. Hence a donor q can cover at most A_comp=(4K+1)b_comp comparable short endpoints, and their TOTAL prime weight is <=Lambda q, Lambda=D A_comp. These bounds hold simultaneously for all original paths and any subset of endpoints. There is no assumption that disjointness for one label transfers to other labels.

## 3. Two different propagation rules for an arbitrary marked seed

Given any source-tagged marked set S, let V(S)=sum marked p_i. Marking is accounting only; the events of the original trajectory, their donor intervals and original label occurrence numbers never change.

Rule A (aggregate donor gain, top band): add each as-yet-unmarked short return i with p_i>=Q for which sum_{j(i)<d<i, d in S}(p_d-1)>=p_i/K. Then
    V(new endpoints)<= K sum_{new i} sum_{marked donors d in its interval}(p_d-1)
                     <= K A_top V(S) = Gamma V(S).
Rule B (single comparable donor, all scales): add each as-yet-unmarked short return i if some marked d inside its interval has p_i<=D p_d. Choose one such donor for each new endpoint. The comparable interval count implies
    V(new endpoints)<=Lambda V(S).
Each round uses only the PREVIOUS marked set. Thus after t rounds the cumulative weight is at most (1+Gamma)^t times the initial weight for A, and (1+Lambda)^t for B. These are union bounds, not independence estimates. They cover overlapping return intervals and all ancestry multiplicities. Any finite chain of comparable short-return donor edges directed from an earlier event to a later endpoint and starting at a seed is marked after no more than its length in B rounds; every edge advances chronological event index. Rule A permits many small donors, even if none is comparable to the endpoint.

## 4. Seed costs and a diverging number of deletion rounds

Use Q=ceil(B/log B) as in the prior hybrid. Define a FAST seed as the union of:
- first k=floor(sqrt(log B)) uses per source and label;
- global long endpoints S_i>H p_i;
- actual light-background p>=Q return endpoints from 2d184f3 (background gain J=floor(log^(1/4) B) besides a largest intervening donor);
- all actual dense-word marked events from edffc245, using its own z=ceil(sqrt B), K_d,J_d~(loglog B)^(1/4).

For light returns we need selected-prime weight rather than only r. The exact same tuple count in section 2 of the prior repeat-energy note bounds the sum of p over possible endpoint pairs (C,p) by O(X (loglog B)^2/sqrt(log B)): for a dyadic p-band U count feasible pairs using the two-form sieve and CRT, then multiply by 2U. Counting the union of (C,p), not just C, is bounded by that argument's pattern sum. Each original source visits C at most once, so actual light endpoints have selected weight O(XN (loglog B)^2/sqrt(log B)). We do NOT claim that selected weights of all events at the relaxed light horizon set are small; the earlier r-cost deletion of that set is kept separately, and those extra events are not used as donor seeds. The dense-word theorem directly bounds selected weight. Therefore
    V_fast,0 = O(XN l^2/sqrt(log B)).

Choose K=D=max(2,floor((log l)^(1/4))) for large B. Rule A has Gamma=O(K^2 l). Set
    t_A=floor(l/(8 log(1+Gamma))).
Then t_A->infinity and (1+Gamma)^t_A<= (log B)^(1/8). The entire A closure through t_A rounds costs
    V_fast <= O(XN l^2/(log B)^(3/8))=o(XN/l).
In particular ALL short top-band returns whose gain is supplied sufficiently by globally first-use labels or any other FAST seeds are removed, even with many small intervening labels.

Now augment the A closure by the first adaptive k_p=k+floor(B^2/(p^2 l^2)) uses (existing inverse-square caps) and local long endpoints S_i>F p_i^2. The previous baseline sum and section 1 give total new seed weight O(XN/l). Call this the SLOW seed. Rule B has Lambda=O(K^2 log(2K)), so take
    t_B=floor(log l/(4 log(1+Lambda))).
Again t_B->infinity, and the cumulative B closure has weight
    V_marked=O(XN/l^(3/4))=o(XN).
Thus a growing number of propagation steps are covered, without requiring uniform smallness of the entire unlimited closure. Unlimited closure or a depth estimate large enough to cover every event is NOT established. Slow growth of K is chosen to ensure both round counts diverge. At finite tested B the asymptotic formula gives zero rounds; the separate diagnostics deliberately use three rounds.

## 5. Residual structure and continued hybrid implication

All previous accounting deletions can be kept. After the new marking, any unmarked nonfirst return satisfies the two long-span bounds from section 1. For an unmarked short top-band return, gain supplied by the A-closure through round t_A-1 is <p_i/K (assuming t_A>=1). It cannot be fed entirely by globally fresh donors: E_i>=p_i-1 and their first uses were in the fast seed. For an unmarked short return of any p>=5, none of its comparable donors is in the B-closure through t_B-1 (assuming t_B>=1). Therefore any backward path of <=t_B comparable short-return edges from such an endpoint cannot reach the slow seed. If it stops early at an unmarked predecessor, that predecessor must either have a nonshort return or have no comparable donor to extend along; it cannot be globally first-use. This leaves the intermediate-span class K p<S_i<=min(Hp,Fp^2), diffuse donor gain carried by smaller labels, or long chains of mutually supporting, previously used comparable labels. A locally singleton donor need not be globally fresh and is not automatically removed. No claim that every residual interval has a comparable donor.

All newly marked p>y events have count at most V_marked/3. For the existing growing LOW primorial L<=(loglog B)^(1/4), their extra LOW-block attachment cost is O(L V_marked)=O(XN/l^(1/2))=o(XN). The previous deletion of the full relaxed light horizon set still has its old r-cost and LOW count estimate, with no selected-weight bound needed. Thus the previous hybrid proof carries through with n_m(M,p) and W_h,late(C) now excluding the new marked incidences in addition to the previous ones:
    Z_m=sum_{M,y<p<Q} n_m(M,p)^2=O(N B log^3 B),
    E_h,late=sum_C r(C) W_h,late(C)^2=o(X^2 B)
on the SAME unbounded dyadic sequence would imply R=o(XN), hence twin-prime infinitude by the original clock contradiction. Both bounds still OPEN. This is a strict structural reduction of their incidence domains, not a proof of either moment. The clock-budget deletion need not bound the quadratic energy of the deleted part.

A further useful general formulation: for a chosen short span K and arbitrary marked set, any band family for which the aggregate donor-gain propagation multiplier times its seed cost is o(XN) permits the same type of deletion. The wide-band B rule avoids a log B loss by requiring comparable sizes. In contrast, blindly charging all overlapping donor intervals across all prime scales costs O(K log B) per donor and does not establish the desired saving.

## 6. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_donor_propagation_audit.mjs, exact remote readback at cccc79b59272066ff28856408e60aee9218de634, blob 2105b7af0846fad480038d9087b76972b6ad058e. Run:
    node research/min_prime_root_donor_propagation_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime (not separate Node). All prime roots, original cutoffs, exact SPF parity clock with 1724 literal parity-GCD comparisons per mode at X256/1024. For every p independently checks disjoint return spans, global and local long-budget inequalities, every short donor's total top-band and comparable coverage and selected endpoint weight, each separate propagation round, and the final residual span and preceding-layer donor conditions. The long-budget numerical comparisons use floating division with absolute tolerance 1e-7; actual event times, gain intervals, incidence counts and layer weights are integers. The residual energy uses exact BigInt. The prior light condition is checked from actual largest intervening donor; dense marked intervals are recognized directly by scanning actual high words. The audit does not enumerate the relaxed CRT support or independently prove the sieve estimates; those were established in the parent paper notes. All three modes at six windows passed, and full R reproduces prior prime-root audit at every window.

Analytic mode uses stated asymptotic caps (with finite small-log guards) and no positive propagation depth in these finite windows. The adaptive baseline already covers all events, so the residual is empty. Fixed diagnostic mode uses k=1, no adaptive extra, K=6,D=3,H=16,F=4, Q=ceil(B/log B), dense z=7,K_d=6,J_d=2, light J=12 and three A/B rounds. Wide mode changes Q to 7 to exercise aggregate gain propagation at smaller labels. These diagnostic parameters do not have the asymptotic guarantees of section 4. They are nonvacuous checks of the exact inequalities, not finite evidence of a calibrated o estimate. The diagnostic residual moment excludes p=3 only; it is not the full combined prior LOW/relaxed-horizon/near-origin partition.

| X | fixed A new counts (three rounds) | fixed B new counts | residual clock cost | residual high energy |
|--:|:--|:--|--:|--:|
|256|5,0,0|30,8,2|501|7|
|1024|0,0,0|82,8,4|1196|0|
|4096|16,0,0|744,126,55|9532|4686|
|16384|27,0,0|3451,697,208|43859|1456|
|65536|102,0,0|13334,2696,757|180048|5741|
|262144|195,0,0|58296,11409,3124|779374|132155|

At X262144, N=20390, original events=616116, R=16687054, total gain=19169594. Fixed global-long weight=1166937, newly added local-long weight after A=39336; A new prime weights 70633,0,0, B new weights 577836,88081,21212. A+B remove 50243+592923=643166 additional units of actual clock cost beyond the respective seeds. 79089 short returns, 5824 survive, none at diagnostic top Q=188; the high residual still has 9703 clock cost at other spans. Retained medium moment=90202. Max actual top overlap 2, comparable overlap 5 (not asserted uniform). Wide mode at same X: A adds 14181,302,5 endpoints (weights 375403,5122,87), B adds 32862,77,33 (weights 164312,561,173); 77 top-short endpoints survive, maximum coverage 5 in both classes. All modes include exact original source multiplicity. The finite samples exercise later rounds in both propagation rules, but do not establish disappearance of the residual or the growing-depth asymptotic.

## 7. Next target

The missing arithmetic is now concentrated in intermediate normalized return spans, short return chains that evade the seeds for a diverging number of steps, and short diffuse-donor returns fed by much smaller labels. A potentially useful next step is to derive a quantitative bound on the depth of comparable chains using actual source-weighted arithmetic (rather than an abstract unlimited closure), or to apply the rooted return equations to a dependency DAG after separating diffuse donor gain. For the medium labels, the local-long cutoff restricts the possible recharge multiples to O(p l^2) even for very high multiplicities, and the adaptive cap ensures large prior gain; these can be used in deleted-prime-shadow analysis. No proof of an aggregate contraction or of the residual moments. Main and other research branches unchanged.
