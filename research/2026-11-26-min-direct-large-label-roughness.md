# Deterministic roughness from large labels and low pre-deficit

Continuation of [62b9b73](https://github.com/tara-sooo/A166944-Lean/commit/62b9b7368758bf00495ed1eca4e670e9e2278a5e) on the independent direct-arithmetic branch. The previous rough-plateau clock theorem was conditional on roughness and small ordinary deficit. Here actual large labels relative to the pre-deficit force those hypotheses, with stronger class-dependent factor exclusions. A deterministic three-class alternative on every large crossed window follows from the dense barrier capacity. The result is necessary, not a contradiction with finite twins. No Lean kernel verification.

## 1. Large-label low-deficit criterion

At an actual event let (t,H) be the pre-plateau, n=t+w, e=+1 even or -1 odd, I=(1-e)/2, selected p, g=p-1, post Z=H+g. Let d=2t-H>=0, d'=2n-Z>=0 and D=d'-6I. Assume
    p>=47, p>=5d+15.                                      (A)
By the ordinary envelope, w>=(p-1-d)/2>=2d+7>2(d+3). Any prime f<=d+3 dividing either neighbor would be eligible (f<p) and give a clock within 2f, a contradiction. Thus neither neighbor has such a factor.

Put c=1-H mod4, k_f=1 for f=c mod4 and 3 otherwise. For every eligible factor f, f>d+3, the exact clock formula of 62b9b73 applies: S_f=k_f*f+6I_f, w_f=(S_f-d-1)/2, where I_f=0 for even side and1 for odd side. The proof needs only f>d+3, not a separate lower bound L>=7. For odd f the signed defects at relevant ticks are c mod4, and the first positive multiple in that class is k_f*f; the inequality ensures it occurs strictly after the pre-plateau. Scores are distinct across the two sides by parity and within a side by primality. Consequently the winner has
    D=(k_p-1)*p in {0,2p}.                              (1)
All other eligible factors have score strictly greater than that of p.

## 2. Stronger roughness and selective exclusions

If k_p=1 (reset), then any prime f<=floor((p-7)/3) dividing either neighbor would be eligible (f<p), and its score would be <=3f+6<=p-1, a contradiction. Hence both neighbors have no factor <=L=floor((p-7)/3). Under (A) and p>=47, d<=L-3: indeed d<=(p-15)/5 and L-3>=(p-7)/3-4=(p-19)/3; for p>=47 the latter is >=(p-15)/5. Thus the exact rough low-deficit hypotheses of the preceding paper hold with this L.

If k_p=3 (nonreset), every prime f<p would be eligible. For f=c mod4 its score is <=f+6<3p, while for f!=c mod4 it is in the same class as p, hence f<=p-4, and its score <=3p-6<3p. Both contradict the winning score >=3p. Therefore p is the least prime factor of the product (H-1)(H+1), not just of the selected neighbor. Here we can take L=p-1, with d<=L-3. Also EVERY eligible prime f in the reset class c satisfies
    f+6I_f>3p+6I,
    hence f>3p-6.                                     (2)
On the odd winning side the bound improves to f>3p (or f>3p+6 for even competitor). For the reset winner the corresponding exact inequality is k_f*f+6I_f>p+6I. These inequalities concern eligible factors only; a very large prime cofactor may be ineligible and is not subject to (2).

Thus the previous conditional score classification is now obtained from a checkable deterministic condition on an actual path. In the nonreset case it also yields a strictly stronger least-factor statement than the older generic w/2 roughness bound.

## 3. Consequences for composite cofactors

Assume (A), D=2p, and put H-e=pq. Every prime factor of both neighbors is >=p. If p^3>H+1, q is prime since a composite q would have at least two factors >=p and H-e>=p^3. Both neighbors have at most two prime factors, counted with multiplicity. This cube threshold has constant1, in contrast to the earlier general long-wait certificate p^3>512(Y+1); it applies to the special low-pre-deficit nonreset class.

If p^4>H+1, both neighbors have at most three factors. If a neighbor has exactly three factors, ALL are eligible: if one exceeded sqrt(H+1), the product of the other two would be >=p^2>sqrt(H+1), giving a product >H+1. So (2) applies to every reset-class factor of a triple.

If the selected neighbor is H-e=pab (a,b prime, repetitions permitted), the following refinements hold:
* Odd winning side e=-1: q=ab=3 mod4, since p!=c mod4. Thus exactly one of a,b is in class c. It is >3p-6, and the other is >=p. Necessarily H+1>p^2(3p-6). In particular the odd nonreset cannot select a balanced triple with all factors p+o(p) in this fourth-root regime.
* Even winning side e=+1: q=1 mod4, so a,b are in the same mod4 class. If both are in class c then H-1>p(3p-6)^2. Otherwise both are in the nonreset class (same class as p) and this extra product bound is not asserted.

The q congruences are direct: if H=0mod4 then p=3mod4, and if H=2mod4 then p=1mod4. Dividing H+1 by p gives q=3mod4 in either case, and dividing H-1 gives q=1mod4. These restrictions do not exclude all type-III events. The targeted controls below show both stated asymmetric triple configurations can actually occur at abstract plateaus, satisfying the true minimum rule.

## 4. Deterministic window alternative with rough low-deficit states

Take the high-far events and exact barrier notation from cafea3c: fixed eps in (0,1), lambda>1, crossed window [X,lambda X] on an infinite canonical ray, R=floor(c0 log X) for 0<c0<1/(8log2), P_R odd prime product, alpha_R=product (p-1)/(2p). Far means outside the previous near-square band, hence q-p>2sqrt(eps*p) for sufficiently high H. Write G for total gain, N_g,N_c for high-near gain/count. The residual L0=G-N_g-2P_R(N_c+1) satisfies L0>=((lambda-1)/2-o(1))X. The high-far events jointly cover at least alpha_R L0/2 barriers. For any subset covering B barriers its gain F and count m satisfy
    F>=2B, F+2P_R*m>=2B/alpha_R,
    m>=(2B/alpha_R)/(sqrt(lambda X+1)+2P_R).
These are the exact capacity inequalities of cafea3c (with harmless use of sqrt in place of integer floor).

For sufficiently large X, R>=47. Partition the high-far events into three disjoint classes:
 A0: condition (A), D=0;
 A1: condition (A), D=2p;
 B: failure of (A), so d>(p-15)/5.
At least one class covers >=alpha_R L0/6 barriers. It follows that in EVERY sufficiently large crossed window one of the three classes has, simultaneously,
    m>=((lambda-1)/(6sqrt(lambda))-o(1))*sqrt X,
    F>=((lambda-1)/6-o(1))*alpha_R X,
    F+2P_R*m>=((lambda-1)/6-o(1))*X.                   (3)
The class may vary between windows. For A0 or A1 the count gives that many distinct actual pre-plateaus satisfying the previous rough low-deficit hypotheses, with roughness cutoff at least floor((R-7)/3), and stronger p-dependent cutoff as in section2. A0 normalizes to distinct canonical roots within seven ticks (up to one pending at window endpoint); A1 has d'>=2p and selected p is the least prime factor of both neighbors. For B each PRE-plateau is distinct and has d>(p-15)/5. In particular sum of these pre-deficits is >=(1/5-o(1))*F, as p>R->infinity. This last charge uses only pre-deficits, so no two events charge the same plateau.

Conditional consequences: if all pre/post ordinary event-plateau deficits in a sequence of such windows are o(log X) uniformly, every high-far event satisfies (A) and is a reset (D=2p would violate the post bound). Then ALL the high-far capacity bounds of cafea3c apply to actual rough low-deficit reset plateaus. More generally if the number of canonical visits is o(sqrt X) and the number of high-far events failing (A) is o(sqrt X) along a sequence of windows, A0 has count o(sqrt X) by normalization, B has count o(sqrt X), and both have barrier capacity o(alpha_R X). Then A1 alone satisfies the original full residual lower bound asymptotically, i.e. m>=((lambda-1)/(2sqrt(lambda))-o(1))*sqrt X, F>=((lambda-1)/2-o(1))*alpha_R X, F+2P_R*m>=((lambda-1)/2-o(1))*X. All these events choose the globally least factor and have D=2p. No condition on previous information exposed is inferred: the deterministic plateau hypotheses do not justify applying the formal fresh-residue law repeatedly on a fixed integer path.

This advances the earlier question of when rough low-deficit plateaus are forced: either many such plateaus occur, or many pre-plateaus have deficit comparable to or larger than their selected prime. It does not eliminate class B, force a positive-density set of such plateaus on every ray, or force an eventual stop. Under finite twins all sufficiently large canonical roots have infinite paths, so the alternatives apply to each of them. No contradiction with that hypothesis yet.

## 5. Diagnostics

[Audit eb5dc52](https://github.com/tara-sooo/A166944-Lean/blob/eb5dc520a02574002c2492c1f06f44513a8e9601/research/min_direct_large_label_roughness_audit.mjs), blob d12bb56a2957eb21ccb5ab8c52bf5a5f0a6ae5a4, exact remote readback. Run node research/min_direct_large_label_roughness_audit.mjs 150000 180. Actual ECMAScript execution in tool runtime, not a separate Node process.

All 74,998 odd M=5..150000, at most180 events: 1,630,951 actual events, 74,951 terminated before the cap, 47 cap-unresolved. Four cutoff partitions for each root, 299,992 checks; 114,887 high-label failures of (A) checked against the exact pre-deficit inequality. In addition 9,405 abstract actual rough starts H=10000..200000 (d=0,2,6) satisfying (A), with 1,157,220 literal GCD ticks. Combined canonical and abstract runs and two targeted controls: 48,524 qualifying events (27,617 resets,20,907 nonresets), 158,051 factor roughness checks,14,197 competing score checks,19,662 nonreset prime-cofactor checks,93 nonreset selected triples in the fourth-root regime. Counts are overlapping event incidences, not distinct initial states. 39,117 qualifying incidences belong to the canonical scan; no actual canonical odd asymmetric triple is claimed.

Two targeted abstract controls outside the original SPF factorization range, 141 candidate tests and 143 additional literal GCD ticks:
    H=399828,t=199914,p=47,e=-1,w=73,
    H-1=487*821, H+1=47*47*181;
    H=1335600,t=667800,p=47,e=+1,w=70,
    H-1=47*157*181, H+1=103*12967.
Both have d=0,D=94, p^4>H+1, and meet the corresponding odd/even product restriction. These are actual minimum-clock events from abstract starts, not asserted canonical ancestry. All final assertions passed. The finite cutoff audit checks the partition and deficit charge, not an empirical verification of a macroscopic crossed-window asymptotic. The capacity inequality (3) is a paper deduction from the earlier verified dense-barrier estimate. No new external novelty claim, no Lean verification. Main and siblings unchanged.

Next target: analyze the transitions between these deterministic rough low-deficit states and class B pre-plateaus. In particular it would be useful to obtain a constraint linking repeated low-pre-deficit nonresets (which choose the global least prime factor) to the subsequent deficit dissipation, rather than another marginal lower bound alone.
