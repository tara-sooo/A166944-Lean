# Bounded-coefficient high-prime return relations and the LOW-gain resource

2026-11-25 JST. Continues c34e74f9b207268a65e0eaa872a2d883a292a4f7 on the SAME research/min-cycle-forest-2026-11-24 branch. Original elementary probability and arithmetic deductions, with finite shared-CRT path audits and modular subset-support checks. No Lean compilation. The clipped-height probability-tail criterion and physical far-coalescence deficit remain unresolved.

## 1. A relation for every consecutive pair of selections of the same high label

Use the common CRT ghost, including its infinite alphabet version, with elapsed integer time s, relative even horizon gain g, and initial residue c_p mod p at each odd prime. A high label is p>=z>=11; a LOW label is p<z. The entire path is considered through integer time U. As before, two successive selected clocks of p are separated by at least p-2. The total number of selections of p through U is therefore at most
    1+floor(U/(p-2)) <= M := 1+floor(U/(z-2)).
Let p be selected twice consecutively in its own list of selections, at times u<s. Between these events, let d be the total gain from LOW labels and n_q the number of selections of each other high q. All horizon gains are even. Immediately after p at u, its horizon residue is 0 or -2; immediately before p at s it must be +1 or -1. Hence necessarily
    p | d + sum_(q>=z,q!=p) n_q(q-1) - c,
    c in {-1,1,3}.
The choice c depends on the two divisibility sides. This uses all actual intermediate high selections, including repeats, and no assumption of fresh intervening labels. Coefficients satisfy 0<=n_q<=M. The integer on the right is odd and nonzero, regardless of d or the coefficient vector. The total intermediate horizon gain is at least p-1 by the prior even-gap return lemma. The new objective is to exclude SMALL LOW gain d even when the high gain is large.

For fixed integer R>=0 call a set of distinct high labels relation-bad if there exist a modulus p in the set, coefficients 0<=n_q<=M for all its other labels, an even d in [0,R], and c in {-1,1,3}, satisfying this divisibility. Zero coefficients are allowed. This is a conservative condition on the set of seen labels, much larger than the actual set of chronological return witnesses. If the set of all high labels selected by U is not relation-bad, EVERY actual consecutive return of any p>=z must have intervening LOW gain >R. This also covers chains in which all the intervening high events are repeats. If there are no high labels, the condition is vacuous.

## 2. First-seen count concentration

Use the filtration revealing low coordinates p<z at time zero and the actual tick-by-tick selected labels and common parity thereafter. By the exact history law, an unused q>=z has conditional selection probability at tick s<=U at most 1/(q^2-s+1)<=2/q^2, provided z^2>=2U. This upper bound is uniform even when smaller selected or unused primes are present. Let K_s be the number of distinct high labels first selected through s, and J_s=K_s-K_(s-1) in {0,1}. Then
    Pr(J_s=1 | history before s) <= lambda_z := 2 sum_(q>=z prime) q^-2
                                = O(1/(z log z)).
For every t>0, iterated conditional expectation gives
    E exp(t K_U) <= (1+lambda_z (exp(t)-1))^U
                  <= exp(lambda_z U (exp(t)-1)).
This is an exponential-moment bound for the first-seen count, not an independent Bernoulli model for selections. With t=1,
    Pr(K_U>K0) <= exp((e-1)lambda_z U - K0).
In particular for z=ceil(U/(log U)^b), fixed b>1, and K0=ceil(C_b (log U)^(b-1)) with a sufficiently large fixed C_b, the right side is exp(-Omega((log U)^(b-1)))=o(1). No lower bound on the number of high events is inferred from this upper bound.

The previous deletion/cutoff coupling also implies
    Pr(some selected q>=V by U) <= O(U/(V log V)).
For the theorem below take V=ceil(U), so this is O(1/log U). We may restrict all seen high labels to [z,V) at the cost of this probability, without conditioning the later first-selection probabilities on the good cutoff event.

## 3. Uniform arithmetic exclusion at the last first-selection time

Fix U,z,V,M,K0,R satisfying z^2>=2U, M<z, and R>=0. We count the event that the set of high primes actually seen by U is relation-bad, K_U<=K0, and all these labels are <V. Suppose there is a witness relation. Among the modulus p and the other labels with nonzero coefficients in that witness, take the label x whose FIRST selection occurred last in elapsed time. Such a label is unique (at most one selection per tick). At the tick s of that first selection, all other nonzero-coefficient labels and the modulus if different from x have already been selected. In the filtration of section2 these labels are known before s, while x is unused. The witness coefficients and d may depend on the future, so enumerate every allowable coefficient vector and d; do NOT condition on their actual future values. Labels previously selected but not used can receive coefficient zero.

Case A: x is the modulus p. Given the prehistory and the vector of coefficients on the previously selected high labels, the integer
    N=d+sum_(known q>=z) n_q(q-1)-c
is fixed, odd and nonzero. On the prehistory restrictions of at most K0 known labels, all <V, it satisfies
    |N|<=R+K0 M V+3.
It has at most O(1+log(R+K0 M V+3)/log z) prime factors >=z, and this number is at most one if |N|<z^2. For each possible candidate p the conditional first-selection probability is <=2/p^2<=2/z^2.

Case B: x is a summand q, with n_x>=1. The modulus p>=z is already known. Because 1<=n_x<=M<z<=p, n_x is invertible mod p. Given the prehistory, the chosen p, the coefficients on all known high labels, n_x, d and c, the witness puts x in ONE residue class mod p. The sum of x^-2 over integers x>=z in that class is at most
    1/z^2 + 1/(p z) <=2/z^2
by the decreasing-function integral bound. Counting integers rather than primes avoids requiring prime-distribution estimates in large-modulus progressions. The conditional first-selection probability of any such x is therefore O(1/z^2).

At each tick with the stated prehistory restrictions, the number of coefficient/d/c choices in Case A is at most 3(R+1)(M+1)^K0. In Case B also choose the modulus among at most K0 known labels and the new coefficient 1..M. These overcount even d and impossible choices; the overcount is harmless. Thus, writing
    Bfac = 1+log(R+K0 M V+3)/log z,
the probability of the restricted relation-bad event is at most
    O(U (K0+1)(M+1)^(K0+1)(R+1) Bfac / z^2).
We sum over ticks s<=U and apply the conditional bounds ONLY with the individual past restrictions, not conditional on the future event K_U<=K0 or on no large labels being selected later. Every witness on that future event has a last first-selection tick satisfying those past restrictions. This is why the adaptive choice of the high set does not invalidate the probability estimate. It also handles witnesses involving repeats of labels selected long ago. The earlier fresh-landing exclusion was restricted to a next fresh landing or its low continuation; the present estimate excludes simultaneous bounded-coefficient relations across the whole seen set.

Adding the two exceptional probabilities of section2 yields the unconditional bound
    Pr(any consecutive high return with intervening LOW gain <=R by U)
     <= exp((e-1)lambda_z U-K0)
        + O(U/(V log V)
             + U (K0+1)(M+1)^(K0+1)(R+1) Bfac/z^2).
The same bound holds for the larger event that the full seen high set is relation-bad. No LOW duration, terminal support, or total gain assumption is used in proving this bound.

## 4. Near-top cutoffs with a nontrivial first-seen budget

Take fixed 1<b<2, z=ceil(U/(log U)^b), V=ceil(U), M as above, K0=ceil(C_b (log U)^(b-1)). Then M=O((log U)^b), M<z, and
    D0=(K0+1)(M+1)^(K0+1)=exp(O((log U)^(b-1) log log U))=U^o(1).
For 0<=R<=U, R+K0 M V+3=U^(1+o(1))<z^2 for large U, so Bfac=O(1); in Case A there is at most one prime factor >=z. For any fixed epsilon in (0,1), R=floor(U^(1-epsilon)) makes the arithmetic error O(U^(-epsilon+o(1)))=o(1). Thus with probability 1-o(1), EVERY high return through U requires intervening LOW gain >U^(1-epsilon) up to rounding. The statement holds for every fixed epsilon, not a uniform assertion over all epsilon. This is a uniform near-linear gain threshold for a cutoff where the first-seen upper budget grows, unlike the old z=U/log^b U, b<3/4 repeat deletion where the first-seen upper expectation itself tended to zero.

One can make the threshold more explicit and closer to U:
    R_*(U)=floor(z^2/(U D0 log U)).
It tends to infinity, is <U eventually, and is U^(1-o(1)); indeed log D0=o(log U). The arithmetic error is O(1/log U + U D0/z^2)=o(1), even with R_*+1 in the numerator. The total failure probability is O(1/log U)+exp(-Omega((log U)^(b-1))). In the remainder write R=R_* or the fixed-power threshold. The use of R_* depends on choosing the deterministic C_b large enough for the count tail; no numerical value of C_b is needed for the asymptotic assertion.

For the quiet-gap criterion we specifically take 1<b<3/2, so K0=o(sqrt(log U))=o(T/w), with T=floor(Y sqrt(log Y)), w=2Y, U=T+w. Then z<Y eventually, log z/log(2w)->1, and all the previous gap-or-repeat test hypotheses hold. The unconditional arithmetic exclusion does NOT imply that all returns are rare: LOW gain may exceed R. Also the bound is not intended for a fixed power cutoff z=U^theta with theta<1, since K0 would be polynomial and the coefficient enumeration would be too large.

## 5. Resource ledger using disjoint return intervals per label

Let G_low(U) be the total actual gain of all selected labels p<z through U (sum of p-1), and let R_U be the total number of repeated high selections by U. On the good relation/count/cutoff event from section4, for each fixed p, the intervening intervals between its consecutive selected times are disjoint, so the sum of LOW gains in those intervals is at most G_low(U). Each such interval consumes >R of LOW gain. The number of returns of p is consequently at most
    min(floor(U/(p-2)), floor(G_low(U)/R))
with the latter a weak integer bound (strict >R can improve equality cases). Summing gives
    R_U^term <= R_U <= min(sum_(seen p>=z) floor(U/(p-2)), K0 G_low(U)/R).
The first bound is the old clock budget, the second the new LOW resource budget. In particular for k>0,
    Pr(R_U^term>k) <= Pr(G_low(U)>k R/K0)+o(1).
This is a conditional-in-resource improvement, not an unconditional vanishing bound for R_U. A sufficient additional condition is
    G_low(U) = o_prob(R sqrt(log U)/K0)
along a diverging sequence. Then R_U^term=o_prob(T/w). For b=5/4, K0=O((log U)^1/4), R=R_*, the sufficient resource scale is R_* (log U)^1/4 (constant factors harmless). Since R_*=U^(1-o(1)), any bound G_low(U)=O_prob(U^eta) with fixed eta<1 would be more than enough for repeat deletion. Neither such gain bound nor the weaker sufficient scale is proved. The original first-selection estimate for arbitrary smaller labels and their crude clock repetitions does not give this small total gain.

This resource can also be localized. Choose arbitrary p0 in [3,z]. Let N_big count LOW selections p0<=p<z, and G_small the total gain from p<p0. A return interval either contains one of the N_big events, or all its LOW gain is small-label gain. For fixed p, at most N_big of its disjoint return intervals can contain such a big event; the remaining ones each consume >R small-label gain. Thus on the same good event
    R_U^term <= K0 (N_big + G_small/R).
If A_U denotes elapsed time of LOW-active plateaux on [0,U], then G_small<=(p0-1) A_U: each selected p<p0 has an immediately preceding plateau of integer length >=1 on which a LOW label was eligible, and the charged plateaux are disjoint. This does not replace horizon gain by elapsed time without a label-size factor. It yields the alternative resource condition
    K0 (N_big + (p0-1) A_U/R) = o_prob(T/w)
for repeat deletion. It can be useful if a bound on actual larger LOW jumps is obtained independently. No p0 has been shown to make this condition hold unconditionally.

Combining the resource inequality with the preceding gap-or-repeat theorem, for fixed 0<delta<1 and integer k=o(T/w),
    Pr(sigma_Y>T)
     <= Pr(A_T>(1-delta)T)
        + Pr(G_low(U)>kR/K0)
        + o(1)
        + 2^k(1-c/2)^floor(delta T/w).
The last term tends to zero for such k. One may use the localized resource instead of G_low. This leaves two distinct quantities, actual LOW-active occupation and LOW horizon gain (or larger LOW jump count). We have not proved the required upper bounds on either. A proof along a diverging sequence would imply the clipped-height probability-tail condition by finite-time coupling. The physical far-coalescence upper estimate is still separately required for twin-prime infinitude.

## 6. Finite diagnostics

Saved research/min_ghost_high_repeat_relation_audit.mjs and research/min_ghost_high_repeat_relation_results.json, with exact remote readback at 9f05f2c2a73da1643c1fb1a65ff414cd9883a840. Run 512 fixed-seed shared CRT samples each for Y=53,199,797,1597,3203, finite V=8Y, T=floor(Y sqrt(log Y)), U=T+2Y. Diagnostic cutoffs z=ceil(U/log^1.2 U), ceil(U/log^1.4 U), ceil(T^.8) with min11. These are finite tests of identities and certificates, not tests of the asymptotic small-probability union bound (the latter uses cutoff V=U and a deterministic K0). For each actual return check time separation, intermediate total horizon gain, exact decomposition by LOW gain and high coefficients, relation for one of c=-1,1,3, and first-selection ordering of the last involved label. In the summand case check coefficient invertibility; in the modulus case check nonzero integer divisibility. Check disjointness of per-label LOW-resource sums. Compute conservative exact modular support for each seen target prime p (when number of seen high labels<=24; all tested paths meet this cap) by DP modulo p, including each other seen q with coefficients from 0 to its own clock bound 1+floor(U/(q-2)). For each reachable residue find the smallest nonnegative EVEN d producing one of the three target residues. This gives a pathwise lower bound on actual LOW gain of each return; it need not be attained by any chronological return path. Record the global minimum across target labels and compare with R=floor(U^.5), floor(U^.75), floor(U^.9), verifying the resource bound on every path certified free of the corresponding small relation. These certificates are weaker than actual absence of repeats and can fail when no repeat occurs. No resimulation of canonical source paths or Lean formalization.

At Y797,U3654,z293 (log^1.2 diagnostic):515 distinct-first high selections across512 paths,2 high repeats (both terminal repeats), with intervening LOW gains10 and642; minimum relation certificate fails at R60 in111/512 paths, although only one actual repeat has d<=60. This illustrates the conservativeness of the all-coefficient certificate. At Y1597,U7531,z352 (log^1.4 diagnostic),608 first selections,one high repeat, terminal, with LOW gain104 and high gain408; no actual small return at R86. At Y3203,U15506,z1022 (log^1.2 diagnostic),433 first high selections, no high repeat, maximum seven distinct high labels on one path; total LOW gain598646 across512 paths (mean1169.23046875). At R124, the conservative relation certificate is bad in67 paths, despite zero actual repeats. At z649 (log^1.4 diagnostic),572 first selections, no repeat, total LOW gain484780; at R124 certificate bad in114 paths. These numbers are finite empirical diagnostics, not probabilities bounded for the limiting CRT law. Zero repeats at largest tested Y is not a proof. The active diagnostic recorded in the script is a sum over completed plateaux only, not a substitute for the previous exact A_T or A_U including the final truncated plateau; no conclusion uses that field.

## 7. Residual

The new unconditional result excludes ALL bounded-coefficient small-LOW-gain relations among the seen high primes at suitable near-top cutoffs, rather than requiring a fresh high event immediately before each potential return. Its consequence for repeat counts is a resource bound; it still needs a sufficiently small actual LOW gain or a localized small-label gain/larger-jump estimate. The separate active occupation and physical far-coalescence tasks remain unresolved. No new branch, no main edit, no Lean compilation.
