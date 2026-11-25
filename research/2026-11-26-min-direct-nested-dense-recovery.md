# Nested dense cuts: normalized recovery length and genuine ordinary-deficit reduction

Continuation of [db1b303](https://github.com/tara-sooo/A166944-Lean/commit/db1b3035c2b185b8b35873040ff4f171aacc6c82). The previous potential was tied to multiples of a small primorial K_S. We now normalize the count of ALL dense S-barriers and use a second smaller cutoff to bound local coverage. This strengthens the gain lower bound for the corresponding (larger) crossing-B population, and yields a conditional quantitative ordinary-deficit recovery theorem. It is not an upper bound contradicting finite twins, nor a Lean kernel verification.

## 1. Exact normalized dense-cut potential

Use adaptive MIN with even pre-horizon H, absolute pre-tick t, ordinary deficit d=2t-H>=0. An event has gain g=p-1, wait w>=1, post Z=H+g, d'=d+2w-g, side indicator I=0 even/1 odd, adjusted D=d'-6I. A1: p>=47, p>=5d+15, D=2p; A0: same size/deficit test, D=0; B: failure of the test at p>=47. Far and near are the established square-band classes for a fixed epsilon0 in (0,1). All ordinary deficits at canonical-ray plateaus are nonnegative. Each nonreset p>=5 has d'>=2p.

For integer S>=3 let P_S be the product of odd primes<=S, K_S=2P_S, A_S=product (p-1)/2 over these primes, alpha_S=A_S/P_S. Define the dense S-barrier family of nonnegative even J by J mod p in {0,2,...,p-3} for each odd prime p<=S. Denote by B_S(H) the number of these cuts in [0,H), for even H>=0. The half-open interval is important; landing on a cut is not crossing it. Every jump with p<=S crosses none. There are exactly A_S cuts in any period of K_S absolute horizon units. For any even endpoints H<=Z, the exact periodic discrepancy is
    |(2/alpha_S)*(B_S(Z)-B_S(H))-(Z-H)| <= K_S.       (1)
Let L(H)=2 B_S(H)/alpha_S, f(H)=H-L(H). Then f is periodic on the even horizon lattice with period K_S and has oscillation at most K_S, by (1) applied between any two even positions in a period. Set rho(H)=f(H)-min f, so 0<=rho<=K_S. This choice is explicit and finite; it differs from the previous strict-preceding-multiple distance. Define
    u=d+3+rho(H).
For c_S=B_S(Z)-B_S(H), the exact identity is
    u'-u=2w-W_S, W_S=2 c_S/alpha_S.                 (2)
All noncrossers increase u, regardless of ordinary deficit reduction. Also W_S<=g+K_S by (1), W_S<=g/alpha_S by c_S<=g/2, and
    W_S-2w = d-d'+rho(H)-rho(Z).                    (3)

For any integer 3<=Q<=S, S-barriers are a subset of Q-barriers. In particular an event crossing an S-barrier crosses a barrier of EVERY lower cutoff. By (1) at Q,
    W_S <= (alpha_Q/alpha_S)*(g+K_Q).               (4)
This is a simultaneous-cut comparison for the same jump, not a statistical assumption on phases. It will be useful when g>=S and K_Q=o(S).

## 2. Segmented exact recovery budgets

Fix integers R>S>=47. Let T=R/5+K_S, Phi=log max(T,u),
    ell=log(10/(1+5K_S/R)), gamma=log(3/2+K_S/T).
Mark ALL A1 events with p>R (count m). Remove unmarked A1 as separators, retain the consecutive segments containing marks, and trim a retained segment ending at the full block endpoint just after its last mark. All other retained segments end at the pre-state of a removed A1. This is exactly the segmentation of db1b303, now using the new rho. Each removed A1 starts at Phi=log T because d+3<=p/5, rho<=K_S. Each marked A1 increases Phi by at least ell since its post d'>=2p and its pre u<=p/5+K_S. Every negative change of Phi requires W_S>2w and thus c_S>=1, p>S.

Let Jset be the set of retained unmarked nonresets strictly decreasing Phi, j its count. These are all B: smaller A1 were removed, larger A1 marked, A0 is reset. For each v in Jset, writing l_v=Phi_pre-Phi_post>0,
    l_v <= gamma,
    T*l_v <= W_S-2w <= W_S,
    T*l_v <= d-d'+K_S.                            (5)
The first bound follows from W_S<=g+K_S<=p+K_S, post max(T,u')>=max(T,2p), and the logarithm ratio estimate; the others use log a/log b in the sense log(a/b)<= (a-b)/b, or directly log ratio<=positive drop/T of the truncated u. The final inequality uses (3). A reset q reducing Phi has loss <=log_+((q+6+K_S)/T) since d+3<=q+6. Count at most N+1 such resets in the block by the seven-tick normalization, where N counts actual canonical visits. Each is p>S>=47.

Let Delta be the sum of retained segment endpoint differences of Phi. If Y bounds the pre-horizons and C=floor sqrt(Y+1), then
    Delta <= E=log(max(T,2C+9+K_S)/T).
All segments ending at a separator have nonpositive endpoint difference, and the one possible final trimmed segment ends at an A1 with d'<=2C+6. Define Zloss to be the sum of the reset loss bounds just given, so Zloss<=(N+1)log_+((C+6+K_S)/T). Telescoping gives
    ell*m <= Delta+Zloss+sum_{Jset} l_v
           <= E+Zloss+gamma*j.                       (6)
The first inequality also proves, for Jset as above and F_J=sum g over Jset,
    T*(ell*m-E-Zloss) <= sum_{Jset}(W_S-2w)
                     <= sum_{Jset} W_S
                     <= min(F_J/alpha_S,
                         (alpha_Q/alpha_S)*(F_J+K_Q*j)), (7)
    T*(ell*m-E-Zloss) <= sum_{Jset}(d-d') + K_S*j
                     <= sum_{Jset}(d-d')_+ + K_S*j.   (8)
These finite inequalities remain true with E replaced by actual Delta; for subsets of Jset use the per-event gamma bound on the discarded log losses. This is an actual loss bound including waiting time, not simply a bound on cut length. No low-run error term is needed.

## 3. Global dense-barrier coupling and improved gain theorem

On an infinite canonical ray crossing [X,lambda X] for fixed lambda>1, let G=(lambda-1)X+O_lambda(sqrt X) be the first-crossing block gain, C=floor sqrt(lambda X+1). Use R=floor(c log X), 0<c<1/(8log2), S=floor(a log R), 0<a<1/(4log2), and Q=floor(b log S), 0<b<1/(4log2). For sufficiently large X, R>S>=47, 3<=Q<S. Elementary Chebyshev bounds give
    K_S<=2 R^(4a log2)=o(R), K_Q<=2 S^(4b log2)=o(S),
    P_R log X=o(sqrt X).
Consequently T~R/5, ell->log10, gamma->log(3/2); E,Zloss have the same O(log X), O((N+1)log X) bounds as before. All constants may depend on the fixed cutoffs' coefficients, lambda and epsilon0.

Let B denote the count of ALL far B events with p>S crossing at least one dense S-barrier, F their gain. This is a different population from B_K of db1b303: every multiple of K_S is a dense S-barrier, so B includes B_K, but it can also include events crossing other dense S-barriers. Let b_R be the number of dense R-barriers covered by high-far B with p>R, alpha_R their usual dense density. Because R-barriers are also S-barriers, all covering events are in B. The earlier dense R-barrier residual, the A1 gain ceiling 5G/14+O(C), and A0 normalization yield
    G/7-o(X) <= 2P_R*m + (C+2P_R)(N+1) + 2b_R/alpha_R,  (9)
    2b_R/alpha_R <= (C+2P_R)*B, 2b_R<=F.
Here the count m includes all A1 p>R, not just high-far. The residual lower bound G/2-o(X) follows from near square packing with O(sqrt X) near events and gain <=G/2+O(sqrt X), as in cafea3c. Using (6) with near recovering B count O(sqrt X) gives m=O(B+sqrt X+(N+1)log X), hence recovers the same count theorem
    N+B >= ((lambda-1)/(7 sqrt(lambda))-o(1))*sqrt X.
This count is weaker in its event restriction than the preceding multiple-cut count. The new result is its improved gain estimate and actual recovery constraints.

On a sequence of root-sparse windows N=o(sqrt X), charge near recovering B by gamma O(sqrt X) and far recovering B by (4)-(5). Their p>S ensures g>=S, hence K_Q/g=o(1) uniformly. It follows that
    ell*m <= (1+o(1))*(alpha_Q/alpha_S)*F/T
                 + O(sqrt X+(N+1)log X).
Substitute into (9), bounding 2b_R<=F, to get
    [alpha_R^(-1)+(1+o(1))*2P_R*alpha_Q/(T*ell*alpha_S)] F
         >= G/7-o(X).                              (10)
By Bertrand, A_R=alpha_R P_R>=c_1 R for some c_1>0 and sufficiently large R, so alpha_R^(-1)=O(P_R/R). Also alpha_Q>=alpha_S. Thus
    F = Omega((alpha_S/alpha_Q)*R X/P_R).            (11)
Without the second cutoff, (7) gives the valid weaker Omega(alpha_S R X/P_R). The new lower bound compared to the earlier multiple-cut gain bound Omega(S R X/(K_S P_R)) has a ratio of scale
    (alpha_S/alpha_Q)*(K_S/S)=2A_S/(S alpha_Q).
Since A_S=Omega(S) by Bertrand and alpha_Q->0 by infinitude of primes, this ratio tends to infinity. This comparison is of lower bounds for different nested populations, NOT an improvement to the previous restricted B_K gain theorem. Further, the elementary lower estimate alpha_S>=exp(-C S/log S) gives alpha_S/alpha_Q>=R^(-o(1)) for S~log R, so (11) is Omega(R^(1-o(1)) X/P_R) in the lower-bound sense. No uniform positive fraction for growing S is asserted.

## 4. Narrow-band genuine ordinary recovery

Assume additionally that the number of far B with p>R crossing dense S-barriers is o(sqrt X). This is stronger than requiring sparsity of only the multiple-K_S crossers; it includes all B covering dense R-barriers. Then (9) gives
    m >= ((lambda-1)/14-o(1))*X/P_R,
which is much larger than sqrt X log X. Discard the near and above-R far recovering B in (6)-(8) using gamma times their counts, and the reset/endpoint terms. All these omitted losses are o(m). Let J_band be the remaining charged events (far nonreset B, S<p<=R, strict decrease of Phi). Write j_band=j, F_band=F, Dplus=sum_{J_band}(d-d')_+ and Dnet=sum_{J_band}(d-d'). The resulting bounds are
    j >= (log10/log(3/2)-o(1))*m,
    sum_{J_band}(W_S-2w) >= (log10/5-o(1))*R*m,
    F >= (log10/5-o(1))*(alpha_S/alpha_Q)*R*m,
    Dnet+K_S*j >= (log10/5-o(1))*R*m.              (12)
The third inequality uses (4) and K_Q=o(S) uniformly. Dplus obeys the last inequality as well. Each charged event crosses a dense barrier simultaneously at every cutoff <=S and W_S>2w. The net ordinary decrease may be negative for some individual events; the exact correction is (3).

New ordinary-deficit alternative: writing c_* = log10/5, for sufficiently large windows under these hypotheses, either
    j >= (c_*/3)*R*m/K_S
or
    Dnet >= (c_*/2)*R*m
(up to choosing X sufficiently large that the o(1) in (12) is <=c_*/6). The second case forces total genuine positive ordinary reduction at least this large. In particular if j=O(m), the first case is impossible since K_S=o(R), and Dnet>= (c_*-o(1))*R*m. More concretely suppose j<=C_0*m for some fixed C_0. Each positive ordinary drop is <=p-3<R. For sufficiently large X set delta=c_*/(4 max(1,C_0)), a fixed positive number. Drops <delta R can contribute at most (c_*/4)Rm, whereas Dplus>=(c_*/2)Rm eventually. Thus at least (c_*/4)m distinct charged events have
    d-d' >= delta R, p>=delta R,
    2w = p-1-(d-d') <= p-1-delta R <= (1-delta)*p.
They are genuine ordinary-decreasing nonreset B with label of order R, not merely decreasing the cut-corrected potential; and the relative wait is bounded away from p/2. This is a conditional lower bound on one actual trajectory, not an assertion that j=O(m) is forced. If j is very large the count alternative remains, and the proof does not force the actual-decrease branch.

## 5. Reproducible diagnostics and limitations

[Audit 0dd4206](https://github.com/tara-sooo/A166944-Lean/blob/0dd4206c2a9146512144e2e102a51e8e1d42ee99/research/min_direct_nested_dense_recovery_audit.mjs), blob aa7202b3c8ccb3ed42ea7879eaa7bbb57d55f1d5. Exact remote readback. Run node research/min_direct_nested_dense_recovery_audit.mjs 50000 180. Actual ECMAScript execution in tool runtime, not a separate Node process. 24,998 odd canonical M5..50000,452,868 events,3,929 A1, all terminated within180. Complete dense periods S=3,5,7,11,13,17 verified; normalized rho computed via exact scaled integer arithmetic (A_S times u and rho); max-min <=K_S. 678,665 block/cutoff incidences including witness,37,760 retained segments,38,490 separator checks,327,295 exact local update checks and nested-capacity checks each,251,552 noncrossing checks. 678,665 weighted and 678,665 ordinary-recovery budget checks; 2,742 charged nonreset incidences,1,980 with genuine ordinary decrease. Diagnostic R47/101/1009, (S,Q)5/3,7/3,11/5,13/5,17/7, below the theorem's S>=47 restriction; classification checked for labels>=47. Some finite coefficients ell<=0, not used for asymptotic bounds. Cut counts and scaled potentials exact BigInt, log comparisons floating point tolerance1e-8. All assertions passed.

Reconstructed earlier 9,962-digit eight-event canonical witness, 22,195 literal BigInt GCD ticks,20,600 stage-residue checks. At R1009,S5,Q3, m2,j6, zero resets, actual total gain14604, normalized S-cut length14595, normalized recovery loss13899 and ordinary decrease13908. At S7 the same six losses are charged, with normalized cut length14665. This confirms the correction can have either sign in aggregate; does not empirically test a macroscopic asymptotic window. The audit does not claim every charged event is an ordinary decrease (1980/2742 overlapping sampled incidences). All final assertions passed. No new external novelty claim, no Lean kernel verification. Main and sibling branches unchanged.

The repeated-label approach alone still has not supplied a sufficiently strong upper bound; the new comparison exploits simultaneous nested cuts instead. Under finite twins each sufficiently large canonical root gives an infinite ray, and the necessary count/gain/recovery statements apply without any probabilistic independence assumptions. No contradiction with finite twins yet. Next investigate whether abundant small-label recovery or actual fast ordinary reduction can be bounded globally, rather than treating the conditional j=O(m) branch as automatic.
