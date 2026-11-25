# Far-only recovery, an improved joint count, and a weighted A1 tail bound

Continuation of [f82180c](https://github.com/tara-sooo/A166944-Lean/commit/f82180c76e6c0db2570a063b7931544054c5b9db). A geometric observation about later near-square labels makes almost the entire required A1 recovery inaccessible to near nonresets. This yields a far-gain share ceiling and a stronger unconditional-on-sparsity root-or-B count. In the root-sparse/high-far-B-sparse branch, the previous exceptional large-A1 tail has o(X) total gain, not just o(m) occurrences. No contradiction with finite twins or Lean kernel verification.

## 1. Later near-square labels cannot pay the lower recovery levels

Use the established adaptive MIN model, ordinary pre/post deficits d,d', x=d+3 and x'=d'+3, event label p, gain g=p-1, wait w, side I and adjusted D=d'-6I. At an A1, p>=47,p>=5d+15,D=2p, so x<=p/5 and x'>2p. Every nonreset p>=5 has x'>=2p+3. Decreasing nonresets have x/x'<3/2; label3 never decreases. Decreasing resets have label>=7 on canonical rays. The seven-tick normalization gives distinct associated canonical visits for any resets of label>=7, except possibly one pending at the block endpoint.

Consider a finite contiguous canonical event block with pre-horizons H>=A>=257 and labels <=C (one can use C=floor sqrt(Y+1) for upper pre-horizon Y). Set
    k=floor((A-1)^(1/4)), eta=2/k, c=9/5-2eta=9/5-4/k>0.
Use the fixed near-square definition of 8b30078: selected label s and cofactor q>=s give center a=(s+q)/2 and half-gap b=(q-s)/2, with H=a^2-b^2+e; near means b^2<=epsilon0*a (fixed 0<epsilon0<1) and the prior minimum-center threshold. For a near event occurring AFTER a marked A1 of label p, let H0 be the mark's pre-horizon and H1 the later pre-horizon. Then
    s=a-b >= (1-1/k)*sqrt(H1-1)
          >= (1-1/k)^2*sqrt(H0+1)
          >= (1-eta)*p.                               (1)
Indeed a>=sqrt(H1-1), b/a<=sqrt(epsilon0/a)<=1/k, and sqrt((H0-1)/(H0+1))>=1-1/k since H0>=A>=257. Eligibility gives p^2<=H0+1. Thus no later near NONRESET can cross downward any level
    y in (p/5, 2(1-eta)*p],                            (2)
since its post x'>=2s+3>2(1-eta)*p. This applies even if the original mark itself was near. Near resets may still pay such levels. The width of (2) is exactly c*p, and eta=O(A^(-1/4)). No assumption on the size of the nonreset multiplier h or on other intervening events.

## 2. Full real-level allocation and far gain share

Mark any subset of A1 events, count m, weight W=sum of their labels p, and let F_f be the total gain of the marked FAR A1 events. Let G_f be all far event gain, G the block gain, N the number of actual canonical visits in (start,end]. Each mark crosses all levels (2) upward. Assign each real level in its interval to the first subsequent downward crossing of that level if one occurs before the block ends. At each fixed level the assignments are injective: another mark cannot cross it upward before the first mark's level has been crossed downward. Equivalently maintain disjoint pending half-open intervals, add each mark interval (which begins at or above the pre-state), and remove the portions in (x',x] at every decrease. At all times pending levels are <=current x. This is a finite interval construction, so there is no measure-theoretic or infinite exchange issue.

Each decreasing event can pay at most its actual ordinary drop d-d', and the total pending length at the endpoint is <=2C because all assigned levels lie in (0,2C]. All nonreset payments come from far events by (1). A1 marks are not decreasing events. Thus with D_nr the sum of the actual drops of all near decreasing resets,
    c*W + F_f <= G_f + D_nr + 2C.                     (3)
For this sharper inequality, far resets are already included in the unmarked far gain; only near resets require a separate term. D_nr<=C times their count. In particular
    (1+c)*F_f <= G_f + D_nr + 2C.                    (4)
These are finite inequalities for any marked subset and do not require root sparsity. If A~X and N=o(sqrt X), C=O(sqrt X), then D_nr<=C(N+1)=o(X), c=9/5-o(1), giving F_f<=5G_f/14+o(X). Previously the ceiling was 5G/14+O(C). This version charges recovery to the far gain itself, not to all gain.

## 3. Coupling to the Fourier horizon barrier

Now mark ALL A1 p>R with R>=47, writing m_f for the count of far marked events and B_R for the count of all far B p>R (B means failure of the established low-deficit test; A0/A1 exhaust the other high events). Use E_R, the common normalized discrepancy bound of f82180c in the halved coordinate. Let n_near be the number of all near events in the block. Total normalized H-barrier coverage is >=G-2E_R; near events cover at most G-G_f+2E_R*n_near, and low labels p<=R cover none. Hence
    G_f <= F_f+2E_R*m_f
           +(C+2E_R)*(n_A0+B_R)+2E_R*(n_near+1),      (5)
where n_A0 counts high-far A0 resets. Substituting (4) proves
    c/(1+c)*G_f <= 2E_R*m_f
      +(C+2E_R)*(n_A0+B_R)+2E_R*(n_near+1)
      +(D_nr+2C)/(1+c).
The near decreasing resets counted by D_nr are disjoint from the high-far A0 resets. Each has label>=7 and thus their combined count is at most N+1, by normalization. Since D_nr<=C times the former count, the resulting exact common bound is
    c/(1+c)*G_f <= 2E_R*m_f
      +(C+2E_R)*(N+1+B_R)+2E_R*(n_near+1)+2C/(1+c).   (6)
This use of disjoint reset counts avoids charging the same canonical reentry twice. The analogous finite statement with an arbitrary upper bound for the H discrepancy instead of E_R also holds.

For crossed [X,lambda X] on an infinite canonical ray, fixed lambda>1, G=(lambda-1)X+O(sqrt X), G_f>=G/2-O(sqrt X), n_near=O(sqrt X), C=floor sqrt(lambda X+1). Choose the balanced R of f82180c (largest odd prime with P_R<=sqrt X), or any R~log X with E_R log X=o(sqrt X). Then c=9/5-o(1), so (6) gives
    9G/28-o(X) <= 2E_R*m_f+(C+2E_R)*(N+1+B_R).         (7)
This improves the earlier G/7 residual to 9G/28, a factor9/4, and explicitly counts FAR A1.

In the sparse branch N=o(sqrt X), B_R=o(sqrt X), it follows that
    m_f >= (9*(lambda-1)/56-o(1))*X/E_R.              (8)
At lambda16 the coefficient is135/56, rather than15/14. This is the factor9/4 improvement at the same Fourier cutoff. All asymptotic errors are uniform for fixed lambda and near definition.

## 4. Stronger root-or-B count without sparsity assumptions

Choose S to be the largest odd prime with P_S<=R. Then S~log R in the order-of-magnitude sense, S>=47 eventually, and Bgap=2ceil(E_S)+4=o(R) by the Fourier estimate. Define B_union as the number of actual events in the disjoint union:
* all far B with p>R;
* far ordinary-decreasing nonreset B with S<p<=R which cross a dense S DEFICIT barrier downward.
All members are far B with p>S. The lower-band condition uses deficit barriers, not horizon barriers. In particular this is a different event population from the earlier multiple-horizon-cut restriction.

Apply the rounded geometric matching of f82180c to the FAR marks p>R, restricting the upper level to 2(1-eta)*p rather than 2p. Put beta=3/2+10Bgap/R, use reference z_j=(R/5)*beta^j through2C (any fixed phase in [1,beta) also works), round up to the first shifted dense S-deficit barrier y_j in [z_j,z_j+Bgap). Successive rounded levels have ratio>=3/2. Select for mark p the references in
    (p/5, 2(1-eta)*p-Bgap].
The multiplicative ratio tends uniformly to10 as X grows, beta->3/2, so each mark has at least five and at most six selected levels, all inside (2). At each level match first downward crossings. A nonreset crosses at most one rounded level because x/x'<3/2; thus all nonreset matches are globally injective. By (1) and the deficit barrier property all have far labels s>S, and all are B because they decrease and S>=47. Each is counted by B_union. Resets and the endpoint remove at most (N+2)*L slots where L=O(log X) is the number of reference levels. Therefore
    5*m_f <= B_union+(N+2)*L.                         (9)
This is a count bound for occurrence multiplicity, not distinct labels.

Substitute (9) into (7), using B_R<=B_union and E_R L=o(sqrt X). The endpoint errors are o(X), and the coefficient of N+B_union is C+o(sqrt X). Hence for every such crossed window,
    N+B_union >= (9*(lambda-1)/(28*sqrt(lambda))-o(1))*sqrt X.  (10)
For lambda16 the constant is135/112, versus15/28 in the earlier root-or-B count. This is the same factor9/4 improvement, with no root-sparsity or high-B-sparsity hypothesis. It does not bound the number of B that can occur from above. It also does not imply the identical stronger constant for the previous horizon-cut-only population.

## 5. Weighted upper bound on large A1 labels

Use any marked subset with p>R and p>=T, and denote its weight W_T and count m_T. In the real-level intervals (2) take only shifted dense R-deficit cuts. The normalized count of slots per mark (2/theta_R times the number) is >=c*p-2E_R-2 by the uniform Fourier interval discrepancy, with +2 for real endpoints. By alternating crossings no event/cut pair can be used twice. Every downward payment must have label>R, and if nonreset, is far by (1).

Let J_R be the count of all far ordinary-decreasing nonresets with label>R, D_R their actual ordinary decrease sum. Let Z be the count of all decreasing resets in the block, D_Z their total ordinary decreases. Thus J_R<=B_R for R>=47, Z<=N+1. A decreasing event can pay normalized dense-cut count at most its ordinary drop+2E_R. The pending slots at the endpoint lie below2C, so their normalized count is <=2C+2E_R+2. We obtain the finite weighted upper bound
    c*W_T <= (2E_R+2)*m_T + D_R+D_Z
               +2E_R*(J_R+Z+1)+2C+2.                (11)
The capacity of low labels is exactly zero, not merely small on average. No near-nonreset count term appears. Since m_T<=W_T/T, when c>(2E_R+2)/T this yields an upper bound on W_T in terms of the actual high far decrease and reset supply.

For large crossed windows choose T=max(R+1,4ceil(E_R)+8). Then the coefficient c-(2E_R+2)/T is bounded below by a positive constant. Also D_R<=C J_R,D_Z<=C Z. Under N=o(sqrt X), B_R=o(sqrt X),
    W_T=O((C+2E_R)*(N+B_R+2))=o(X).                 (12)
This is the NEW weight bound for the same large-label tail as in f82180c (including an immaterial p>R restriction). That note bounded its count by o(m) but left the possibility of macroscopic exceptional gain. Here its total gain is at most its total weight W_T=o(X). In particular all marked near A1 have weight o(X): each near label is >=(1-o(1))*sqrt X, while T=o(sqrt X), so belongs to the tail. No relative o(W) bound is asserted if total mark weight W=o(X).

## 6. Full-weight low-band recovery and removal of the exceptional macroscopic weight

Use the entire mark collection p>R in (2), but now choose dense S-deficit cuts with S<R and E_S=o(R). The same allocation has normalized slot demand >=c*W-(2E_S+2)*m. Every nonreset payment is far; every payment label is >S. Omit payments by resets and by high far decreasing nonresets s>R, as well as pending endpoint slots. Their total normalized capacity is at most
    L_loss=D_R+D_Z+2E_S*(J_R+Z+1)+2C+2.
For F the total ordinary decreases by far nonresets S<s<=R and j their count, per-event slot capacity gives simultaneously
    F+2E_S*j >= c*W-(2E_S+2)*m-L_loss,
    F/theta_S >= c*W-(2E_S+2)*m-L_loss.               (13)
In the second inequality use the even-level count capacity (d-d')/2. In the sparse branch at balanced R,S, L_loss=o(X), (2E_S+2)m=o(W) since W>=Rm, so
    F+2E_S*j >= (9/5-o(1))*W-o(X),
    F >= theta_S*[(9/5-o(1))*W-o(X)].                (14)
These full-weight inequalities do not discard any marks. They are useful at macroscopic weight W=Omega(X); if W=o(X) the additive error may dominate, and the previous good-mark relative bound remains useful.

Indeed the completed-slab good-mark argument of f82180c at eta_slab=1+1/log X discards at most O(sqrt X log^2 X) mark occurrences. The sum of their labels below T=O(E_R+R) is o(X) because E_R log^2 X=o(sqrt X), and their tail weight is o(X) by (12). Thus W_good=W-o(X) in the sparse branch. This supplies the previously missing macroscopic weight control for that argument. It does not claim W_good=(1-o(1))*W for every sublinear W. Nor does (13) yield a supply upper bound low enough to contradict (8); abundant small-label recovery remains possible under these estimates. Neither sparsity hypothesis follows from finite twins.

## 7. Reproducible diagnostics and persistence

[Audit ea02981](https://github.com/tara-sooo/A166944-Lean/blob/ea029815a29e7dc393da690c6b9869fee9a6c594/research/min_direct_far_recovery_tail_audit.mjs), blob b5b5f5d68660bd5a8fe9c84872d07ae19dce6261. Exact remote readback. Run node research/min_direct_far_recovery_tail_audit.mjs 60000 180. Actual ECMAScript executed in tool runtime, not a separate Node process.

29,998 odd canonical roots,549,085 actual events,5,254 A1, all stopped within cap180. Complete small periods R5/7/11/13 for H and deficit families, using their exact finite discrepancy (not an extrapolation of Fourier asymptotics). 217,844 full/suffix block-cutoff incidences,26,908 marked blocks incl four witness controls,27,412 mark incidences (852 near),255 checks of later near labels against prior marks. 594,324 ordinary interval allocation checks,4,800 dense intersection checks,26,908 each far-share, near-reset-only share, combined canonical-root, tail weight and low-band inequalities;26,904 joint horizon/deficit capacity tests including the stronger combined-root inequality. 11,227 tail mark incidences,244,211 selected dense tail slots,14,607 paid by events. Finite thresholds R7/11/13,S5/7, below the asymptotic R>S>=47 restriction; tests of geometry use all other high far events where necessary. Integer scaled interval coordinates and exact complete-period discrepancies are used within safe integer ranges. Rounded geometric matching uses exact rational references, including 4 witness blocks with40 slots,20 distinct far nonreset matches and20 endpoint exceptions. All assertions passed on the final rerun.

Rebuilt prior9,962-digit canonical root,22,195 literal BigInt GCD ticks,20,600 stage-residue checks. For finite control use conservative lower horizon A=100000001, so k100 and c1.76. The two marks7687 and7369 have total label weight15056, assigned ordinary decrease13529.12, pending length12969.44, actual far ordinary decrease13908 and no resets. The small cutoffs make the six recovery labels high, as intended for the tail-capacity diagnostic; no claim of an actual macroscopic sparse window is made. No Lean kernel verification or observation of an infinite ray. Main and sibling branches unchanged.

Next: exploit the joint count (10) and tail weight (12) to separate the small-label A1 concentration from the supply of actual deficit-crossing far B. The current fixed-level occurrence bounds are still too large; neither (10) nor the sparse-branch constraints close the finite-twins contradiction.
