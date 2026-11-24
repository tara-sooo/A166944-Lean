# Exact large-exit clock priorities and a weighted low-height restart budget

2026-11-25 JST. Continues 46ebb6b7e1cec27ae256a3bb3af3c08ba02d365d on the SAME research/min-cycle-forest-2026-11-24 branch. New exact periodic first-exit distribution, its reset/nonreset moment split, and an unconditional source-weighted cost bound for low-height-start cell blocks at arbitrary previous depth. Uses classical Mertens product and prime number theorem in the two odd classes mod 4, and the previously used uniform dimension-two upper-bound sieve. No new external literature search. No Lean compilation. No proof of eta->0, global weighted coalescence, or twin-prime infinitude.

## 1. General low-height start and deterministic priority formula

Use canonical MIN clocks, even horizon C and integer time t, height h=2t-C>=0. Write b=0 for the even clock (C==1 mod p), b=6 for the odd clock (C==-1 mod p). For any eligible odd prime p, even if it is not the winner, its strict future next clock n=t+w satisfies 1<=w<=2p and candidate post-height
    h'=2n-(C+p-1) == b (mod 2p).
Moreover h'>=h+3-p>=3-p. For p>=5, the largest negative number in the residue class b mod2p is strictly below 3-p; for p=3 the direct lower bound is zero. Hence h'>=0. In particular all actual candidate clocks preserve nonnegative height; this is not an assumption about selecting the least clock.

If p>max(7,h+1), then h'<=h+3p+1<4p, so
    h'=b+2kp, k in {0,1}.
For p>=5, k cannot be negative by nonnegativity. The case k=0 is exactly a reset, h'=b. The parity of k is determined by the landing horizon: both the even clock with b=0 and odd clock with b=6 give h'-b == -(C+p-1) mod4. Thus set
    a_d(p)=1 if d+p-1 ==0 mod4, else 3,  d=C mod4 in {0,2}.
Then k=(a_d(p)-1)/2 and the exact wait is
    2w=a_d(p)p+b-1-h.
All candidates for such p at a fixed (C,t) are ordered by the pair (a_d(p)p+b,p), using the second entry for the MIN tie-break. This formula is independent of the value of h in the comparison, as the same -1-h is subtracted from every priority. It also shows the qualitative difference between a large reset jump (wait approximately p/2) and a large nonreset jump (wait approximately 3p/2), when h=o(p).

## 2. Periodic root-slice exit law, including arbitrary bounded starting height

Let W be an even primorial, allow W=2. Use right-closed W-cells (cW,(c+1)W]. For each fixed nonnegative even initial height h0 and fixed parity epsilon in {0,1}, vary the initial time u in that parity, put C0=2u-h0, and run the finite prime alphabet <=Z until the first executed W-cell departure or a natural terminal inside the cell. This is the actual one-dimensional source slice, not the independent two-coordinate CRT ghost. Canonical odd sources correspond to h0=6,epsilon=1 with u=M+2; even reset starts have h0=0,epsilon=0. For all such starts, before an exit:
    0<=g=C-C0<W,
    e=t-u<=3g,
    h=h0+2e-g<=h0+5W.
Every internal label is <=W. Let H>=h0 and Z0>=2H+10W+14. Then any prime q>Z0 cannot preempt an internal step: the internal wait is <=2W, so that candidate would have negative post-height by the bound h<=H+5W. Any q>Z0 is also in the range of the exact priority formula of section1.

Let D_A=2 product_(3<=p<=A prime)p for a cutoff A; W divides D_Z0. Condition on a time residue u mod D_Z0, of the designated parity. Relative trace and position within the W-cell are fixed for the <=Z0 model. If it terminates inside the cell, call its terminal phase d=C mod4, height h. Here d is invariant under u->u+D_Z0 since D_Z0 is even. Every enlarged alphabet <=Z, Z>=Z0, follows the same internal trace until this terminal because q>Z0 cannot preempt an internal step. At the terminal, all q<=Z0 are ineligible. For each q>Z0, the source residue u mod q is independently uniform over its q possibilities by CRT, conditional on the lower residue. The two eligibility sides each occur with probability 1/q, and neither with probability 1-2/q. There is no additional independent clock coordinate: the fixed-height source slice makes the eligible wait deterministic given d,h,q,b.

For a candidate (p,b), Z0<p<=Z, write
    j_q(p,b;d)=# {b' in {0,6} : (a_d(q)q+b',q) < (a_d(p)p+b,p)}
for each q!=p with Z0<q<=Z. It is 0,1,or2. The exact probability of selecting p on side b conditional on the lower-terminal phase is
    Pr(p,b | lower terminal phase)
       = (1/p) product_(Z0<q<=Z,q!=p) (1-j_q(p,b;d)/q).
The other side of p need not be excluded as an extra factor; the two side events at p are disjoint. This expression is valid even if priority ties occur. If no candidate matches, the path terminates inside the cell, with conditional probability product_(Z0<q<=Z)(1-2/q). These outcomes exhaust probability one. The product depends only on d (and Z0,Z), not h or the detailed low path. Actual elapsed wait still contains the term -h/2.

Let nu_(h0,epsilon)(W,A) be the no-exit fraction over a full period of the indicated time slice. The exact no-exit law of the preceding note holds for this slice by the same argument (also if a lower trace exits, an earlier preempting added label >W exits). Put rho_A=product_(3<=p<=A)(1-2/p). Then
    alpha_(h0,epsilon)(W)=nu_(h0,epsilon)(W,Z0)/rho_Z0,
    1<=alpha_(h0,epsilon)(W)<=1/rho_W=O(log^2(2W)),
and nu_(h0,epsilon)(W,Z)=alpha_(h0,epsilon)(W)rho_Z for Z>=Z0. The first inequality counts initially rough horizons; C0=2u-h0 is uniform mod each odd prime. The upper bound conditions on the <=W lower trace ending inside its cell, then excludes the two terminal divisibility residues of every larger prime. Alpha is independent of Z0 once it satisfies the indicated threshold. For h0=6,epsilon=1 it is the previous alpha(W); the other slices can have different coefficients.

Conversely, every actual first exit of label p>8Z0 must have been at such a <=Z0 terminal: h<=H+5W implies w>2Z0, so no smaller alphabet label can be eligible, and all prior internal steps agreed with that alphabet. Thus the preceding probability formula covers ALL first exits p>8Z0, not merely a conditional subset. The extra factor 8 avoids any claim of this converse for the intermediate band immediately above Z0.

## 3. Large-label moment asymptotic: equal gain, unequal waiting time

For p>8Z0 and p sufficiently large, all competitors q<p/4, q>Z0 have both sides before (p,b), and all q>4p have neither side before it. This follows from priorities in [q,3q+6] and [p,3p+6], with small p absorbed by a uniform threshold. Comparing the exact product to rho_p/rho_Z0, the only factors that can differ are in [p/4,4p] (including p itself). Their total harmonic prime weight is O(1/log p) by the prime-count upper bound. Uniformly in d,b,Z>=p and the lower-terminal phase,
    Pr(p,b | phase)
       = (rho_p/(p rho_Z0))(1+O(1/log p)).
This also works near the top cutoff Z, since the missing competitors above Z only change factors in the same constant-ratio band. There is no assertion that the relative error at a finite p is numerically tiny.

Fix W and a reset start type (h0,epsilon)=(0,0) or (6,1), or allow W<=log^(1/4)Z growing and use Z0=10W+14 for these reset types. Write alpha for its amplification coefficient. Consider the random original reset time on a full period of D_Z. By the converse in section2 all exits with p>sqrt Z are covered for large Z. Split lower-terminal phases according to d=0,2, writing alpha_d for their respective fractions divided by rho_Z0; alpha_0+alpha_2=alpha. Then for each d the reset class is precisely p==1-d mod4, and the nonreset class the other odd residue. For each sign the unconditional probability of a label p>sqrt Z from those phases is alpha_d rho_p/p * (1+O(1/log p)). These are one-dimensional CRT counting probabilities, not the distribution of packet masses conditional on arrival.

Let c_rho>0 be the Mertens constant for rho_x ~ c_rho/(log x)^2. The classical PNT in the two odd residue classes mod4 and partial summation imply, for either odd class a,
    sum_(sqrt Z<p<=Z, p==a mod4) rho_p
        ~ c_rho Z/(2 log^3 Z).
The lower bound sqrt Z can be rounded and removing it from the total is negligible. Since the error in the label law is uniform for p>sqrt Z, it follows (summing both sides b and both lower phase classes) that the two expectations of FIRST EXIT GAIN, with zero contribution when the exit is absent or is not in the indicated class, satisfy
    E[(p-1) 1{p>sqrt Z, reset}]    ~ alpha c_rho Z/log^3 Z,
    E[(p-1) 1{p>sqrt Z, nonreset}] ~ alpha c_rho Z/log^3 Z.
These statements are uniform for the stated slowly growing W: the alpha_d are nonnegative, total alpha>=1, and the PNT estimates involve only the two fixed residue classes, not W. The h at the exit is O(W+1)=o(sqrt Z), so the actual wait ratio in section1 gives
    E[w 1{p>sqrt Z, reset}]    ~ (1/2) alpha c_rho Z/log^3 Z,
    E[w 1{p>sqrt Z, nonreset}] ~ (3/2) alpha c_rho Z/log^3 Z.
Internal elapsed <=3W, and exits p<=sqrt Z add at most 2sqrt Z elapsed and sqrt Z gain per source. Those contributions are negligible versus alpha Z/log^3 Z. Consequently nonreset large exits account asymptotically for one-half of the gain and three-quarters of the first-exit block elapsed time in this FULL PERIODIC model, for either reset source type. They also create post-height b+2p, unlike reset exits. This is an actual asymptotic moment calculation, not a fit to finite data. It concerns a single local block from a uniformly sampled reset origin. It neither estimates the mass distribution of actual arrivals at those origins nor asserts the same ratio at integer cutoff B~sqrt X. The complete period D_B is too large to transfer this equality to [X,2X).

## 4. Actual integer low-start block costs: unconditional uniform sieve bound

Return to X dyadic, B=ceil(sqrt(7X)), canonical original source cutoffs, and hypothetical time origins u in an O(X)-length interval containing all actual attained times, with even C0=2u-h0 in the physical horizon window. For each h0 even, 0<=h0<=H, and each parity epsilon, analyze the entire first W-cell exit/terminal block using primes <=B, without any time-cutoff restriction until the block ends. This only overcounts the actual executed prefix, even if the final hypothetical clock lies beyond the original cutoff. All pre-horizons remain in the origin cell; no event beyond the first exit is counted. Choose W even primorial, W<=log^(1/4) B, H<=log^(1/2) B, H>=6, Z0=ceil(2H+10W+14). Then D_Z0=B^o(1) <=B^(1/4) eventually; p>sqrt B exceeds 8Z0 eventually.

For a large first exit p>sqrt B, all earlier events form the <=Z0 terminal-inside trace by section2. Its terminal horizon is 2u-h0+g_r for a fixed lower residue r mod D_Z0, with even 0<=g_r<W. By nonnegative landing height and w<=2r(C) (here r(C) is the least eligible prime, not the residue index), r(C)>p/8. For each side sigma=+/-1 and each fixed lower terminal residue, p | (2u-h0+g_r+sigma) fixes one progression u=u0+D_Z0 p j. Along it the selected neighbor divided by p and the other neighbor are affine forms
    f1(j)=m0+2D_Z0 j,
    f2(j)=p f1(j)-2sigma.
For every odd prime ell>Z0 up to a small fixed power p^c, the slopes are invertible and the forbidden residues are distinct, since ell!=p and f2-pf1=-2sigma. Both forms must avoid zero by roughness r(C)>p/8. The progression length is O(X/(D_Z0 p)+1); it can be bounded by an interval of length comparable to X/(D_Z0 p)>=c' B^(3/4). The standard dimension-two upper-bound sieve used in the preceding root-slice proof, with fixed small-power sieve range and level, gives
    #origins for this residue, p, sign
       = O(X/(D_Z0 p) * log^2(2Z0)/log^2 p).
Indeed the product of local factors over ell>Z0 to p^c is O(log^2(2Z0)/log^2 p) by Mertens; the usual small-power-level remainder is absorbed by the displayed interval bound. The estimate is uniform in h0, parity, g_r, and the terminal residue. All eligible factors are considered; no new assumption of independent source masses is made.

The number of terminal residues at the fixed parity is (D_Z0/2) nu_(h0,epsilon)(W,Z0). Using rho_Z0=Theta(1/log^2(2Z0)), their total yields the refinement
    #origins with first exit p at fixed h0,epsilon
        = O(X alpha_(h0,epsilon)(W)/(p log^2 p)),  p>sqrt B.
It retains the actual local amplification rather than multiplying the number of roots by W. By summing over p, and using p as a bound for the r-cost of the exit step, the large exits contribute at most
    O(X B alpha_(h0,epsilon)(W)/log^3 B).
All internal steps together cost <=1.5 W per origin by monotone horizon and r(C)<=p<=1.5(p-1); a small exit costs <=sqrt B. Thus if F(h0,epsilon) is the sum of the hypothetical entire local block costs over all admissible time origins of that fixed height and parity,
    F(h0,epsilon)
       = O(X(W+sqrt B)+X B alpha_(h0,epsilon)(W)/log^3 B).
Use alpha<=O(log^2(2W)) to sum over the O(H+1) height/parity choices:
    F_low(H,W) = O(X(H+1)[W+sqrt B+B log^2(2W)/log^3 B]).
Every actual bounded-height start state has a unique u,h0,epsilon. This bound includes all internal events regardless of how many occur or how many intermediate resets they include. It is not an asymptotic equality for the actual integer model.

## 5. Weighted arbitrary-depth restart lemma and residual for a new physical cap

The preceding unweighted bound can be applied to source-weighted paths even after large local mergers. Use a new optional accounting stop: at EVERY attained physical V(t,C) of height <=H, stop all its active tags if its actual total mass is >=T, with T=ceil(B log^2 B). Keep original individual cutoffs and MIN choices; the new rule changes only where prefixes are truncated. One can use this alongside other stops, but the following residual statement uses this rule alone. Physical states at each horizon are processed together, so all active tags at such a state face the same test. Root starts have h=6<=H. If a tag continues from any low-height start state, it is among fewer than T tags at that state, regardless of previous history or ancestry. No factor for number of later mergers is needed.

On each actual truncated path, mark each segment starting at a state of height <=H and ending at the first subsequent state of height <=H, the first executed W-cell departure, natural terminal, or accounting stop, whichever occurs first. Include the departure/next-low event if executed. If a segment exits into a high state h>H, then leave the following part until the next low-height state (or termination/stop) unmarked. Inside a marked segment all events follow a prefix of the hypothetical local block from its start. Starting another segment at its last event's post-state does not double-count that event. A source visits a given start state at most once (strict horizon growth). Across the entire population, the marked cost R_lowstart is therefore bounded by
    R_lowstart <= T F_low(H,W).
This also holds if only selected such segments are marked or they are truncated further. One may count only reset starts, getting the stronger bound without the H+1 factor using the two reset slices. The sum is over starts at ANY depth and permits arbitrarily many previous large packets to merge, not just first exit from an original root.

For example H=floor(log^(1/2)B), W an even primorial tending to infinity sufficiently slowly with W<=log^(1/4)B, the new cap T satisfies
    R_lowstart = O(X^2 [(H+1)(W+sqrt B)log^2 B/B
                       +(H+1)log^2(2W)/log B])
                = o(X^2),
since X asymp B^2. For reset starts alone one can take T=B log^beta B for any fixed beta<3 under the same slow W. The estimates follow from the standard sieve and do not require the unresolved LOW height-tail hypothesis. They are valid for every actual source-preserving run with the specified cap. They do not bound the unmarked remainders.

Let S_lowstop be total source mass stopped by this new low-height physical cap alone. Let R_highremain be the cost on the remaining portions of the unstopped paths, or more generally on all truncated paths. Every such portion starts only after a W-cell exit from a marked segment landing at h>H, and continues with all actual pre-heights >H until the next low state or termination. All initial states were low, and by construction these portions cannot start at arbitrary earlier high events inside the same W-cell block. Since the exit label is >= the primorial cutoff, this identifies a specific transition into the unresolved high-state transport. On a no-twin window every naturally unstopped source has cost >=c X for a uniform c>0 by the existing canonical non-twin elapsed lower bound. Consequently
    R_highremain >= c X (N-S_lowstop) - o(X^2).
This is a genuine removal of the low-start portions of the global weighted budget, without restrictions on number of intermediate events. It does NOT say that S_lowstop is small, or that the high-state remainders have small cost. Low-state stops have large physical mass >=T, so can alternatively be added to a physical forest target (without virtual clock merging), but no upper bound on their far variance follows here. This is a new accounting option, not a proof that it improves the earlier cell/inverse scheme in every respect. In particular one must not treat an arbitrary high-start segment as reset-origin or apply the periodic moment ratio to its actual adaptive arrival weights. A further analytic task is control of the long high-height stretches following nonreset exits, and their mass growth. The earlier eta and global weighted coalescence problems remain independently open.

## 6. Audit and exact preservation

Saved research/min_reset_local_exit_priority_audit.mjs and research/min_reset_local_exit_priority_results.json, exact remote content readback at 3a84d9a3131993127777d8b6d52ab77849bdab2e. The final source was run independently using local Node.js v22.16.0; its local SHA256 was 06e550484ddb1bd272e5aa0d6b4972408d520a6c88f292730b0693e5246baa84. The earlier combined tool-runtime attempt failed a cutoff-match assertion, with a diagnostic inconsistent with the elementary p=3 clock at the displayed state. The standalone local rerun passed all cases; we do not infer a cause of that tool-runtime discrepancy. The persisted code is the locally run version. No simulation of the new weighted cap in this turn; its inequality is a paper deduction from the hypothetical-start bound. The extension to all bounded h0 is also a paper proof; the actual integer audit tests reset starts only.

Integer audit: X=16384,65536,262144; W=2,6,30; for every hypothetical reset u in [X+3,floor((7X-1)/4)], simulate the first W-cell exit/terminal block, including the full block even if it extends beyond this time interval. Exact SPF and MIN clocks, gain/elapsed bound and nonnegative heights, terminal/exit conservation. At p>8(10W+14) replay with cutoff 10W+14, assert identical terminal pre-state and prior event count, exact reset/nonreset priority and roughness. This threshold is sufficiently large for both reset types by h0<=6 and the direct bound h<=6+5W; the general h0 formula Z0=2H+10W+14 is deliberately more conservative. At X262144,W6, B1355 there are196605 hypothetical reset starts, 7960 terminals inside the cell, 106126 reset and82519 nonreset exits. For large p>592,1669 reset and451 nonreset exits,2120 exact tail checks; corresponding exit gain totals1414290 and317934, waits705438 and477205. Total r-cost of all blocks6865589, elapsed6153436. At W30 no exit above the diagnostic tail threshold2512 is possible in these X windows; not evidence of the asymptotic tail estimate. These data are actual integer slices, not complete-period law and need not have the limiting ratio.

Periodic product audit: for Z=4096,16384,65536, W=2,6,30, both d=0,2, sort all sign priorities p>10W+14, compute the independent residue probability product incrementally, check sum of sign probabilities plus no-event probability equals1, check no-event product equals rho_Z/rho_Z0. Sum gain and raw wait=(a_d(p)p+b-1)/2 for the tail p>max(8Z0,sqrt Z); actual wait subtracts h/2 per selected exit. At W30,Z65536 the nonreset gain shares are .4548989177701766 (d0) and .45149858713097824 (d2); raw wait shares .7145574343908433 and .7117501589532884. These are deterministic numerical evaluations of the derived product at two fixed terminal parities, not full-period enumeration of lower-terminal phase weights. The analytic half and three-quarter limits follow from Mertens and fixed-modulus PNT, not extrapolation. All final local test cases passed; no Lean compilation.

## 7. Next target

Use the exact large-jump post-height and restart decomposition to study the high-height remainder after a nonreset first exit. The periodic moment law shows that discarding nonreset exits merely because they do not return to the reset backbone would lose the dominant time component. The new weighted bound removes all low-height anchored local blocks, even after arbitrary-depth merging, under the stated physical cap. The remaining task is a weighted control of the high-state stretches and of the low-height mass-saturation stops, or a different global deficit; it is not another local packet anti-concentration hypothesis. No new branch, no main edit, no twin-prime proof.
