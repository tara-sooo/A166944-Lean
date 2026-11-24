# Two-exit scale separation and a bounded-gain extension of the high-height remainder

2026-11-25 JST. Continues d673b8076e1761f5214594d159d68f7f2dc55b5f on the SAME research/min-cycle-forest-2026-11-24 branch. Original paper deduction strengthening the preceding low-height restart budget and the older two-high-prefix estimate. Uses the already established dimension-two upper-bound sieve and elementary prime-count upper bounds. Exact finite audits on hypothetical low-height starts and actual source-preserving low-height mass stops. No Lean compilation. Neither the final high-remainder cost nor the mass at low-height stops is bounded sufficiently for twin primes.

## 1. Setup and the two-cell prefix

Use canonical MIN, X dyadic divisible by 4, B=ceil(sqrt(7X)), original N=X/2 odd source tags M in [X,2X), initial (t0,C0)=(M+2,2M-2), individual K(M)=floor((7M-1)/4). At every attained state h=2t-C>=0, an executed event has selected label p<=B, wait w<=2r(C), r(C)<=p<=1.5(p-1), and new height h'=h+2w-(p-1)>=0.

Let H>=6, W an even primorial. For now assume W<=log^(1/4)B, H<=log^(1/2)B, as in the preceding low-height restart budget. Take all hypothetical start states of even height h0 in [0,H], with u in a fixed O(X)-length integer interval containing every actual time, and C0=2u-h0. The audit takes u from X+3 to floor((14X-1)/4). Both parities of u are included. Count the full hypothetical prefix without its individual cutoff; the actual executed part from any such state is a prefix of it.

Run MIN until its SECOND executed exit from its current W-cell, or until a natural terminal before that. Cells are (jW,(j+1)W]. A large jump skipping several cells counts as one exit. All internal events before either exit have gain p-1<W. The sum of internal gains in the two visited cells is <2W, so total internal r-cost is <3W. Write p for the first exit label, q for the second exit label, setting missing labels to zero. Define the cost majorant per start
    f2*(u,h0) = sum_(internal events before/through two exits) r(C) + p+q.
This dominates the actual r-cost of this entire prefix. Put F2*(H,W)=sum over all hypothetical starts f2*. It also dominates the sums of exit labels (not merely r-cost). No estimate on the number of internal events is required.

The preceding low-height restart theorem, for each fixed h0 and parity, gives the bound for the first label
    sum_u p <= O(X [sqrt B + B log^2(2W)/log^3 B]).
Indeed labels <=sqrt B contribute at most X sqrt B; large label counts are O(X alpha_(h0,epsilon)(W)/(p log^2 p)), and alpha<=O(log^2(2W)). That theorem used the fixed lower residue of a terminal inside the cell and a root-slice sieve, not a uniform arrival-mass assumption.

## 2. Scale separation yields an additional saving for the second exit

Let f>=32 be real, allowed to grow slowly. For any fixed height/parity, the contribution from second labels q<=f(p+W+H) is at most f times the sum of first labels plus O(X f(W+H)). The contribution from q<=sqrt B is <=O(X sqrt B), even if the comparability condition failed. Thus consider only q>f(p+W+H) and q>sqrt B. Necessarily p>0 and q!=p.

Write g0 for internal gain before the first exit, g1 for internal gain after its landing and before the second exit. Both are even and in [0,W). The two pre-horizons are
    A=2u-h0+g0,
    C=A+p-1+g1.
Each possible choice of signs sigma,tau in {-1,+1} requires p|A+sigma and q|C+tau. The cumulative gain before the second exit is g0+p-1+g1 < p+2W. Consequently the pre-height h is at most H+5(p+2W) by the elapsed/gain inequality. Nonnegative post-height and the MIN wait bound give
    4r(C) >= q-1-h > q/2,
    r(C)>q/8,
because f>=32. Thus the two neighbors at C avoid all odd prime factors below q/8.

For fixed distinct p,q, g0,g1, signs, h0 and parity, the congruences fix a single residue of u modulo 2pq. The progression interval can be embedded in length n comparable to X/(pq), since pq<=B^2=O(X). We use the same dimension-two upper-bound sieve as in research/2026-11-24-min-reset-prefix-gain-and-depth.md, section 2. Along the progression, the neighbor divisible by q divided by q and the opposite neighbor are affine forms with two distinct forbidden residues modulo every odd sieve prime other than p,q. Their relation has nonzero constant difference +/-2 after the first form is multiplied by q. Omit 2,p,q, and sieve at a small fixed power of min(n,q). The omitted factors are bounded uniformly, the usual small-power sieve remainder is absorbed for large n, and trivial counting covers bounded n. Since q>sqrt B and n<=O(B^2), this gives
    #candidate starts <= O((X/(pq))/(1+log(2+X/(pq)))^2).
The constants are uniform in all the offsets and labels; this estimate does not require that the candidate trajectories actually choose both primes. Multiplying by q gives the required upper bound on the second exit label sum for each tuple. There are O(W^2) offset/sign choices per fixed h0 and parity.

For p<=B^(1/4), n is at least a constant times B^(3/4), so the total of these weighted counts (before the W^2 multiplier) is
    O(X/log^2 B * sum_(p<=B^(1/4) prime) 1/p * pi(B))
     = O(XB log log(3B)/log^3 B).
For p>B^(1/4), use i=floor(log(B/q)), j=floor(log(B/p)). Each harmonic prime sum in one such band is O(1/log B), uniformly, by pi(x)=O(x/log x). The actual separation q>fp forces j-i>=log f-1. Also q<=B exp(-i), and 1+log(2+X/(pq)) is comparable to 1+i+j. Hence the remaining second-label sum is at most
    O(XB/log^2 B * sum_(i,j>=0, j-i>=log f-1) exp(-i)/(1+i+j)^2)
     = O(XB/[log^2 B (1+log f)]).
For the last equality, sum over j first, obtaining O(1/(1+2i+log f)), then sum the geometric series in i. The actual additional gain over the earlier O(XB/log^2 B) two-high estimate is this factor 1/(1+log f). It is obtained by excluding comparable label pairs before doing the CRT count; no additional sieve dimension or independence assumption is required.

Combine both parts, the first-label sum and the at-most-3W internal cost per start, and sum over O(H+1) fixed heights/parities. The new estimate is
    F2*(H,W) <= O(X(H+1) [
          f(H+W+sqrt B+B log^2(2W)/log^3 B)
        + W^2 B (log log(3B)/log^3 B
                      + 1/(log^2 B (1+log f))) ]).
All constants are independent of H,W,f within the stated parameter regime and f>=32. If f is so large that the separated range is empty, the corresponding estimate is simply a harmless overcount. In particular it controls the first two crossing labels of every hypothetical low-height start, including starts at arbitrary previous depths in actual source paths.

## 3. Application at the previous low-height physical mass cap

Use ONLY the optional accounting stop of the preceding note: at every attained V(t,C) with h<=H, stop all active original tags if its mass is >=T=ceil(B log^2 B). No stop at high height is imposed for the following argument. Keep original individual cutoffs. All groups at a horizon are processed in order of increasing C, and at one physical state all active tags face the same stop. Every actual continued start at a low state has fewer than T tags, regardless of any earlier mergers.

Segment each source path from a low state to its next attained low state, accounting stop, or natural terminal. Count the event ending at the next low state in the preceding segment only. Within each segment, first charge the prefix until its second W-cell crossing (including that crossing), or the whole segment if it ends before the crossing. For each tag its charged prefix agrees with the hypothetical prefix from the same start, possibly truncated. Every start is visited at most once per tag, by strict horizon growth. Sum over all physical starts with the mass cap. The total of these charged r-costs is <=T F2*(H,W). The sum of first-two executed crossing labels for these segments is likewise bounded by T F2*. This reasoning counts starts, not all subsequent merges; it does not require a cap on high-state mass.

Take the concrete asymptotic choice
    H=floor((log log B)^(1/4)), with H>=6 eventually,
    W the largest even primorial <=(log log B)^(1/8),
    f=(log B)^(1/4), with f>=32 eventually.
These meet the preceding root-slice assumptions, including the small period D_Z0 for Z0>=2H+10W+14. Both H and W grow to infinity (W in steps). Since X asymp B^2, the new bound implies
    T F2*/X^2
    = O((H+1)[f(H+W+sqrt B)log^2 B/B
               + f log^2(2W)/log B
               + W^2 log log(3B)/log B
               + W^2/(1+log f)]) = o(1).
For example the final term is O((log log B)^(-1/2)), and the other terms decay faster up to constants. This improves the previous one-exit budget while keeping the SAME T=B log^2 B cap. Merely using the older O(XB/log^2 B) estimate for two high events would not give this improvement even for fixed H,W.

## 4. Extend the marked cost through arbitrary-depth bounded additional gain

For a continued high segment after its second executed W-cell crossing, put A0=p+q+H+W, and let d be the cumulative horizon gain AFTER that second crossing. Take s>=1 (allowed to grow). Starting with d=0, charge further executed events while the actual pre-state remains high (h>H), d<s A0, and the next label l<=64s A0. When either d>=s A0 or l>64s A0 is encountered at an executed event, leave that event and the entire remaining high segment uncharged until the next low state (or termination). If a low state is attained earlier, no remainder exists in this segment. If the individual cutoff forbids the next event, there is no executed charge or remainder event.

This extends the charged prefix through arbitrarily many events and W-cells, without a bound on their number. Monotone gain shows that its total additional gain is <65s A0 (including the last charged event even if it overshoots s A0). Since r(C)<=1.5(l-1), the additional r-cost per segment is <=100s A0. For each actual segment reaching its second crossing, both p and q equal the labels of its corresponding hypothetical prefix. For all starts, even those not reaching it, use the harmless upper bound 100s(p+q+H+W) based on hypothetical labels. Therefore the total extended marked cost is
    R_mark <= O(s T [F2*(H,W)+X(H+1)(H+W)]).
For the concrete parameters of section3 and s=(log log B)^(1/8), this is still o(X^2). In particular the final logarithmic term has exponent -3/8, and the added X(H+1)(H+W) term is negligible after multiplying by sT. The result does not use the conjectural LOW phase coefficient eta or the infinite CRT signed-peak limit.

The first executed event of every remaining high portion now satisfies one of two precise alternatives:
    (a) two actual W-cell exits already occurred since the last low state,
        and subsequent gain d >= s(p+q+H+W);
    (b) two exits occurred, d<s(p+q+H+W), and the next label
        l>64s(p+q+H+W).
Case (b) is an abrupt oversized jump. At that pre-state h<=H+5(p+q+2W+d)<=16s A0, since s>=1. Hence 4r(C)>=l-1-h>l/2, so r(C)>l/8. All actual pre-states of the remaining portion stay high until the next low state or terminal by construction. The giant trigger is not counted twice; if (a) holds, use (a) even if the next jump is also large.

Thus the residual high-state cost is restricted to stretches with substantial horizon travel relative to their first two exits, or those entered by a new large rough jump. This is not a proof that their contribution vanishes. The bound in this note is a source-weighted cost deletion, not a per-trajectory upper bound on its whole high-state lifetime.

If no twins exist in the canonical terminal window, the earlier non-twin natural-terminal cost lower bound cX per unstopped root remains valid with this cap. With S_lowstop the number of original tags stopped at a low-height physical state, and R_rem the total unmarked executed cost,
    R_rem >= cX (N-S_lowstop) - o(X^2).
To complete this route would still require an upper bound on R_rem and a sufficiently strong upper bound on S_lowstop (or a joint deficit in those quantities). The old weighted far-coalescence route also remains open. The two-exit estimate and bounded-gain extension do not themselves estimate either remaining term.

## 5. Exact finite audit and persistence

Saved research/min_two_exit_high_extension_audit.mjs and research/min_two_exit_high_extension_results.json, exact remote readback at c341495ce042f110f72286107507803024755bae. Run the same function body for X=1024,4096,16384,65536, W=2,6,30, fixed diagnostic H=6, f=32, s=2, cap T=max(3,floor(B/8)). These are diagnostic thresholds, not the asymptotic cap or slowly growing parameter values. Hypothetical starts: all even h0 in [0,6], all u in [X+3,floor((14X-1)/4)], no time cutoff until the second W-cell exit/terminal. Use exact SPF and clocks, check nonnegative heights, wait bound, both internal gain bounds, total cost/label majorant, and for every separated second exit check r>q/8 and both divisibility constraints. The field F1 in the output is an unused zero; firstSum is the sum of first exit labels, F2 is the actual two-exit r-cost, star is F2*. The numerical results do not test the sieve estimate quantitatively.

Additionally run the actual canonical source population with source-specific K(M) and low-height physical cap. Process all physical V groups at each C, stop only low-height groups at diagnostic T, and track segment restart, first two executed crossings, bounded-gain extension and remainder. For every continued low start compute its hypothetical two-exit cost. Verify each actual prefix <= that cost, individual extension <=100s A0, global prefix <= sum of actual-start budgets <= T times all hypothetical F2, extension <= total extension budget, exact partition of executed r-cost into prefix/extension/remainder, source conservation, and high remainder triggers. No explicit assertion is made about asymptotic vanishing from these finite data. The diagnostic small cap means the actual stopped population is not the analytic one. The audit tests actual integers rather than the previous conditional CRT priority distribution.

At X65536,B678,H6,W6: 655348 hypothetical start states; 625327 first exits,587725 second exits,1165 separated second exits with q>32(p+W+H) and q>sqrt B (895 with p<=B^(1/4),270 with p>B^(1/4)). All pass the roughness and two-congruence check. Hypothetical F2=38685375 and F2*=42233199. For W2 the separated count is3451; for W30 it is zero at this diagnostic cutoff. For X65536 the actual N32768 roots have3849 low-height stops and28919 natural terminals (all classified twin);183597 continued source-segments. With W6 the total executed cost14019428 partitions into prefix4982927, bounded-gain extension4063762 and remainder4972739. With W30 the same actual cost partitions into prefix6946496, extension4131438 and remainder2941494. There are13236 remainder starts at W6 and7081 at W30, all due to the long-gain trigger (a). The giant trigger (b) was not observed in these finite tests, so that implication is a paper-level deduction only in this audit; its assertion is implemented in the code. All structural and numerical ledger checks passed. No Lean compilation.

## 6. Next analytic target

The additional scale-separation saving permits a second exit and a growing-factor bounded-gain high extension under the earlier B log^2 B physical cap. It is a genuine o(X^2) deletion of these portions, not a claim that all high stretches are short. Further work should exploit the explicit residual conditions, including conditional large-jump counts after two known exits and the cost/height effect of prolonged moderate travel. The number of large low-height physical stops also remains a major unresolved term. No new branch, no main edit, no twin-prime proof.
