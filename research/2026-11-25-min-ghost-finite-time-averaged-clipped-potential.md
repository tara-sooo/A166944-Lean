# Finite-time averaged clipped potential: bypass the full lifetime and gap-tail condition

2026-11-25 JST. Continues 34fd312d9821033c951649a8739da52fed27f315 on the SAME research/min-cycle-forest-2026-11-24 branch. Original deterministic potential and probability deductions, exact finite phase tests, and finite-window CRT samples. No Lean compilation. Neither the new finite-time drift condition nor the independent physical far-coalescence upper bound is proved.

## 1. Signed gain at a first passage and its limitation

For the common CRT ghost write g(s) for the relative even horizon gain and h(s)=2s-g(s). When considering attained-event peaks, s must be a selected event time, except that s=0 is allowed. If a first passage of level K occurs at attained time s<=U, all gain through s is nonnegative and totals at most 2s-K. In the preceding high-label return-relation notation, on the good event with at most K0 distinct high labels and every consecutive return requiring intervening LOW gain >R, let F_s and r_s be the fresh and repeat high counts through that passage. Then G_high(s)>=(z-1)(F_s+r_s). Summing the disjoint per-label return intervals gives G_low(s)>=R r_s/K0. Consequently
    (z-1) F_s + (z-1+R/K0) r_s <= 2s-K.
The strict return-gain inequality can improve this weak bound for r_s>0. This is a signed prefix resource inequality, not an unconditional estimate that r_s=o(T/Y); it holds only at a passage within the time window on the good relation event. For the near-top scales of the preceding note it does not alone supply a useful vanishing probability, and later passages may occur after U. Thus the remainder of this note takes a different route: restrict the auxiliary potential to finite time, and account for its artificial boundary exactly. This avoids needing to suppress all negative-height blocks or prove a long gap before a prescribed time.

## 2. Truncated attained-event maximum and exact finite-budget recursion

Return to the canonical MIN setting and the low-only ghost at cutoff Y, as in the clipped-height theorem (447acd0cd16414a86c0dead5938415eae63266c5). L=2 product_(3<=p<Y prime)p. For integer T>=0, define D_{Y,T}(C,t) as the maximum of 0 and the signed height increments over all prefixes of the LOW-only ghost whose LAST EXECUTED event is at elapsed time <=T, starting from even C and time t. A non-event time after the last included event is NOT a candidate peak. In particular D_{Y,0}=0. This is periodic in C mod L and t mod L. It is nondecreasing in T, nonnegative and at most min(2T,5L). The 5L bound is the preceding full-ghost bound.

If a LOW next event exists with selected prime p<Y and wait w>=1, write delta=2w-(p-1), x=(C,t), x'=(C+p-1,t+w). Then
    D_{Y,T}(x)=0, if T<w,
    D_{Y,T}(x)=max(0,delta+D_{Y,T-w}(x')), if T>=w.
At a LOW terminal every finite-budget value is zero. The recurrence follows by splitting the empty prefix from all prefixes containing the first event. It applies to every actual LOW step of the full process, since if that step is selected it is exactly the next LOW ghost event.

Choose integers S>=1 and 0<=K<=S. Let
    f_T(x)=min(K,D_{Y,T}(x)),
    F(x)=(1/(S+1)) sum_(T=S..2S) f_T(x).
Define the averaged finite-time corrected height
    Phi(t,C)=2t-C+F(C,t).
It is a periodic bounded correction to ordinary height, with 0<=F<=min(K,5L). No actual elapsed-time counter is added to the state: the time-budget average defines one fixed potential on the original two-dimensional phase rectangle. In contrast to the full-ghost potential it need not decrease on every LOW event. The following estimate bounds the leakage caused by the finite budget.

## 3. Exact clipping and averaged-boundary estimate

For a selected LOW event and a budget T>=w, the earlier clipped Bellman identity applies to the finite-time recursion:
    [delta+f_{T-w}(x')-f_T(x)]_+
        = min(delta_+,(D_{Y,T}(x)-K)_+).
If w<=S, apply it for all T in [S,2S]. Because f_T(x') is nondecreasing in T and in [0,K], the shifted-budget boundary difference satisfies
    0 <= sum_(T=S..2S) [f_T(x')-f_{T-w}(x')] <= w K.
Indeed the difference telescopes to the sum of the final w terms minus the sum of the first w shifted terms. No independence of the successor phases is needed. Averaging the one-sided bounds and using convexity of the positive part yields
    [Phi(next)-Phi(now)]_+
       <= (1/(S+1)) sum_(T=S..2S) min(delta_+,(D_{Y,T}(x)-K)_+)
            + wK/(S+1)
       <= delta_+ 1{D_{Y,2S}(x)>K}+ wK/(S+1).
The first line is a sharper bound than the second; it accounts for negative ordinary height increments by the exact clipped identity. The boundary term is small for K/S small, not merely because S is large. This is a pointwise bound for every short-wait LOW event, using a fixed state potential rather than resetting a time budget at each event.

At any actual LOW step let r(C) be the least eligible prime. Since p<Y is chosen, r<=p and w<=2r. If w<=S, delta_+<=2w<=4r and K<=S give positive increment <=6r. If w>S, the preceding finite recurrence need not apply to every budget, but the trivial bound delta+F(x')-F(x)<=2w+K<=3w<=6r suffices. Thus at ALL LOW steps
    [delta Phi]_+ <=6r.
For a high q>=Y, using 0<=F<=K gives
    [delta Phi]_+ <=4r(C)+(K-q+1)_+.
These estimates include the possibility that the final event is a first passage. They do not use the long-gap, terminal-repeat, large LOW-gain block or active-occupation conditions.

## 4. Revised canonical first-passage estimate

Use the original canonical MIN small-physical-terminal-class first-passage construction: N=X/2, B=ceil(sqrt(7X)), Y slowly growing with L<=log^(1/4) B, barrier-cell full inverse stopping rule, original individual time cutoffs. Retain only tags ending at noninitial cell stops with terminal physical clock-class mass<=a. Every earlier attained physical state and actual physical event has retained mass<=a by determinism of the suffix and common accounting stop for retained tags. For the first passage of ordinary height H>=max(BL,10B), pre-heights are in [0,H) and all included post-heights <=H+4B. Let Z(H) count these original retained tags attaining H, truncated at their first passage. As in the preceding clipped-height theorem, this is not a bound for arbitrary projected-key masses.

Choose a secondary cutoff 11<=P<=Y and require 2P<=S. Define
    mu_{Y,S}(K)=Pr_(uniform even C mod L,t mod L)(D_{Y,2S}(C,t)>K).
At a selected label p<P, w<=2r<=2p<2P<=S. By section3 the positive corrected gain at this LOW step is at most
    4P 1{D_{Y,2S}(C,t)>K} + 2P K/(S+1).
If P=Y this still applies to all labels <Y; a high q>=Y is not counted here. Count all possible attained pre-states by CRT. In each fixed even horizon and time residue class mod L, the horizon window and pre-height band contain O(X H/L^2) possible actual pairs (C,t). There are L^2/2 residue pairs, and at most a retained tags per actual state. The total positive gain for labels p<P is therefore
    O(a X H P [mu_{Y,S}(K)+K/(S+1)]).
This is a count of all candidate pre-states, not an assumption of equidistribution of actual paths.

For labels P<=p<Y use the 6r pointwise bound. For high labels p>=Y use the preceding 4r plus (K-p+1)_+ bound. The established projected eligible-horizon sieve estimate S_p^cost=O(X/log^2 p), together with O(a H/p) event incidences at each projected (p,C) on the truncated retained paths, gives total r-cost over labels >=P of O(a X H/log^2 P). The high excess gives
    O(a X H sum_(q>=Y prime) (K-q+1)_+/q^2),
using O(X/q) eligible projected horizons for each q. This sum is O(K/(Y log Y)), and vanishes identically if K<=Y-1.

Initial Phi<=6+min(K,5L), final Phi>=H. Sum its increments on all first-passage prefixes; discard negative increments only after using the finite-budget clipped identity to bound LOW leakage. Since min(K,5L)=o(H), we obtain the unconditional estimate
    Z(H) <= O(a X [P(mu_{Y,S}(K)+K/(S+1))
                       + 1/log^2 P
                       + sum_(q>=Y prime)(K-q+1)_+/q^2]).
All constants are uniform in the allowed parameters, with the previous sieve constants. This is a genuine finite-time substitute for the previous full D_Y probability-tail estimate. In particular no information about D_Y after time 2S is used. The additional leakage term is P K/(S+1). The theorem may not be numerically superior at every finite parameter choice.

## 5. A separate sufficient condition on a single infinite CRT process

Let D_infty(T) be the maximum of zero and 2s-g(s) over executed event times s<=T of the infinite CRT ghost from its random initial residues. This is well defined since at most T events are executed, and D_infty(T)<=2T. The earlier common-CRT finite-time cutoff coupling gives
    P(D_{Y,2S} differs from D_infty(2S)) <= 2S sum_(p>=Y prime)1/p^2
                                            = O(S/(Y log Y)).
The equality of peak variables holds whenever event records agree through 2S. This uses the infinite ghost's probability space; there is no identification of an infinite CRT tuple with an ordinary integer.

A sufficient new condition is the existence of integers S_j->infinity with
    D_infty(2S_j)/S_j -> 0 in probability.
By diagonal selection choose integer K_j->infinity with K_j/S_j->0 and P(D_infty(2S_j)>K_j)->0. For instance take a slowly decreasing positive epsilon_j with the corresponding tail going to zero, raise it to at least S_j^-1/2 if needed, and round K_j up. Choose a diverging Y_j>=S_j^2, large enough that K_j<=Y_j-1. Then the finite-time coupling error tends to zero, so mu_{Y_j,S_j}(K_j)->0. Choose P_j->infinity sufficiently slowly with 2P_j<=S_j, P_j<=Y_j and P_j(mu_{Y_j,S_j}(K_j)+K_j/(S_j+1))->0. Finally choose a_j->infinity slowly with a_j<=ceil(log^(1/4)Y_j) and a_j times the remaining bracket in section4 tending to zero. The high excess is exactly zero by K_j<=Y_j-1.

Select Y(B) on this sequence slowly enough that the previously required L_Y<=log^(1/4) B and Y<=c log log B hold, with its associated S,K,P,a. Then Z(H)=o(X) for all H in the prior first-passage range. The previous conditional cell-stop reduction applies unchanged: H0=X/(log^4Y*(1+log log(3B))) is eventually >=max(BL,10B), landing-divisor deletion and low-height clock-class counts remove o(X) other small cell classes. Remaining physical terminal variance and the near-distance bound imply 2 P_phys,far>=N-o(X) on no-twin windows, as before. The separate upper bound on P_phys,far is still open.

This is an ALTERNATIVE sufficient condition to the old full-ghost D_Y/(Y log Y)->0 in probability and to the various quiet-gap criteria. We do not assert a logical implication from the old full-tail condition to this infinite-time-window condition, or conversely at the level of the ghost distributions. The new condition suffices for the canonical first-passage estimate without a full-ghost tail or lifetime bound. In particular, very large peaks of a finite ghost at elapsed times beyond 2S are irrelevant to this new potential. A simple sufficient special case would be last attained event time through 2S=o_prob(S), since the peak is bounded by twice that time, but neither this stronger property nor the displayed signed-peak limit is proved.

## 6. Exact finite phase checks

Saved research/min_ghost_finite_time_averaged_potential_audit.mjs and research/min_ghost_finite_time_averaged_potential_results.json, exact remote readback at b6d26a059fa8297c0cf570fcc7d3d6a5779b806b. For Y=5,7,11, all even-C/time phases of the low period, S=8,16,32, and K=floor(S/4),floor(S/2),S, compute D_{Y,T} for every integer budget T<=2S by exact integer time-DP. Verify monotonicity in T, D<=2T, the exact finite-budget clipped identity for every T>=S when w<=S, the nonnegative boundary difference <=wK, and the pointwise averaged leakage and 6r bound (including w>S). These are integer checks after multiplying averaged quantities by S+1. At Y11,S8 there are 22050 phases, 17868 short-wait and 1032 long-wait eligible phases; 160812 exact finite-budget clipping checks per cap. At S16 and S32, all 18900 eligible phases have w<=S; 321300 and 623700 checks per cap respectively. For Y11,S16,K8, mean D_{Y,2S}=12.0985941, exact tail fraction .4736508, mean positive averaged-potential LOW leakage 2.4304228, mean boundary contribution .0716020. At S32,K8 the exact mean boundary contribution is zero (the relevant clipped values have already stabilized). No original source trajectories resimulated, and the canonical first-passage theorem is a paper deduction.

## 7. Finite-time larger CRT samples

The same script separately draws 512 fixed-seed pseudorandom CRT tuples at S=128,512,2048,8192,16384, finite prime cutoff V=4S, simulating all actual event records through 2S. It records attained-event peaks, not the height at the end of a quiet waiting interval. The finite-time cutoff coupling bounds the probability of a different infinite record by O(1/log S); this is an asymptotic error, not a calibrated numerical error bound on the finite samples. For the finite ghost, an actual terminal state may occur before 2S; the infinite ghost never has a terminal horizon. The samples are not infinite-alphabet trajectories and do not prove any tail limit. All time caps are part of the definition of the measured observable, not censored estimates of a full-lifetime maximum.

Selected results (512 samples each):
    S       mean peak / S     median peak    count peak>S/2    count peak>S/4
    128     .681488            54            236               312
    512     .536789           160            186               279
    2048    .390854           256            140               196
    8192    .339827           422            116               159
    16384   .334494           764            104               155
At S16384,V65536 there are6541 odd primes in the alphabet. Mean peak5480.3515625, 90th percentile20976, 99th percentile36326, maximum45924, 71 samples increase their attained peak in the second half of the observation window. 417 samples reach a finite-alphabet terminal before the simulation ends. The proportion peak>S/2 declines across tested scales, but remains .203125 at the largest tested window. The mean ratio is not tending rapidly to zero over these finite scales, and the tail at the moving cap floor(S/sqrt(log S)) is .275390625 at S16384. These finite results do not establish the new sufficient condition. The exact DP check does not verify the infinite-process convergence or asymptotic canonical result.

## 8. Remaining work

The first-passage potential now uses a finite observation window, with controlled boundary leakage K/S. This removes the need to prove the full lifetime or quiet-gap tail in this route. The concrete new analytical target is sublinear attained-event signed peak in probability for the common infinite CRT ghost along a diverging sequence of time windows. This requires a new probabilistic estimate, not extrapolation from the finite samples. No twin-prime proof, no main edit, no new branch, no Lean compilation.
