# Clipped corrected height: a probability-tail criterion without a first-moment assumption

2026-11-24 JST. Continues 4c28d044315faa350bf709c06b16554385cac24a on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions and exact finite residue tests, plus larger fixed-seed CRT samples. No Lean compilation. No proof of twin-prime infinitude or full stopping deficit.

## 1. Clip the LOW-only Bellman potential

Use the preceding canonical MIN small-terminal-physical-class first-passage construction, N=X/2, B=ceil(sqrt(7X)), original source cutoffs, Y tending to infinity sufficiently slowly with Y<=c log log B, L=2 product_(3<=p<Y prime)p<=log^(1/4) B. Use the barrier-cell full inverse stop rule. Retain only the original tags ending in noninitial cell-stop crossing clock classes of mass <=a. Each attained physical pre-state (t,C) as well as each executed physical event (p,C,n) is visited by at most a retained tags: identical actual state forces identical deterministic future and identical accounting stop for all retained tags, since natural truncation cannot intervene on a retained stopped path. This applies also at an original initial state. Every individual path has strictly increasing C at events, so the same tag never revisits an attained state. No assumption on projected masses or phase distribution.

Let D_Y(C,t) be the earlier nonnegative maximum signed prefix gain of the complete LOW-only deterministic ghost, periodic in C and t mod L. It lies in [0,5L]. Let K>=0 be a clipping level, and define
    d_K(C,t)=min(K,D_Y(C,t)),
    Phi_K(t,C)=2t-C+d_K(C,t).
For a real LOW event with wait w and label p<Y, delta=2w-(p-1) and the ghost's next event is exactly this event. Put D=D_Y(C,t), D'=D_Y(C+p-1,t+w); Bellman recursion gives D=max(0,delta+D'). Then the EXACT positive increment of the clipped potential is
    [Phi_K(next)-Phi_K(now)]_+
       = min(delta_+, (D-K)_+).
To prove: if D<=K, delta+min(K,D')-D<=0. If D>K, then D=delta+D'; delta+min(K,D')-K=min(delta,D-K). Taking positive parts yields the identity. It includes K=0 and K>=max D. At a horizon with no LOW eligibility define the LOW leakage to be zero (no actual LOW step is possible). Thus clipping creates positive leakage only at pre-states with D>K, and its magnitude is bounded by the ordinary positive height increment <=4r(C). The large value of D itself does NOT multiply this leakage. This is why a probability-tail criterion can replace a first-moment bound.

## 2. First-passage theorem with a clipped correction

Truncate the retained hitting paths at their first attained h>=H, where H>=max(BL,10B), and let Z(H) count distinct hitting tags. All executed event post-heights <=H+4B; all pre-states satisfy 0<=h<H, including the initial state. At a fixed projected key (p,C) each possible event clock lies in one mod2p progression, so there are O(H/p) possible clocks, and at most O(aH/p) retained incidences. The established per-prime cost sum S_p^cost=O(X/log^2 p) holds for p>=11, uniformly. Choose a secondary cutoff 11<=P<=Y and K<=5L (or clip at min(K,5L) without changing the function).

Define Lambda(Y,K,P) as the full uniform phase-rectangle mean of
    1{ghost has next LOW label p<P} min(delta_+, (D_Y(C,t)-K)_+).
All phases without a LOW event contribute zero. In particular
    Lambda(Y,K,P)<=4P mu_Y(K),
    mu_Y(K)=Pr_(uniform even C mod L, t mod L)(D_Y(C,t)>K).
No assumption about actual path phases is made. For a fixed residue pair C0 even,t0 mod L there are O(X/L) possible actual even horizons in the window and for each horizon O(H/L) possible actual attained pre-times with 0<=2t-C<H. Count all these pre-states (even if unreachable). Each supports <=a retained tags. Therefore the total positive clipped gain from executed labels p<P is O(a X H Lambda). This directly counts pre-states, not candidate waits per post-clock. It remains valid if a small label occurs many times on one path.

For LOW labels P<=p<Y the clipped positive increment <=4r(C) by section1. For every high q>=Y, the clipped increment is bounded by
    delta Phi_K <=4r(C) -(q-1)+K <=4r(C)+(K-q+1)_+.
The per-prime sieve and clock incidence bound yield total 4r over ALL p>=P bounded by
    O(a X H sum_(p>=P prime)1/(p log^2 p))
      =O(a X H/log^2 P).
The extra high term is bounded by
    O(a X H sum_(q>=Y prime)(K-q+1)_+/q^2)
       <=O(a X H K/(Y log Y)),
using O(X/q) projected eligible horizons and O(aH/q) incidences per key. In fact there is no extra high term when K<Y-1. These estimates overcount positive gains, so all negative clipped changes may be discarded without affecting the upper bound.

Initial Phi_K<=6+K, final Phi_K>=H. Consequently
    Z(H)(H-6-K)
      <= O(a X H [Lambda(Y,K,P)+1/log^2 P
                       + sum_(q>=Y prime)(K-q+1)_+/q^2]).
Since K<=5L=o(H), conclude
    Z(H) <= O(a X [Lambda(Y,K,P)+1/log^2 P+K/(Y log Y)])
         <= O(a X [P mu_Y(K)+1/log^2 P+K/(Y log Y)]).
Constants here are absolute apart from the already established sieve constants and fixed horizon-window factors. No full Gamma(Y) or A_+(Y) mean estimate is required. This is a different unconditional first-passage upper bound, not a proof that any of its bracketed terms vanish in a particular limit. It counts only the retained small physical terminal-class population as in the previous theorem. It cannot be applied to arbitrary projected masses.

## 3. Weaker sufficient distributional condition

It suffices along a diverging sequence of Y to have
    D_Y/(Y log Y) -> 0 in probability
with respect to the uniform residue rectangle (different finite probability spaces for different Y). Equivalently there exist K(Y)=o(Y log Y) such that mu_Y(K)->0. One direction is immediate; the other follows by a diagonal choice of positive epsilon_Y->0 for which Pr(D_Y>epsilon_Y Y log Y)->0. Round K to an integer and replace by min(K,5L) if necessary. This condition is implied by A_+(Y)=o(Y log Y) via Markov, but it does not in general require uniform integrability or control of the first moment. No converse implication for the specific MIN ghosts is proved. Nor do we assert that this criterion is logically weaker than the previous Gamma(Y)->0 criterion, which can use other cancellation.

Take P->infinity sufficiently slowly with P<=Y and P mu_Y(K)->0, for example P=min(Y, max(11,floor(mu_Y(K)^(-1/2)))) eventually if mu>0, and P=Y when mu=0. Then take integer a->infinity slowly enough, a<=ceil(log^(1/4)Y), such that a times the bracketed coefficient tends to zero. Thus Z(H)=o(X). A convenient sufficient special case would be tightness of D_Y/Y in probability (uniformly small tails beyond growing multiples of Y), since then K=floor(Y sqrt(log Y)) is o(Y log Y) and mu_Y(K)->0. Tightness itself is not proved. A still more targeted condition is Lambda(Y,K,P)->0 for slowly growing P and K=o(Y log Y), without requiring the full unweighted tail probability to vanish.

Use the same conditional cell-stop reduction as the preceding note: choose Y(B) on the sequence sufficiently slowly for L<=log^(1/4) B and Y<=c log log B, H0=X/(log^4 Y*(1+log log(3B))), Q=ceil(L log B), Dscale=floor(sqrt(a)). Then H0>=max(BL,10B) eventually. Landing-divisor deletion at q>=Q costs o(X) tags; clock-class counts at q<Q,h<=H0 cost O(a log^2Y [Q+H0(1+log log(3B))])=o(X) small-class tags. The new Z(H0) bound removes the remaining high-height small classes if the probability condition holds. Initial cell injections cost o(X). Large cell physical classes have within-class variance >=S_c/2-o(X) at Dscale, and prime-stop moments give within-clock variance >=S_p/2-o(X), with the harmonic near deletion as before. Therefore the same conditional necessary inequality on no-twin windows is 2 P_phys,far>=N-o(X). The physical far-merge upper bound remains a separate open task. Neither the new probability condition nor that upper bound is proved here.

## 4. Exact finite checks and expanded full-path sampling

Saved research/min_clipped_height_potential_audit.mjs and results JSON, exact remote readback at f381251d35391ef884d3dd69ebd27bfa02c74865. Compute D, next LOW label, signed delta and successor D at every phase for Y=5,7,11,13 using exact backward integer DP. At each phase and each tested cap (0,Y,2Y,floor(Y sqrt(log Y)),floor(Y log Y),max D; duplicates removed) check EXACT clipped positive increment identity and support bound, small-P mean leakage <=4P times its joint tail frequency, and all-phase sums. These are exact finite integer recursions with rounded output means. At Y13 (2668050 phases), K20, tail0.3153501621, full LOW leakage mean1.67191919, P5 leakage0.90629111, P11 leakage1.47033751. At K33, tail0.1803489440, full leakage0.90703135, P5 leakage0.48684470, P11 leakage0.80954030. Max D192; K192 produces zero leakage. The first-passage theorem is a paper deduction; this new code checks the pointwise LOW identity and phase statistics, not a rerun of full source paths.

Saved separate research/min_clipped_height_potential_sample.mjs and results JSON, exact remote readback at 91ac51a2f8b2c2569386bd74bfe022bd1746f642. At each Y in 13,53,101,199,397,797,1597 draw 8192 fixed-seed pseudorandom CRT residue states (even C residues independent over odd primes, time residues independent over odd primes with common parity), run the entire deterministic LOW-only ghost to termination, track maximum signed prefix and first event's label/delta. No high-q sum is sampled or truncated in this diagnostic. All runs terminate before the 20000-step guard (maximum observed415). Thus the sample D values are complete, not censored. Report exact empirical frequencies/quantiles and clipped leakage via the identity. These are not rigorous bounds on the full residue population, in particular not a proof of uniform tightness or convergence in probability. Large unobserved D values may still contribute to the mean; the new criterion only needs their frequency.

Selected empirical results with K=floor(Y sqrt(log Y)), P=11:
    Y     K      tail Pr(D>K)    P11 leakage mean   median D   90% D   99% D
    13    20     .309204         1.465820           10         46      100
    53    105    .177246         .658936            30         148     328
    101   216    .124390         .445313            46         244     506
    199   457    .082642         .318726            70         416     902
    397   971    .052856         .188965            94         700     1634
    797   2060   .033081         .131104            138        1230    2882
    1597  4337   .018677         .063843            192        2106    5118
At Y1597, 153/8192 samples exceed K4337; 1150/8192 exceed Y itself; 1/8192 exceeds floor(Y logY)=11779. Largest sampled D11850, mean687.145508, mean steps28.150757. At K4337 the full LOW leakage mean is .51159668 and P5 leakage .04968262. The empirical decline at these cutoffs motivates the probability-tail condition; it does not supply the bound. The finite K/(Y logY) is about 1/sqrt(logY), so the small observed tail or leakage alone cannot quantify the entire first-passage theorem at these finite Y.

## 5. Remaining work

The previous research needed control of a first moment or of the full nonnegative high residual coefficient. The clipped potential gives an alternative sufficient tail-frequency criterion and separates exceptionally large values from their magnitude. Next seek a rigorous tail bound for D_Y/(Y log Y), or directly Lambda, via the distribution of actual deterministic LOW prefix paths on the CRT rectangle. In particular a count of rare long paths, not their maximal total lengths, now suffices. No full stopping deficit or twin-prime proof. No new branch, no main edit, no Lean compilation.
