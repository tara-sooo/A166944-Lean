# Fresh high-prime landing exclusion and low-suffix reduction for quiet gaps

2026-11-24 JST. Continues 20927623d04482ffd0fd001bee0639202bc16279 on the SAME research/min-cycle-forest-2026-11-24 branch. Original elementary arithmetic and probability deductions, finite shared-CRT diagnostics. No Lean compilation. The clipped-height tail criterion and physical far-merge bound remain open.

## 1. Additional deterministic return constraint

Use the preceding common CRT ghost: initial even horizon residues c_p mod p, time residues b_p mod p and common parity, all independent except the shared parity. At integer tick s the current relative horizon g is frozen until a selected least matching prime q; then g increases by q-1. All statements below concern this ghost, not a claim of uniformity for actual canonical source trajectories.

If p>=5 has just been selected, its post-horizon residue c_p+g is 0 or -2 mod p. To become eligible again an additional nonnegative even horizon gain d must bring this residue to +1 or -1. Starting at 0 the least such d is p-1; starting at -2 the least is p+1 (p>=5). Thus any two consecutive selections of p>=5 have intervening gain (from immediately AFTER the first to immediately BEFORE the second) at least p-1, in addition to the previous clock separation >=p-2. For p=3 the -2 residue is already +1, so this horizon exclusion does NOT hold. Consecutive post-horizons for the same p>=5 differ by at least 2(p-1). This arithmetic constraint is independent of the elapsed clock, and holds in every finite cutoff and in the infinite CRT ghost.

## 2. Fresh-high landing exclusion

Let U be an integer time horizon, z>=11 with z^2>=2U, and let 0<=R<z-1. Call a selected label q>=z fresh if this is its first selection anywhere on the path. Reveal the selected tick labels through each time s, as in the preceding exact conditional-history law (one may reveal the coordinates for p<z at time zero). Let K_s be the number of previously selected distinct p>=z at time s. A fresh high event is called bad if at its POST-horizon g' some previously selected p>=z is eligible at one of the even horizons g'+d, 0<=d<=R. Its own q is automatically ineligible throughout that range by section 1.

Condition on the history before tick s, with pre-horizon gain g. For each known p>=z its c_p is known. If a fresh q lands badly for this p at offset d, then
    q = +/-1 - c_p - g +1 - d (mod p).
For each fixed p,d and sign this restricts q to a single residue class mod p. The conditional probability of selecting any particular UNUSED q>=z at tick s is at most 1/(q^2-(s-1)) <=2/q^2, by the exact history law; requiring q to win the tie only reduces this. For a residue class modulo p>=z,
    sum_(integer q>=z in that class) 1/q^2 <= 1/z^2+1/(p z) <=2/z^2.
Indeed the first term has q0>=z and the remaining sum is bounded by the integral of the decreasing function (q0+p x)^-2. This deliberately counts all integers, not only primes; it requires no distribution of primes in large-modulus progressions. Summing over the O(R+1) even offsets and two signs gives
    Pr(bad fresh high event at s | past)
        <= O((R+1) K_(s-1)/z^2).
The preceding single-prime deletion bound gives
    E K_s <= s sum_(p>=z prime)1/p^2 = O(s/(z log z)).
This remains true with arbitrary repeats of smaller or larger labels. Therefore
    E[number of bad fresh high events through U]
        <= O((R+1) U^2/(z^3 log z)).
In particular the probability that ANY such event through U is bad obeys the same bound. This holds uniformly over finite upper alphabets >=z and for the infinite CRT process. For fixed 2/3<theta<1 and 0<rho<3theta-2 choose z=ceil(U^theta), R=floor(U^rho). Then the bound is O(U^(rho+2-3theta)/log U)=o(1). Since rho<theta, R<z-1 eventually. Thus, with probability tending to one, EVERY fresh high event in the whole time window lands in a forward interval of horizon length R on which ALL already selected high primes, including its own label, are ineligible. This is an all-depth probability bound for known-prime reactivation at fresh landings; it does not say those primes remain inactive beyond that interval, or after a repeat high event.

A separate first-selection gain bound follows from the deletion estimate: for finite upper cutoff V and z>=sqrt U, the expected sum of (q-1) over FRESH selections q in [z,V) through U is <= U sum_(z<=q<V prime)1/q. By Mertens this is O(U(1+log(log V/log z))) for V>=z, and O(U) for V<=U^A with fixed A and z>=sqrt U. It does not bound all repeat gains. In the infinite process the sum over all q>=z of 1/q diverges, so one must not assert a finite first-gain expectation by this argument. Truncation at V=U^2 loses probability only O(U/(V log V)) by the prior coupling bound.

## 3. A second unconditional deletion: short interferences by fresh high primes

Let v>=1 be an integer with U+v<=2U and z^2>=4U. For any stopping time s<=U for the revealed history, the conditional probability that an unused high prime is selected in the next v ticks, before any other fresh high selection, is at most
    O(v/(z log z)).
Use the conditional probability bound at each tick, sum over unused primes, and stop at the first such selection. This holds even if other already known primes are selected before it. In particular apply after time zero and after every fresh high selection through U. The expected number of fresh high selections through U is E K_U=O(U/(z log z)), so by conditioning at their stopping times and summing (nonnegative expectations, or enumerating the possible first-selection ranks),
    Pr(some fresh high event within v ticks after time zero
       OR within v ticks after another fresh high event through U)
      <= O((1+U/(z log z))*v/(z log z)).
The event can include a second fresh selection up to U+v. No independent trials assumption is used. For z=ceil(U^theta) with theta>2/3 and v=floor(U^rho), rho<3theta-2, this is o(1), since rho<2theta-1 and rho<theta. This estimate and section2 can be applied simultaneously. It is not a deletion of repeat high selections.

## 4. Conditional reduction to short low suffixes, with no known-high blockers

The preceding estimates isolate a precise sufficient low-only suffix target. Take the infinite CRT ghost, Y tending to infinity, T=floor(Y sqrt(log Y)), w=2Y, U=T+w, z=ceil(U^theta) for fixed 2/3<theta<1, R=v=floor(U^rho) for fixed 0<rho<3theta-2. Then U asymp T, z<Y eventually, z^2>=4U, and v=o(Y). Reveal p<z initially. Consider the LOW-only (<z) deterministic ghost from time zero and from the actual post-state of EACH fresh q>=z selected by time T. Define BadLow to mean that at least one of these continuations has elapsed lifetime >v or total horizon gain >R. This event depends on actual low coordinates, and its probability has NOT been bounded; it is not a uniform-residue fresh start assumption.

Outside BadLow and the two o(1) exceptional events of sections2-3, the infinite process proceeds as follows up to T:
- the initial LOW continuation finishes with no high interference (no previously selected high, no fresh selection for v ticks);
- at its terminal horizon no low label is eligible, and no known high is eligible; the next event, if before T, is a fresh high;
- after each such fresh high event the LOW continuation stays within its R horizon interval and v time interval. All known high primes are ineligible there by section2, and no fresh high can interrupt it by section3. Thus it finishes exactly at its LOW-only terminal, again with neither low nor known high eligible.
Inductively, every high event before T is fresh, and every such LOW terminal reached by T is a quiet-gap opportunity as in the preceding conditional law. This induction does not use projected-clock identification or treat previously selected high primes as independent.

At each opportunity time s<=T (an attained state, or time zero), the conditional probability of no event over the next w ticks is at least c_theta>0: all p<z and all known p>=z are ineligible, unused high coordinates have at most s exclusions, z^2>=2s, and log z/log(2w)->theta. Apply the earlier Mertens product lower bound. The good-event induction is used to count opportunities, NOT as a conditioning event for the gap probability. In particular do not condition the product law on BadLow or its complement in addition to the history; the gap probability is conditional only on the revealed history at each opportunity.

Test opportunities in time order, ending each test at the first event if it occurs within w ticks, otherwise at s+w with success. After a failed test seek the next opportunity. All tests are history stopping times (all p<z known, previously selected high coordinates known); failure is known before the next test. On the good event and sigma_Y>T (no gap >w starting by T), the initial opportunity occurs by v, and after a failed test the next fresh high event occurs within w and its LOW block finishes within v. Consequently at least m=floor((T-v)/(w+v)) tests start by T and fail, for large Y, and m tends to infinity. Their successive conditional failure probabilities are at most 1-c_theta. Thus
    Pr(sigma_Y>T)
     <= Pr(BadLow)
       + O((R+1) U^2/(z^3 log z)
            +(1+U/(z log z))*v/(z log z))
       +(1-c_theta)^m.
The conditional probability of the first m failures is bounded by induction with the existence/start-time restrictions imposed at each test, without requiring any independence or conditioning on future good events. All other displayed error terms tend to zero. If Pr(BadLow)->0 along a diverging sequence, this would prove the preceding clipped-height tail criterion via the finite-time coupling, and remove the small physical cell-stop residual. The separate physical far-merge upper bound would remain open.

This sufficient condition is demanding: for power choices rho<3theta-2<theta, the allowed low suffix length is much smaller than the cutoff z. The finite sample below shows that most tested fresh landings do NOT have such short low suffixes. It would be unjustified to assert that BadLow is small based on the successful landing exclusion alone. The theorem identifies the obstruction as the size of the low continuation, rather than immediate reactivation of known high primes at a fresh landing. One possible next improvement is to replace the worst-case interval of all even offsets up to R by the particular attained offsets of a low suffix, rather than requiring a whole interval to avoid known high labels. That would require treating the dependence of the suffix on q, not using a union bound with a fixed path independent of q.

## 5. Finite audit

Saved research/min_ghost_fresh_high_landing_audit.mjs and results JSON, exact remote readback at a91e40d1c4b578b65f4ccaffa89e2e2c132fde62. 2048 fixed-seed pseudorandom common CRT residue samples for each Y=53,199,397,797,1597 with finite V=8Y, T=floor(Y sqrt(log Y)), z=ceil(T^.8), R=floor(T^.3), rather than the section4 U. Enumerate finite ghost event paths through T. Verify every consecutive repeat time separation p-2 and, for p>=5, intervening even gain >=p-1. Check the exception for p=3 separately; an initial diagnostic assertion without this restriction failed, corrected before saving. At fresh high landings verify exact reactivation congruence for every previous known high prime and own-label exclusion throughout offsets <=min(R,p-2). From every good fresh high landing test whether the low-only (<z) continuation terminates before either elapsed time or gain exceeds R. This is a deliberately truncated test for the short-suffix condition, not a numerical evaluation of the entire suffix distribution. The analytic probability bounds are paper deductions, not tested as sharp numerical bounds at these finite parameters. The sample is not an infinite-alphabet simulation.

Selected finite counts:
    Y     T     z    R  fresh high  bad landings  repeat high  good short suffixes
    53   105    42   4    928           8             4              139
    199  457   135   6   1029           7             2              131
    397  971   246   7   1041           3             2              100
    797 2060   448   9   1110           3             2               98
    1597 4337  813  12   1190           3             1              118
At Y1597 there are 46102 repeat-clock checks including 2278 p=3 exceptions to the horizon gain condition; 454 known-high congruence checks; bad landings occur in 3/2048 runs. There are 1187 good fresh landings, but only 118 tested short low suffixes. These figures are counts across event incidences, not independent per-event estimates or a confidence bound. No original source trajectories or Lean compilation in this turn.

## 6. Remaining work

The fresh-high landing exclusion and short fresh-interference deletion are unconditional asymptotic estimates. They do not by themselves prove many quiet gaps. The sufficient low-suffix condition in section4 is not established and is restrictive in finite samples. Further work should seek reactivation bounds for actual low suffix offsets or less restrictive low-suffix termination estimates. The clipped-height tail and physical far-merge upper bound remain open. No main edit, no new branch.
