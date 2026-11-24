# Clock-only suffix guards and terminal offset support for fresh high landings

2026-11-25 JST. Continues 91721e316067dffb7657fd20c72c519cb31d5f1d on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary probability deductions from the exact CRT conditional-history law and finite shared-residue diagnostics. No Lean compilation. The clipped-height tail condition and the independent physical far-coalescence upper bound remain open.

## 1. Protect the interior of a LOW suffix by clocks alone

Use the common infinite CRT ghost and its finite restrictions from the previous notes. Let U be a positive integer time horizon, z>=11 with z^2>=4U, and integer 1<=v<z-2, v<=U. Reveal the coordinates of all odd primes <z initially. At each integer tick reveal the selected label (0 for no event). A fresh high event is the first selection of any q>=z. For an unused q at a tick s<=U+v the exact conditional-history law gives selection probability <=1/(q^2-s+1)<=2/q^2. Hence the conditional probability of any fresh high event at a tick is O(1/(z log z)). The earlier deletion bound gives P(p seen by U)<=min(1,U/p^2)=U/p^2 for p>=z. These assertions also hold for an arbitrary finite upper alphabet.

After a fresh q event at time s, call the next v ticks clock-guarded if there is NO possible clock of any previously selected high p>=z in (s,s+v], irrespective of whether its horizon residue would be eligible. This guard depends on the actual known time coordinates, not on any hypothetical low trajectory or on its horizon gain. For the new q itself, the two possible time classes mod 2q are separated by q-2 or q+2; since v<z-2<=q-2, there is no possible q clock in that interval.

For any already seen p, the number of integer starts s in [1,U] for which a possible p clock lies in (s,s+v] is O(v(1+U/p)): at most two potential clock residues in each period 2p, and at most v starts per clock. This is a pathwise bound independent of the random time phase. Count only starts after p has first been selected, so the count is bounded by that quantity times the indicator that p has been seen by U. At a tick s the fact that p was previously selected and its potential clock in (s,s+v] are history-measurable BEFORE tick s. Multiply this indicator by the uniform conditional fresh-high hazard and then sum over ticks and p. The expected number of fresh high events through U violating the known-clock guard is at most
    O(1/(z log z) * v sum_(p>=z prime) (1+U/p) U/p^2)
      = O(v U/(z^2 log^2 z) + v U^2/(z^3 log^2 z)).
Thus the probability of ANY violation is at most the same bound. This is an unconditional all-depth probability estimate. It does not require a bound on the gain, number of events, or distribution of the LOW suffix following a fresh q. It even excludes impossible clocks that would not match the horizon.

Combine with the preceding fresh-interference bound: the probability of a fresh high event in the next v ticks following time zero or any fresh high event through U is
    O((1+U/(z log z))*v/(z log z)).
Include starts at time zero; there are no previous high labels at that time. In the absence of both exceptions, any deterministic LOW-only (<z) continuation from a fresh high post-state that finishes in <=v ticks is an exact suffix of the full process up to and including that LOW terminal, no matter how large its total horizon gain. This follows by induction over ticks: already seen high labels have no possible clock, the newly selected q has none either, and no fresh high is selected. If an unseen high matches at a LOW event tick but loses the tie, that does not affect the trajectory. No assertion is made about the high labels at the LOW terminal AFTER the guarded interval.

## 2. Terminal offset support: replace an entire gain interval by actual endpoint values

A long quiet-gap opportunity needs the known high labels to be inactive at the LOW terminal, not just while the LOW suffix is running. The previous gain-interval theorem required every even gain in [0,R] after the fresh high landing to avoid reactivation. We now separate the endpoint from the interior and count only distinct attainable endpoint gains.

At tick s<=U, condition on the entire revealed history BEFORE tick s, including all low coordinates, parity, and relative pre-horizon g. For every candidate UNUSED prime q>=z, consider the deterministic LOW-only ghost from the hypothetical post-state (time s, horizon gain g+q-1). Let tau_q be its elapsed lifetime and d_q its total even horizon gain. They are determined by the prehistory, q, and s, without revealing any fresh high coordinates. This is a counterfactual continuation and need not be the actual full path. For the finite upper alphabet use only its unused candidates; for the infinite alphabet use all unused q>=z.

Define the endpoint support
    D_s(v) = {d_q : q is an unused candidate >=z, tau_q<=v},
    M_s(v) = |D_s(v)|.
This is history-measurable before the tick. The support is finite even for the infinite alphabet, since every terminating suffix with tau_q<=v has at most v events of gain <z, hence 0<=d_q<=v(z-1). There are at most floor(v(z-1)/2)+1 possible even offsets. No assumption that q and d_q are independent, or that the lower coordinates are freshly resampled after the jump.

If a previously selected high p is eligible at this hypothetical LOW terminal, then
    q == +/-1-c_p-g+1-d_q (mod p).
For any fixed d in the support and each sign, the sum of q^-2 over all integer q>=z in this residue class mod p>=z is <=1/z^2+1/(pz)<=2/z^2, by the decreasing-function integral bound. Thus the probability, conditional on the prehistory, of selecting a fresh q whose suffix finishes within v and whose terminal reactivates some previous high p is
    <= O(M_s(v) K_(s-1)/z^2),
where K_(s-1) is the number of already selected high labels. This bound is a union over distinct TERMINAL offsets across candidates, not all offsets visited in their interiors. We do not sum over q-specific paths as though those paths were independent of q.

The new q may also become eligible at the terminal, even when there was no q clock during the interior. Its post-event residue is 0 or -2, so reactivation requires q to divide at least one of
    d_q-1, d_q+1, d_q-3.
These are nonzero odd integers, since d_q is even; their absolute values are <=v(z-1)+3. For v<z-2 and z>=11 their absolute values are <z^2. Each has at most one distinct prime factor >=z (the weaker O(1) bound also suffices). Summing over d in the support gives conditional probability O(M_s(v)/z^2) for fresh selection with own-label terminal reactivation. This handles own q without requiring d_q<q-1. The actual side determines which divisibilities suffice; using all three is an upper bound.

Combining the two estimates,
    P(fresh q selected, tau_q<=v, some known high label including q eligible at terminal | history)
         <= O(M_s(v)(1+K_(s-1))/z^2).
This is valid without a deterministic bound on the terminal gain other than the automatically implied v(z-1). It may be sharpened by counting only the actual q satisfying each congruence, or by restricting each d support to a high-label subband. A small observed support is not automatically a uniform support bound.

For integer M>=1 let BadSpread mean some actual fresh high event through T<=U occurs at a history with M_s(v)>M. On the complement of BadSpread, the probability of any fresh high event through T having tau_q<=v and terminal reactivation is bounded by summing the preceding conditional inequality with indicator M_s(v)<=M. Since E K_s=O(s/(z log z)),
    P(terminal reactivation at a fresh event with tau_q<=v and M_s(v)<=M through T)
         <= O(M U/z^2 + M U^2/(z^3 log z)).
No conditioning on the future event BadSpread or its complement is used in this sum. Alternatively the exact expectation O(z^-2 sum_s E[M_s(v)(1+K_(s-1))]) gives a bound without a spread threshold. In a finite restriction this expectation uses its actual candidate support; the infinite statement requires the infinite candidate support. The latter can be calculated in principle by using all q residues of the low period, but it is not bounded by the finite sample support.

## 3. Updated quiet-gap reduction with independent time and terminal-support cutoffs

Take Y->infinity, T=floor(Y sqrt(log Y)), w=2Y, U=T+w, and z=ceil(U^theta) for fixed 2/3<theta<1. Let v and M satisfy the above conditions. BadTime means that the initial LOW-only continuation, or the continuation after any actual fresh high event by T, has lifetime >v. Unlike the earlier BadLow, this definition has NO condition on its total horizon gain. BadSpread is the preceding history support event. On the complement of these two events and the unconditional clock/fresh/terminal exceptions, the initial LOW continuation and each fresh-high LOW suffix finish exactly, with no eligible low or known high label at their terminal. Every next high event is then fresh. This is the same inductive quiet-gap opportunity argument as the previous note, but using the clock-only protection and endpoint test.

At each such terminal the exact conditional-history law gives a probability at least c_theta>0 of no event for w more ticks: no known label is eligible, unused high coordinates have at most s exclusions, z^2>=2s, and log z/log(2w)->theta. The product estimate is conditioned ONLY on the revealed history, not on any future good event. As before test opportunities in increasing time, ending each test at its first event or at success after w quiet ticks. On the good event and sigma_Y>T, the initial opportunity occurs by v and each failed test yields a new opportunity within w+v. Thus at least m=floor((T-v)/(w+v)) tests start by T and fail. Iterating conditional failure probabilities, with the existence/start-time conditions imposed at each test, gives
    P(sigma_Y>T)
    <= P(BadTime)+P(BadSpread)
      + O((1+U/(z log z))*v/(z log z)
          + v U/(z^2 log^2 z) + v U^2/(z^3 log^2 z)
          + M U/z^2 + M U^2/(z^3 log z))
      + (1-c_theta)^m.
All algebraic terms vanish, for example, at fixed theta in (2/3,1) with
    v=floor(U^(3theta-2) (log U)^(3/2)),
    M=ceil(U^(3theta-2) (log U)^(1/2)).
Then v=o(Y), v<z-2, and m->infinity. The last clock term is O(1/sqrt(log U)); the last terminal term is also O(1/sqrt(log U)). The other powers vanish since theta<1. At theta=4/5 this allows time U^(.4) log^(3/2) U independently of terminal support U^(.4) sqrt(log U), without imposing any comparable cap on horizon gain. The previous all-offset bound had a factor R and imposed a whole gain interval as well as v. This is a genuine separation of the two restrictions, not a proof of either required probability limit.

If BadTime and BadSpread have probability o(1) along a diverging sequence, the prior finite-time coupling gives the clipped-height probability criterion, hence small-physical-class cell-stop deletion. No proof of either probability bound is obtained here. BadTime can still be demanding because v is smaller than z by a power for fixed theta. Also the mere number of actual suffix steps is not M_s: M_s counts endpoint values across ALL hypothetical unused high q at that prehistory. Substituting the number of steps on just the realized suffix would be invalid. The independent physical far-merge upper bound is still required for a twin-prime result.

## 4. Finite audit

Saved research/min_ghost_clock_guard_terminal_offsets_audit.mjs and research/min_ghost_clock_guard_terminal_offsets_results.json, exact remote readback at c4c84a8cf32065656db06045252273534a38e506. For Y=53,199,397,797,1597 run 512 fixed-seed pseudorandom shared CRT initial states, finite upper alphabet V=8Y, T=floor(Y sqrt(log Y)), z=ceil(T^.8). Enumerate actual fresh high events through T. At each test caps v=floor(T^.3), floor(sqrt z), floor(z/4) (deduplicated). Replay counterfactual LOW-only continuations until terminal or time cap. Verify the clock-only inclusion: any actual possible known-high match on any frozen LOW horizon within the capped trace implies that label has a possible time clock in the interval. The trace is frozen after the last included LOW event through the cap. Check own clock exclusion for v<q-2, known-high terminal congruence, and own terminal divisor necessity at all finished actual fresh suffixes. For the first64 fresh-high prehistories per cap enumerate ALL unused candidate primes >=z and <V, compute the capped LOW continuation and exact finite terminal offset support. Check even gain and gain<=v(z-1). The finite candidate enumeration is not an exhaustive infinite-alphabet support calculation. The actual samples are not independent across fresh events within one path. The analytic bounds are paper proofs, not numerical upper-bound fits.

At Y1597, T4337,z813,V12776: 281 fresh high events, no repeat high events in this particular sample of512 paths. For v12 there are35 finished actual LOW suffixes,7 with gain>12; one known-clock guard violation over all281 fresh events, no actual known-high matches on the counterfactual capped trace, no terminal reactivation among35. For v28:54 finished,13 with gain>28, one known-clock violation, no terminal reactivation. For v203:127 finished,21 with gain>203,12 known-clock guard violations over all281, 121 finished suffixes pass the clock guard and terminal test. No own-clock violation or actual known/own high match on any of these capped counterfactual traces. In the first64 prehistories at v203, 40635 candidate (history,q) pairs finish within cap, sum of support sizes8967 (mean140.109375), maximum support173, maximum terminal offset1554 (the maxima need not occur in the same history). The support is appreciably smaller than the worst-case gain interval in those finite tests. No candidate known or own terminal reactivation at these64 histories with v203. At Y797,v112, 20409 finite candidate pairs finish, 10 have known terminal reactivation and2 satisfy the conservative own-divisibility test, illustrating that the terminal test is necessary even when the interior clock guard is used. Across all sampled Y the test does not establish asymptotic support control or short suffix probability. At Y1597,v203, only127/281 actual fresh suffixes finish, and257/512 initial LOW continuations finish; the BadTime condition for this finite cap is far from established. There was no original canonical source resimulation in this turn.

## 5. Next task

The previous all-offset argument can be replaced by two independent quantities: the actual LOW-only elapsed lifetime after a fresh jump and the number of distinct terminal offsets across possible fresh labels at the prehistory. The new time-clock estimate is unconditional and removes horizon gain from the interior reactivation problem. Terminal offset counting accounts for the dependence on the candidate high label. To proceed, a possible approach is to bound terminal support through the number of distinct LOW suffix itineraries under shifts of the starting horizon, using the deterministic clock schedule and CRT constraints on the selected LOW labels, or to bound the weighted set of bad q directly instead of its unweighted support. The probability of long LOW-only suffixes remains unresolved; the physical far-coalescence bound remains open as well. No new branch, no main edit, no Lean compilation.
