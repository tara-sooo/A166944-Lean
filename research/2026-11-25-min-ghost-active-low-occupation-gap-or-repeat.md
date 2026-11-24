# Active LOW occupation and gap-or-repeat tests without terminal guards

2026-11-25 JST. Continues 0ce9809860118e695f4091cca7866c9cfca2ec0e on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary probability deductions and exact pathwise finite checks. No Lean compilation. No proof of the clipped-height tail criterion or twin-prime infinitude.

## 1. Test every attained LOW terminal, not only fresh guarded suffixes

Keep the infinite CRT ghost with uniform independent prime coordinates and common parity, relative integer time and nondecreasing even horizon. Write T=floor(Y sqrt(log Y)), w=2Y, U=T+w. Use an integer cutoff z>=11 with z^2>=2U, z<=Y eventually, and assume log z/log(2w) is bounded below by a fixed positive constant. A high event is a selection p>=z; fresh means the first selection of that p. The following statements use the filtration revealing all p<z coordinates initially, and the full selected tick sequence including quiet ticks thereafter. Previously selected high coordinates are known; unselected high coordinates are not revealed.

At an attained state (including the initial state) call the state LOW inactive if NO label p<z is eligible at its current horizon, irrespective of clock. Such a state is a LOW-only terminal. Unlike the preceding test criteria, we place NO restriction on previously selected high labels at this state. No short-suffix guard or terminal offset bound is needed.

Start a test at each LOW-inactive attained state with time s<=T, ending the test at the first next event if it is within w ticks, or after w quiet ticks otherwise. If the quiet test succeeds, subsequent tests may resume at the next attained state, not before the previous test ends. All tests are stopping-time tests. Define an outcome of type 1 if either (a) the next wait is >w, including infinite wait for a finite alphabet, or (b) the next event occurs within w and its label was already selected before the test began (including the event that attained the test state). Otherwise the outcome is type 0: the next event is a fresh high selection within w. There are no LOW candidates while the horizon is frozen, by definition.

At each test, conditional on the history at its start, the probability of type 1 is bounded below by an absolute positive constant c depending only on the lower bound for log z/log(2w). To prove this, consider absence of matches from ALL unused high primes on the frozen horizon for the next w ticks. Their independent allowed-coordinate sets have cardinalities >=p^2-s. The exact frozen-interval forbidden pair count is min(w,2p). Thus the conditional probability of their absence is at least
    product_(p>=z prime) (1-min(w,2p)/(p^2-s)).
Here including already selected primes in this lower product only decreases it; the product is bounding absence of unused matches, not absence of known matches. The preceding Mertens comparison gives a positive uniform lower bound because s<=T, z^2>=2U and log z/log(max(z,2w)) is bounded below. If unused matches are absent, either no known high clock matches through w (quiet gap), or the first known matching clock produces a repeat high event within w. The horizon remains frozen until the first event. This proves the assertion without requiring known high labels to be ineligible. It works for every attained LOW terminal, even one reached after repeated high selections or a very long LOW suffix. A finite upper alphabet gives at least as large an unused-absence product, with the same argument.

The type-1 lower bound does not assert that the conditional probability of a gap alone is positive when a known high match is imminent. It explicitly allows a repeat to be the outcome. The test does not reveal unused coordinates that might match after the test ends.

## 2. Count LOW-inactive time instead of short suffixes

On [0,T], split elapsed time into event-delimited plateaux (including the initial plateau and the truncated final one). On a plateau the horizon is fixed, so the property that some LOW label is eligible is constant throughout. Let A_T be total elapsed time of LOW-active plateaux (at least one p<z eligible); let Q_T=T-A_T be the complementary LOW-inactive time. This is actual elapsed occupation, not event count and not counterfactual lifetime. Zero-length boundary points do not matter.

Let sigma_Y be the first attained start of a wait >w in the full ghost as before. On sigma_Y>T each plateau beginning by T has length at most w, and each LOW-inactive plateau beginning by T supplies one test. Hence if Q_T>=delta T for fixed 0<delta<1, at least m=floor(delta T/w) tests start by T. This m tends to infinity. On sigma_Y>T none of these tests can end with a gap, so each type-1 outcome is a repeated high selection by U. Distinct tests cannot charge the same repeated selection. Define R_U^term as the number of tests starting by T whose next event within w is a repeated high selection; define R_U as the number of ALL repeated high selections by U, so R_U^term<=R_U. The former is a smaller statistic and the bound below applies to either one.

For any lambda>0 and integer k>=0,
    Pr(first m tests all exist by T, at most k of them have type 1)
        <= exp(lambda k) (1-c(1-exp(-lambda)))^m.
Proof: at each test start the conditional expectation of exp(-lambda times its type-1 indicator) is at most 1-c(1-exp(-lambda)). Multiply successively, including the indicators that the required tests exist by T. Earlier outcomes are measurable at each next test start; the event that the next test exists can be dropped in the upper expectation bound. This induction needs no independence between tests. Then apply exponential Markov to the sum of the first m outcome indicators. In particular with lambda=log 2,
    Pr(sigma_Y>T, A_T<=(1-delta)T, R_U^term<=k)
        <= 2^k (1-c/2)^m.
The same inequality holds with R_U in place of R_U^term. Thus the new unconditional reduction is
    Pr(sigma_Y>T)
        <= Pr(A_T>(1-delta)T)
           + Pr(R_U^term>k)
           + 2^k (1-c/2)^floor(delta T/w).
If k=o(T/w), the exponential term tends to zero. More generally k=floor(cm/4) works, since k log 2 - cm/2 tends to minus infinity. This criterion permits arbitrarily many long LOW suffixes, and does not require the medium-count restriction, terminal support concentration, short-suffix guard or absence of repeats. It replaces them by two actual-path statistics: LOW-active occupation and terminal repeat count. These two new residuals are NOT yet bounded sufficiently. A bound on A_T alone does not suffice; known high blockers may produce many repeat outcomes.

## 3. Exact decomposition and predictable weighted bound for active occupation

Partition [0,T] by actual high selections. There is an initial interval up to the first high, followed by intervals from each high event to the next (truncated at T). For an interval beginning at s and actual post-horizon g', let tau(s,g') be the lifetime of the deterministic <z ghost from that state, which terminates by the LOW barrier. For the initial interval use tau_z from the initial state. Let ell be the interval's actual length.

Until the next high event the full process agrees exactly with that <z ghost, including its frozen tail: a high match losing a tie to a LOW event changes nothing. The <z ghost is LOW active until its final event time and LOW inactive thereafter; a state with no eligible LOW prime is terminal, so cannot later become active without a high jump. Therefore the EXACT active time in the interval is
    min(ell,tau(s,g')).
This includes repeats and fresh high starts, and holds even when there is a high interruption before the hypothetical LOW terminal. No assumption about absence of a long gap is needed.

Consequently, writing tau_q for the counterfactual lifetime from (s,g+q-1) at tick s with pre-horizon g,
    A_T = min(ell_initial,tau_z)
          + sum_(actual high events s<=T) min(ell_s,tau_q).
This is stronger for active occupation than the earlier bound on bad high-start interval lengths by tau_q+w: the entire potentially very long terminal plateau is excluded from A_T. Decompose A_T=A_initial+A_fresh+A_repeat according to interval type. For every v>=0 the positive excess over v of the contribution of each interval is at most (min(T-s,tau_q)-v)_+. In the filtration revealing all p<z, these counterfactual quantities are measurable before tick s for each candidate q, even though its coordinates are not known. Use the exact conditional candidate law or its upper bound 2/q^2 to obtain
    E A_fresh <= 2 sum_(s<=T) E sum_(unused q>=z) q^-2 min(T-s,tau_q),
    E sum_(fresh intervals) (active_time-v)_+
       <= 2 sum_(s<=T) E sum_(unused q>=z) q^-2 (min(T-s,tau_q)-v)_+.
These inequalities are unconditional; unlike the earlier weighted bad-interval bound they need no no-gap indicator and no additive w. The expectation is taken over actual histories, not fresh independent low-phase resampling. The upper bounds may be sharpened by exact selection probabilities from the prior weighted-candidate law. No estimate of the resulting expectation at the required asymptotic scale is claimed.

For repeats, conditional on the history the least matching known high p is a deterministic candidate. It can be selected only if there is no matching revealed smaller label and no matching unused smaller high. Hence the repeat part has an exact analogous predictable bound: sum over ticks of min(T-s,tau_p) times the conditional probability of selecting that known candidate p (zero if a smaller known label matches or no known high matches). Its conditional probability is the product of absence factors for unused smaller high labels, at most one. This bound does NOT replace the repeat selection probability by p^-2, since p's coordinates are already known. A separate repeat-tail estimate is needed to control the long repeat intervals.

## 4. Unconditional short active-occupation deletion and explicit repeat budget

Let F_T and R_T count distinct first and repeated high selections through T. The previous deletion law gives Pr(p seen by T)<=T/p^2 for p>=z, and each pair of successive selected p times is separated by at least p-2. Thus
    E F_T <= T sum_(p>=z) p^-2 = O(T/(z log z)),
    E R_T <= sum_(p>=z) (T/p^2) floor(T/(p-2))
             = O(T^2/(z^2 log z)).
The second estimate isolates repeats without a first-selection term. In particular for z=ceil(U^theta), 1/2<theta<1 fixed, and v=floor(U^(2theta-1)), 
    E [min(v,A_initial)+sum_(high intervals) min(v,active_time)]
      <= v(1+E F_T+E R_T)
      = O(v + vT/(z log z)+ vT^2/(z^2 log z))
      = o(T).
This includes all short active suffixes and the first v units of every longer active suffix, regardless of label history. Markov gives that this capped occupation is o(T) in probability. The same conclusion holds with v multiplied by any fixed log-power <1. Thus an occupation proof at z=U^(.9) can discard the short active portion up to U^(.8), much larger than the U^(<1/3) duration cap imposed by the prior simultaneous short-suffix guards. This does not assert that whole suffixes terminate within the larger cap, or that the large remainder is rare. It is a bound on total capped ACTIVE time rather than a full interval guard.

The remaining active time is the sum of the excesses over v; it consists of a single initial excess bounded by (min(T,tau_z)-v)_+, a fresh excess bounded in expectation by the predictable weighted sum of section3, and a repeat excess. In the gap-or-repeat criterion of section2, even A_T>(1-delta)T can only arise from these excesses up to an o(T) probability loss for any fixed positive margin. The earlier all-short condition is no longer needed for this reduction.

The crude repeat estimate also gives an explicit near-top result: choose z=ceil(U/(log U)^b) for fixed 1/2<b<3/4 (so z<Y eventually and z^2>=2U). Then E R_U=O((log U)^(2b-1))=o(T/w), so R_U^term=o(T/w) in probability. Consequently
    Pr(sigma_Y>T) <= Pr(A_T>(1-delta)T)+o(1)
for these near-top z. This is NOT a solution of the tail problem: E F_U=O((log U)^(b-1))=o(1) as well, so almost surely no high event occurs in this time window, and the active occupation becomes essentially min(T,tau_z). This regime is just a reduction back to an initial LOW lifetime estimate at a slightly lower cutoff. For a fixed power cutoff z=U^theta with theta<1, the crude repeat bound is generally much larger than T/w; a new estimate on actual terminal repeats is necessary. Do not describe the near-top estimate as simultaneously eliminating repeats and the initial active-occupation problem.

If a growing sequence Y has a cutoff z satisfying the test hypotheses and the two residuals of section2 tend to zero (or an appropriate joint bound holds), then the earlier finite-time coupling gives the clipped-height probability-tail criterion. The independent physical far-coalescence upper bound remains necessary for the twin-prime research goal.

## 5. Finite audit

Saved research/min_ghost_gap_or_repeat_occupation_audit.mjs and research/min_ghost_gap_or_repeat_occupation_results.json, exact remote readback at fd21f7ec8b6c3866b95156080efba340729051c4. Use 512 fixed-seed shared CRT phase samples per Y=53,199,797,1597,3203, finite upper alphabet V=8Y, T=floor(Y sqrt(log Y)), w=2Y, U=T+w. Three diagnostic cutoffs z=ceil(sqrt U), ceil(T^.8), floor(Y/sqrt(log Y)), with min11 and duplicates removed. They are finite diagnostics and need not satisfy z^2>=2U; the algebraic checks do not rely on that condition. Simulate actual event records through U; determine LOW eligibility at each attained state, exact active/inactive elapsed time and initial/fresh/repeat active components. Independently replay every <z continuation capped by remaining T and check that each high-start interval's actual active time is exactly min(interval length, capped LOW lifetime), including initial and interrupted suffixes. Verify test outcome partition, known clock versus unused matches through the earlier of w and the known deadline, no-gap occupation bound Q_T<=w times test count, and per-label repeat bound floor(U/(p-2)). In the first32 sampled paths also enumerate weighted capped-lifetime candidate sums at actual fresh events as descriptive diagnostics. Those sums are conditioned on sampled fresh-event histories, not the all-tick predictable expectation in section3, so they cannot estimate that expectation by direct substitution. No original canonical source resimulation, no exact full conditional probability audit in this turn (the conditional product was audited earlier).

At Y3203,T9100,w6406,U15506,V25624, total elapsed time over512 paths is4659200. At z125, total LOW-active time196426 (initial50398, fresh144508, repeat1520), LOW-inactive4462774, 1709 tests starting by T:492 gap outcomes (possibly multiple per path),9 repeat outcomes,1208 fresh outcomes. 34/512 paths have no gap >w starting by T. In those34 paths active25898, inactive283502, 207 tests and one repeat outcome. All34 have at least half their elapsed time inactive. There are32 repeated high selections through U across all512 paths, compared with9 terminal-repeat outcomes (a different smaller statistic). At z1470, total active597015 (initial382612,fresh214403,repeat0), 753 tests,492 gap,0 repeat,261 fresh. In the same34 no-gap paths active81558,inactive227842,76 tests and no repeat outcome. 30/34 have at least half time inactive. At z1127 total active520001, 813 tests,492 gap,0 repeat,321 fresh; no-gap active78800 and inactive230600,80 tests,31/34 half-inactive. These are finite empirical counts; m=floor(delta T/w) with delta=1/2 is zero at this Y, so the asymptotic exponential bound gives no useful finite probability estimate. We do not extrapolate the observed low repeat occupation to a proof.

## 6. Next target

The preceding simultaneous guard-and-terminal-offset conditions are unnecessary if actual LOW-active occupation and terminal repeat count can be controlled. The new test works at all LOW terminals, and the exact active occupation excludes long high waiting plateaux rather than charging their entire duration to bad suffixes. The short capped component is unconditionally negligible for a much larger time cap at a power cutoff. Remaining quantitative tasks are the weighted long-suffix active excess, especially the initial component, and the terminal-repeat count on paths with many LOW-inactive plateaux. The clipped-height tail and physical far-coalescence remain open. No new branch, no main edit, no Lean compilation.
