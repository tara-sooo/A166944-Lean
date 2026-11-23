# Twin-prime-first: growth-spectrum refiring classification and failed induction tests

2026-11-23 JST, child Issue #3, related #4 and parent #1. **Purpose:** seek an unconditional estimate for high-prime reactivation in the actual squarefree parity-GCD wheel. This note distinguishes fully finite checked exact classifications, falsified stronger ideas, established implications, and the outstanding all-prime analytic issue. The full twin-prime conjecture is NOT proved. The new classification is not yet Lean-kernel checked (the LOW7 22,050-state local budget in draft PR #5 is separately Lean verified).

## A. General elementary reactivation and finite donor growth spectrum

For any nonunit event with odd prime factor q, after the event the even state C satisfies C≡0 (mod q) if the event time is even, or C≡−2 (mod q) if odd. Let E denote all q-free growth before the *next* q-bearing event. The next q clock requires E≡−1,+1 or +3 (mod q), according to the two parity cases. Consequently, for any finite donor alphabet S omitting q, if all possible *prefix* growths E on the S-only wheel belong to a known set A_S, the following is a rigorous **necessary condition** for two q hits without another external donor:

    q divides some E−a, with E in A_S and a in {−1,+1,+3}.

The prefix qualifier matters: the donor trajectory may be interrupted by the next q hit before reaching its S-only sink. The first-hit tie with donors is included.

## B. COMPLETE q-refiring classification for LOW7 donors

For S={3,5,7}, exact event-jump and independently written literal, integer-by-integer parity-GCD oracles agree on EVERY one of 2*105^2=22,050 residues (time mod210, even C mod210). The union of cumulative growths over ALL path prefixes is exactly:

    A_357 = {0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,
             32,34,36,38,40,42,44,104,106}.

All LOW7 paths terminate (kernel-checked budget <=56 time, <=106 growth and finite graph); in particular this spectrum is exhaustive for arbitrary even starts. The congruence condition gives the finite list of candidate primes q>=11:

    E357 = {11,13,17,19,23,29,31,37,41,43,101,103,107}.

No q>107 can qualify because E<=106 and |E−a|<=107 (with the zero-difference case irrelevant for q>=11). For all candidate primes, **actual unrestricted S∪{q} paths with TWO q hits exist**. A separate literal oracle validates these witnesses without using the finite-state q shadow; format q:(start_t,start_C;first_q_time,second_q_time):

    11:(2309,1508;2310,2332)
    13:(2729,430;2730,2771)
    17:(3569,698;3570,3638)
    19:(3989,2338;3990,4049)
    23:(4829,4210;4830,4876)
    29:(1681,1306;1682,1771)
    31:(2946,2386;2947,3009)
    37:(4848,6326;4849,4884)
    41:(7789,862;7790,7833)
    43:(1117,904;1118,1204)
    101:(18686,7776;18687,18786)
    103:(11022,5252;11023,11124)
    107:(5563,5458;5564,5673).

This establishes the **paper/finite-integer-verified iff theorem** for arbitrary even-state alphabet {3,5,7,q}, all primes q>=11:

    there exists an arbitrary-state path with at least two q-bearing events
      ⇔ q∈E357.

The last three witnesses include a LOW7 composite donor event d=105=3*5*7. Without any d=105 intervening donor, all q>=47 cannot repeat through LOW7-only events: non-105 prefix growths E<=44, and q cannot divide E−a for q>=47. This refinement is also finite-spectrum-derived.

For the **full** canonical B wheel, this theorem supplies an important unconditional restriction: two consecutive actual q-bearing events with q∉E357 MUST have at least one intervening event containing a prime r>=11 distinct from q. It does NOT prohibit q returning through other high primes.

Full original-wheel exact C++ check of ZERO-high-donor returns (every odd M in [X,2X) for these test X) confirms both the previous total counts and the allowed q labels:

    X=4096: total 88, q count {11:56,13:27,17:2,19:3}
    X=16384: total 646, {11:279,13:117,17:121,19:118,23:11}
    X=65536: total 3838, {11:1912,13:850,17:473,19:420,23:63,29:120}
    X=262144: total 19492, {11:8556,13:6264,17:2095,19:2200,23:360,41:17}.

These finite numbers are original-GCD computation, not asymptotic estimates.

## C. Two foreign high donor primes: a six-element algebraic spectrum

For any two different odd primes 5<=p<r and no other donors, the p clock cannot fire again until r fires, and the r clock cannot fire again without a p recharge (p−1<r−1). Hence r fires at most once, p at most twice, and the whole S={p,r} wheel has at most THREE events. The only possible full/prefix gains are:

    A_{p,r} = {0,p−1,r−1,p+r−2,2p+r−3,pr−1}.

The simultaneous p*r event cannot be followed by another donor event. For any new q>r, a rehit requires q | (E−a) for some E in this six-element set and a∈{−1,+1,+3}. This is a purely algebraic divisor screen independent of arbitrary huge q.

For p=11,r=13, the spectrum is exactly {0,10,12,22,32,142}. Therefore possible rehit q>13 are exactly

    {19,23,29,31,47,139}.

ALL SIX have explicit true finite three-prime paths with two q events. In particular q=139 from (t,C)=(10704,34610) visits n10705 (d139), n10727 (d143), n10842 (d139). Independent C++ graph checks: S={11,13,17} has 11,819,522 states, no q17 rehit; S={11,13,19} has 14,764,178 states with q19 rehit.

For p,r=(5,7), (7,11), (13,17), (17,19), (19,23), the same exact 2*(p*r)^2 CRT-compressed post-q state search was run; candidate q and reachable actual witnesses were checked. The general sufficiency of all divisor-screen candidates for ALL arbitrary pairs p,r has NOT been proved.

## D. Other genuinely tested ideas: two precise failures and a useful canonical measurement

1. FALSE: adding one prime q can increase an arbitrary-state stopping time by at most 2q. Exact S={3,5,7}, q=11 all 2,668,050 full residue states: max new-minus-old time is 120 (>22), and 236,517 states exceed 22; witness (t,C)=(1008,892). One-prime greedy induction does not work.

2. FALSE: the naive potential V=τ_{3,5}+τ_{3,7}+τ_{5,7}, summing exact stopping-time functions of pairs, obeys the LOW7 Bellman decrease. Exhaustive LOW7 graph has 5,183 violating edges out of 18,900, max one-step deficit32. Witness local (t mod210,C/2 mod105)=(166,52). The previously published OPTIMIZED interacting pairwise potential DOES work on all LOW7 transitions, with bound268, so these are different assertions.

3. Canonical full-wheel all-high-owner repeated occurrences R7(M) are smaller than the count required for a no-twin source in finite scans; maxima over odd M in [X,2X): X4096=>12, X16384=>33, X65536=>36, X262144=>61, X524288=>77, X1048576=>96. These are FINITE observations. In contrast no-twin terminal certificate requires R7(M)>=(3/56−o(1))B pointwise. This contrast does not yield an asymptotic theorem. Note: the C++ audit originally had a 32-bit overflow in the displayed R7/(X*B) at X1048576, corrected to division by double(X)*B in the archived source.

4. Canonical terminal even horizon C_B(M) is not monotone as M increases (e.g. M281->283, Cterm600->570), refuting naive source-order residue dispersion.

5. Arbitrary CRT-state simulated-annealing stress search for increasing prime alphabets produced B31:81 events, B97:296, B251:673, B503:744. This is heuristic achieved finite LOWER bound on maximum event count, not an upper bound/cycle-freeness theorem.

## E. Specific research strategy and external precedents

The full-wheel return decomposition now separates:

- **LOW7-only recharge:** impossible except 13 FIXED small q labels. This is a rigorous finite-spectrum statement.
- **One/two high donors:** use small exact growth-spectra + congruence divisor screens; two-donor case already has only six E alternatives.
- **Three or more high donors:** analyze dependency words/paths (foreign-prime names, recharges, CRT phase) and charge their source-weighted multiplicities, with a norm/expansion bound or a high-donor decomposition.

The Helfgott–Radziwiłł paper *Expansion, divisibility and parity* (arXiv:2103.06853) estimates a spectral norm on a prime-divisibility graph, including analysis of paths with repeated primes and intervening 'lone primes'. Its graph is NOT the same as the adaptive GCD wheel, but suggests a very specific bridge: define an operator on **tagged actual post-event states**, with edges recording donor-q incidence, then seek contraction of the source-weighted walk once all low-only rehit loops are isolated into the finite q list. The paper's spectral theorem cannot be applied without proving a matching operator/kernel estimate for this new graph.

Other relevant tools: Friedlander–Iwaniec *Asymptotic sieve for primes* (arXiv:math/9811186), the Type-II bilinear obstruction to translating sieve upper bounds into prime detection; Jared Duker Lichtman, *A modification of the linear sieve, and the count of twin primes* (Algebra & Number Theory 19 (2025)), proving a sharper UPPER BOUND for twin-prime counts, not infinitude; the 2026 Jacobsthal quadratic bound treats fixed one-residue-per-prime covering rather than dynamic resets; Holt *Eratosthenes sieve supports the k-tuple conjecture* (arXiv:2502.20470) studies primorial gap-cycle persistence but not an actual twin-prime lower bound.

The precise missing theorem remains a source-selected *multi-donor* return bound: for the minimum high-owner count R7 over dyadic X, prove liminf R7/(XB)<9/224 (or one of the stronger o(XB) bounds). Neither finite donor spectrum nor existing spectral-expansion papers establishes this input. An alternative fully deterministic global clock Lyapunov O(sum_{p<=B}p) remains open; the naive insertion induction is now explicitly refuted.

## Replay and evidence classes

- research/low7_growth_spectrum_and_q_reset.py: all 22,050 LOW7 residue states, independent literal oracle, 24 prefix growth values and CRT post-q screens.
- research/low7_q_rehit_literal_oracle.py: independent literal parity-GCD witnesses for all 13 q.
- research/two_donor_spectrum_recurrence.py: six-element two-prime donor spectrum, CRT post-q state search and actual pre-q witness reconstruction.
- research/low7_zero_high_donor_audit.cpp: original full canonical wheel source-weighted zero-high-donor returns (strict C++17).
- research/prime_clock_insertion_probe.cpp: exact all-state false-insertion certificate (strict C++17).
- research/prime_clock_pairwise_naive_test.py: 5,183 explicit transition counterexamples to naive pair sum.
- research/prime_clock_canonical_return_probe.cpp: full original canonical owner return maxima (strict C++17).

Classification/necessary-condition proof uses exact arithmetic plus complete finite state check, **not new Lean kernel acceptance**. The LOW7 time/growth bound base is Lean-checked in draft PR #5. No modification of main.