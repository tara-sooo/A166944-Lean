# Twin-prime-first: MIN-wheel return budget via separated high clocks, height regeneration, and dyadic prime bands

Date: 2026-11-23 JST. Issue #3, cross-issue #4, parent #1. The target is an unconditional proof of infinitely many twin primes, using the canonical squarefree parity-GCD wheel with the **MIN-prime selected-increment policy**. This note records new elementary paper lemmas, exact reproducible finite tests, a genuine counterexample to a tempting pair-only sieve, and a sharper open quantitative target. **Neither the required asymptotic estimate nor twin-prime infinitude has been proved.** The symbolic additions have NOT been compiled in Lean. The MIN-LOW7 all-residue finite base is independently verified computationally; the separate PRODUCT-LOW7 finite certificate was previously checked in Lean (draft PR #5).

## 1. Setup and the actual mathematical target

For dyadic X, odd M in [X,2X), B=ceil(sqrt(7X)), s=M+2, C(s)=2M-2, K=floor((7M-1)/4). At the earliest nonunit parity-GCD event n, choose the **smallest odd prime p<=B** dividing the raw gcd, and set C<-C+p-1 (not the product increment). Clock candidates are n=0 (mod 2p) when p|(C-1), and n=p+2 (mod 2p) when p|(C+1). For p>=11 let N_p(M) be its number of SELECTED events, F=sum_(M,p>=11)1{N_p>0}, R=sum_(M,p>=11)(N_p-1)_+. Because MIN chooses a single prime, every high selected event has exactly one high owner.

The MIN-LOW7={3,5,7} functional graph on 22,050 residues has, by exhaustive integer computation, max total elapsed time 56, max clipped growth **34**, and max 9 events. The general squarefree-wheel terminal twin certificate works for MIN (every selected increment divides the raw gcd and preserves 2M-2<=C<=2n). The pre-existing LOW7 no-terminal-twin argument implies:

    liminf_(dyadic X->infinity) R(X)/(X*B) < 9/224

is enough to prove infinitely many twin primes; in particular R=o(XB) is enough. Finite data alone never establish this premise.

## 2. Exact 2p height divisibility (new strengthening of the dual-height formula)

Define the nonnegative HEIGHT at an event's **post-state** by h=2n-C. For ANY selected odd clipped divisor e>1, not only the MIN p, the raw gcd yields:

    EVEN n: e|(C_pre-1) and e|n
            => e|2n-(C_pre-1)-e = h.
    ODD n:  e|(C_pre+1) and e|(n-2)
            => e|2(n-2)-(C_pre+1)-e = h-6.

Since h is EVEN and e is ODD, the true sharpened constraints are

    EVEN: 2e | h;                     ODD: 2e | h-6.       (HEIGHT-2E)

For MIN e=p>=5, the post-height lies in {0,2p,4p,...} at even events, or in {6,6+2p,6+4p,...} at odd events. The parity and h>=0 exclude negative odd-branch multiples for p>=5.

For a top-band selection p>=B/2, if the *pre-event plateau* has height h_pre<B, and its next-event gap g<=2p, then

    h_post=h_pre+2g-(p-1) < 5p+1.

Consequently, for p>=11 the ONLY post heights are

    even: 0, 2p, 4p;                 odd: 6, 6+2p, 6+4p.  (SIX-ATOMS)

The reset cases are (n,C_post)=(n,2n) at even n, or (n,2n-6) at odd n. These states depend on n alone: all sources reaching the same reset n coalesce in their future event clocks, up to their respective K cutoffs. An ODD reset at n is precisely another canonical start with M'=n-2, since s'=M'+2=n and C'=2M'-2=2n-6. This is an exact deterministic REGENERATION identity, not a distribution claim.

**Independent computational evidence.** MIN original event-jump audited every M at X=4096,16384,65536,262144,1048576, checking HEIGHT-2E at EVERY selected event. For top p>=B/2:

    X        total top events  top resets  distinct (n,C) resets  max source weight  selected top repeats
    4096             572          380            35                     33                11
    16384           2242         1457            85                    115                 0
    65536           8577         4753           238                    176                 0
    262144         27463        19272           630                    629                40
    1048576       102032        72737          2005                   1022                 5

For X1048576, 92976/102032 top events had h_pre<B. The remaining 9056 had h_pre>=B. Of the top events, 72737 reset onto only 2005 time-height atoms (and 4 of the 5 top repeats occurred at resets). Source multiplicity is essential; e.g. one reset state carried 1022 starts. A source-independent unweighted Markov assumption is invalid.

The entirely independent literal per-integer Python oracle matches the event-jump reset (total, reset, unique, max fibre) at X256: (87,15,6,4); X512: (137,124,15,29); X1024: (153,143,18,46). These are FINITE checks.

## 3. Separated two-high alphabet theorem (new symbolic result)

**Proposition (paper arithmetic + exact finite LOW7 base).** In the MIN wheel with S={3,5,7,q,r}, primes 37<=q<r and r-q>68, from ANY even starting state:

* the larger prime r is SELECTED at most ONCE;
* the smaller q is SELECTED at most TWICE;
* there are at most THREE selected high events in total;
* total travel to the last event obeys

    tau_S <= 4*56+2*(2q+r) = 224+4q+2r <=224+6r.     (GAP-68)

Proof: a selected high p is deactivated by its own increment p-1. Until p is selected again, the selected LOW7 events form prefixes of LOW7-MIN paths, each of growth <=34. Since p>=37 requires at least p-1>=36 recharge, two consecutive *high selections* can never have the same high prime: there must be the other high prime in between. In particular, before two consecutive r selections, q occurs exactly ONCE, with at most two LOW7 segments bracketing it (growth<=68 total). The total recharge is at most q-1+68, strictly less than r-1 for r-q>68. Therefore r cannot repeat. Because q repeat needs r in between, q occurs at most twice. At most four LOW7 segments contribute <=56 time each. A high prime p, if selected, is taken at its own clock in <=2p steps after the last preceding low selection. Sum those gaps to get GAP-68. A high clock tied with a smaller LOW7 prime does not disrupt the argument because MIN selects the low prime, as the isolated LOW7-MIN clock would. No assumption on q,r sizes besides the displayed inequalities is needed.

Heuristic CRT state stress tests at pairs (37,109),(41,127),(59,149),(101,211),(137,239) found at most 3 high events and no violation. The small-alphabet cycle scanner exhaustively verifies MIN S=(3,5,7), (3,5,7,11), (3,5,7,13), (3,5,11,13), (3,7,11,13) with respectively 22050, 2668050, 3726450, 9202050, 18036018 states; none had a directed cycle. These finite cases are not a universal acyclicity proof.

**Near pairs behave differently.** Exhaustive 3-prime post-r reset-compatible states for S={3,q,r} (described in §5) admit 2 ADDITIONAL r events after an initial r when (q,r)=(41,43),(59,61),(101,103),(137,139). Thus an attempt to bound each high prime to two selections for near pairs is already false in these allowed post-event residue states.

## 4. Why a near-prime-pair sieve alone cannot solve the full wheel

For the MIN wheel the recharge condition for two consecutive selected q events, with m intervening selected high primes r_j and LOW7-only gain L, is

    q | sum_(j=1)^m r_j + L - m - c,
    L <=34*(m+1), c in {-1,1,3}.                    (MIN-LINEAR)

If there are only q,r high labels, the preceding proposition and near-pair sieves give a finite/sparse-label route. But multiple HIGH donors can reactivate q even if every donor is far from q.

**Direct canonical counterexample, independently checked literally:** X65536, B678, M97289, MIN selected q=197 at n97517 and again at n97712. Intervening selected events, in order, are

    (97518,3), (97669,101), (97674,3), (97693,83),
    (97697,5), (97702,11).

The three high donors are [101,83,11], each more than 68 away from197. LOW7 growth L=2+2+4=8, high growth=100+82+10=192, total E=200=197+3; the necessary congruence is satisfied. HEIGHT at successive q events is (6,0). Thus pairwise-separated **individual** high primes do NOT eliminate combined multi-donor returns. The all-high proof must charge donor hyperedges / sums, not just nearby prime pairs. Strict C++ scans also found other far-donor canonical cases; this explicit one is reproducibly literal.

## 5. Post-event CRT dimension reduction (a separate exact counting idea)

For the restricted alphabet {3,q,r}, 3<q<r odd primes, consider the complete space of clock-residue states immediately after a hypothetical SELECTED r event. The r event time t belongs to exactly two calendar classes modulo 2r (even t=0, odd t=r+2), and post-state C mod r equals 0 or -2 accordingly. Once this r-coordinate is FIXED, the other clock-state residues are t mod 6q and C/2 mod 3q. Thus there are precisely

    2*(3q)*(3q) = 18q^2

post-r reset-compatible CRT states, **independent of the size of r**, versus 2*(3qr)^2 unrestricted states. Not all reset-compatible states need be reachable via a real preceding r selection, so this is an over-complete superset for bounding all continuations.

The complete 18q^2-state test (500-event stop guard never hit) gives:

    (q,r)       post-r states     states with >=2 further r selections   max further high selections
    (37,109)          24642                          0                         1
    (41,43)           30258                        249                         4
    (59,61)           62658                        357                         4
    (101,103)        183618                        609                         4
    (137,139)        337842                        825                         4
    (211,223)        801378                          0                         1

At near twin pairs the r-triple states (including the presumed initial r) are a genuine warning against naive per-label 2-hit bounds. No inference that all alphabets universally terminate is made from this table.

## 6. A quantitatively sharper NEW analytic target: dyadic q-band renewal

Define for Q=11*2^j with Q<=B,

    R_[Q,2Q)(X) = sum_(odd M in [X,2X)) sum_(prime q in [Q,2Q),q<=B)
                    (N_q(M)-1)_+.

A single universal bound, for some absolute A,C>0, for every such Q and all sufficiently large X,

    R_[Q,2Q)(X) <= C * X * (log(2X))^A / Q           (DYADIC-RENEWAL)

would imply

    R(X) <= C*X*(log(2X))^A*sum_(j>=0)1/(11*2^j)
          < (2C/11)*X*(log(2X))^A
          = o(XB),

and therefore infinitely many twin primes via the already established LOW7 MIN clock reduction. This estimate is OPEN, requires source-weighted adaptive correlations, and is MUCH stronger than the threshold 9XB/224. It is a concrete scale-sensitive alternative to proving pointwise R<=C F. A fixed per-prime O(X logX/q^2) bound would imply it up to harmless log factors, but can suffer strongly from coalesced q-specific spikes; **averaging over q in dyadic bands is more natural**.

Exact original-GCD MIN finite measured R_[Q,2Q)*Q/(X*log(2X)):

    X          Q=11    Q=22    Q=44    Q=88    Q=176   Q=352   Q=704  Q=1408
    4096       .5165   .2402   .0322   .0262      --      --      --      --
    16384      .6682   .2662   .0938   .0351   0          --      --      --
    65536      .8337   .3543   .1105   .1005   .0540   0           --      --
    262144    1.0654   .4243   .2276   .1111   .0776   .0394   .0082      --
    1048576   1.2650   .5843   .2815   .1499   .0678   .0416   .0171   .00046

All normalized values on these windows were <=1.265; that does NOT establish an asymptotic constant-2 bound. At X1048576, total MIN F=4,273,096 and R=2,292,324, with 1,755,226 returns in [11,22) alone, and only 5 in q>=B/2. A source-weighted high-label dispersion estimate at the Q scale is the main analytic missing input.

## 7. Literature connection and attempted strategies

* Helfgott--Radziwill, [Expansion, divisibility and parity](https://arxiv.org/abs/2103.06853) and [Helfgott's primary detailed explanation](https://webusers.imj-prg.fr/~harald.helfgott/Expansion_1.html), counts walks by repeated/lone prime labels and rank of their CRT constraints, with a graph/spectral comparison and exceptional vertices. The MIN-LINEAR donor words and the reduced q-band target make the analogy precise. Their adjacency operator is not the one-way, source-weighted, adaptive MIN wheel, so no ready-made bound on DYADIC-RENEWAL follows.
* Matomaki and collaborators, [Weighted sieves with switching (2025)](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C), introduces weights and switched-variable sums, and explicitly separates Chen-type prime/P_2 detection from the unsolved twin-prime statement. The paper's sieve setup does not directly control adaptive q returns. A transfer would have to supply distribution of the post-reset source measures modulo q.
* The earlier full signed-prefix CRT word theorem in this repository fixes source residues but reaches P(word)>X/2 before ~97% of actual repeats. The new height reset states allow quotienting the long suffix into a small collection of (time,height) atoms, provided **their source-fibre masses are retained**. Simply counting distinct atoms is insufficient.

Suggested next mathematical experiment: build the exact source-pushforward transfer operator on the height-0/6 reset atoms, conditional on the low7 residue and dyadic q band, and estimate its **weighted** q-renewal Green kernel. For nonreset top-q events, use the three possible height multiples from SIX-ATOMS and charge the h>=B excursions. Search for an operator norm or large-sieve estimate at scale Q leading to DYADIC-RENEWAL. A counterexample to this particular bound, or growing family of r-q near-prime oscillations, would redirect the attempt.

## 7a. NEW owner-history-free first-reset transfer identity (quantitative fresh test)

The reset quotient can completely discard the seen-prime history if one counts TOTAL selected high events H=F+R rather than repeated-owner R. Since F<=(X/2)*pi(B)=o(XB), the requirements H=o(XB) and R=o(XB) are EQUIVALENT asymptotically along any dyadic sequence, and both suffice for the twin-prime conclusion.

For every canonical M, let rho(M) be its FIRST selected p>=11 event whose post-height h is 0 (even) or 6 (odd). If no such event by K(M), assign no reset and count all its high events in H_pre(M). Otherwise put v(M)=(rho,C_rho) and count high events up to AND INCLUDING rho in H_pre(M). Let U_B(v;T) count subsequent MIN selected high events from the frozen state v, using the SAME cutoff B, until time T. Because the process after v depends only on v,B, and K(M), one has the exact identity

    H_X = sum_M H_pre(M)
          + sum_(first-reset atoms v) sum_(M:v(M)=v) U_B(v;K(M)).

Define the fibre weight w_v=#{M:v(M)=v} and common Kmax=max_{M in I_X} K(M). Since K(M)<=Kmax and the event process is independent of the truncation until that truncation,

    H_X <= H_pre,X + sum_v w_v U_B(v;Kmax).           (RESET-ENVELOPE)

This is a deterministic source-weighted transport bound, not an unweighted Markov or random-phase argument. It is genuinely free of previously selected prime labels, unlike a compressed R count. A sufficient **still-open** analytic two-part goal is

    H_pre,X = o(XB),
    sum_v w_v U_B(v;Kmax) = o(XB)

along unbounded X. A stronger but more explicit candidate is each = O(X*(log X)^A) for a fixed A>0.

The strict C++17 min_prime_first_reset_transfer.cpp reconstructs the forward MIN ghost FROM EVERY DISTINCT first-reset atom v, extends to Kmax, and asserts the envelope always bounds the source-specific post-reset count. Finite exact data:

    X        covered sources  distinct atoms  max source fibre   H_pre    H_post     sum w_v U(v;Kmax)
    256               55              28               5         240        151                151
    1024             265             126              17         608        540                540
    4096            1294             544              16        4222       5177               5177
    65536          23052            9064              35       83720     178835             178835
    262144         96450           36726              74      365564     971997             971997
    1048576       401179          148388              94     1593931    4971489            4971489

The observed equality of H_post and the Kmax envelope in these windows means every reset orbit terminates its high events before the SMALLEST relevant source cutoff there. Equality for all X is NOT proved and not assumed in RESET-ENVELOPE. In the X1048576 sample, max high event count before the first reset on a source was 109, max high count after it was 122, and max U_B(v;Kmax) was 122 (separate local strict-compiled diagnostic). These pointwise polylogarithmic-looking maxima are finite evidence only. Every reachable reset atom still carries a potentially large source fibre, so the weighted term cannot be replaced by the number of distinct atoms.

Replay:

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_first_reset_transfer.cpp -o /tmp/minfirst
    /tmp/minfirst 256 1024 4096 65536 262144 1048576

## 7b. Another strategy explicitly tested and kept OPEN

A more localized alternative is the dyadic label sieve DYADIC-RENEWAL from §6. The actual MIN source-counted returns R_q scaled as R_q*q^2/(X*log(2X)) have occasional large q-specific spikes from coalescence (e.g. X262144, q601: 14.54; q967: 10.83), even while the dyadic Q-band aggregates stayed <=1.265 after scaling by Q/(Xlog(2X)). This favors a **bandwise averaged transfer** over any overly optimistic per-prime uniform estimate. No source-conditioned large-sieve upper bound has yet been proved.

## 8. Reproducible verification and status

Sources committed alongside this note:

    research/min_prime_gap_height_literal_oracle.py          (independent per-integer)
    research/min_prime_post_r_3qr_exhaustive.cpp              (18q^2 full check)
    research/min_prime_dyadic_return_audit.cpp                (actual MIN q-band counts)
    research/min_prime_height_reset_coalescence.cpp           (actual MIN height reset/fibre)
    research/min_prime_small_graph_exhaustive.cpp             (small MIN full CRT graphs)
    research/min_prime_first_reset_transfer.cpp              (first-reset weighted future envelope)

Replays (strict compiler flags -Wall -Wextra -Werror):

    python3 research/prime_clock_controlled_low7.py
    python3 research/min_prime_gap_height_literal_oracle.py
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_small_graph_exhaustive.cpp -o /tmp/min_graph
    /tmp/min_graph 3 5 7 11
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_post_r_3qr_exhaustive.cpp -o /tmp/postr
    /tmp/postr 101 103
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_dyadic_return_audit.cpp -o /tmp/minbands
    /tmp/minbands 4096 16384 65536 262144 1048576
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_prime_height_reset_coalescence.cpp -o /tmp/minreset
    /tmp/minreset 256 512 1024 65536 262144 1048576

The C++ finite computations and independent literal source were separately implemented and their relevant small-X/high-donor outputs matched. The universal height congruence and separated-pair bound are **paper deductions** with finite MIN LOW7 base; not newly Lean checked. DYADIC-RENEWAL remains OPEN. No twin-prime theorem, no A166944 target proof, and no changes to main.
