# Source-counted stopped MIN budgets and low-only ghost risk envelopes

Date: 2026-11-24 JST. Based on 1bd657bed01382e59d6addfd450a278fe8ed079a (sieved multi-donor prefix). New paper-level finite inequalities and source-counted experiments; no new Lean compilation. The twin-prime conjecture and the asymptotic risk estimate below remain OPEN.

## 1. Setup and two sufficient stopped-process criteria

Use the same canonical odd sources M in [X,2X), X dyadic divisible by 4, original cutoff K(M), prime bound B=ceil(sqrt(7X)), low modulus L and high label count P=pi(B)-pi(y) as the parent research note. Let N=X/2 and m=2P. Each source has its own actual MIN trajectory, with no artificial continuation after termination. Freeze the source's cost after termination or at an imposed budget b. All masses below count ORIGINAL sources, even after trajectory coalescence.

The clock inequality from canonical_min_prefix.lean implies that a non-twin terminal has at least m high hits whenever m*(2B+3L)<3X/4-2. This condition holds eventually because P~B/log B and L=o(B).

Let D_j(M) be the repeated-label count in the first min(j,actual high length) high selections. A non-twin source then has D_m>=P by pigeonhole. The first criterion (ALL) counts EVERY repeat as one unit of cost, with b=P. Stop at the b-th unit; any source not reaching b must be twin under the clock prerequisite. This criterion does not need the previous sieve estimates.

The second criterion (RESIDUAL) counts only the increments contributing to Z=A+R_res in the parent note. Specifically a small-label occurrence p<Q increments cost if its new multiplicity exceeds a+1; a large p>=Q increments cost if this is a consecutive repeat classified as residual there. All other repeats are cheap. Their total E(X) over the original sources is o(XP) by the parent paper bounds, including the small-label baseline. Set b=ceil(P/2). A non-twin source with Z_m<b has at least P-b+1 cheap repeats. If K_b is the number of sources reaching budget b, then for large X satisfying the clock prerequisite,

    #twin sources >= N - K_b - E(X)/(P-b+1).

Consequently it suffices to prove liminf K_b/N<1 along dyadic X. In particular it is NOT necessary to forbid even one residual repeat, to bound the full uncapped multiplicity of exceptional sources, or to get a vanishing hard-kill hazard at every rank.

For comparison, the earlier hard rule discards on first residual large return or small excess >P/2. The soft rule only discards after b total bad increments. They are distinct criteria; one is not equivalent to the other.

## 2. Exact layer transport and comparison with a binomial tail

Let C_j(M)=min(b, the cost after j high selections); a terminated source is frozen. Define

    w[j,r] = #{M : C_j(M)=r}, 0<=r<=b,
    f[j,r] = #{M : C_j(M)=r and C_(j+1)(M)=r+1}, 0<=r<b,
    U_j(r)=sum_(s>=r) w[j,s].

Every increment is 0 or 1, so these are exact deterministic identities:

    w[j+1,r] = w[j,r]-f[j,r]+f[j,r-1] (missing fluxes zero),
    U_(j+1)(r) = U_j(r)+f[j,r-1]  (1<=r<=b),
    w[0,0]=N, U_j(0)=N, U_m(b)=K_b.

Choose a fixed eta in (0,b/m) bounded away from b/m, and define

    e_j=max(0, max_(0<=r<b) (f[j,r]-eta*w[j,r])).

Then for all 1<=r<=b,

    U_(j+1)(r) <= (1-eta)U_j(r)+eta U_j(r-1)+e_j.

Compare this to the exact binomial tail recurrence for an auxiliary Bin(j,eta) variable. Induction gives

    U_j(r) <= N Pr(Bin(j,eta)>=r)+sum_(i<j)e_i.

The initial and r=0 boundaries satisfy the inequality, and the coefficients of the two previous tails sum to one. No independence of original MIN paths or congruences is asserted: the binomial distribution is solely a comparison function for the deterministic inequality.

Consequently

    K_b/N <= Pr(Bin(m,eta)>=b)+(1/N)sum_(j<m)e_j.      (1)

The binomial term tends to zero, by the mean m*eta and variance m*eta*(1-eta) and Chebyshev. For ALL take eta=2/5, giving tail <=12/P at m=2P,b=P. For RESIDUAL take eta=1/5,b=ceil(P/2), giving tail <=32/P. The error is the maximum positive excess across layers at each rank, NOT the sum over all layers. Tiny exceptional layers can have 100% increment rate without violating a useful cumulative bound.

Thus the single new sufficient condition is

    liminf_(dyadic X) (1/N) sum_(j<m) max_(r<b)(f[j,r]-eta*w[j,r])_+ < 1.    (2)

A bound by ANY constant strictly below one suffices. The terminal sources remain frozen in w (they are not incorrectly counted as currently moving sources). An active-only uniform contraction can fail even at finite X, and is not used.

Variant: one may choose a rank-dependent eta_j and the comparison is a sum of independent auxiliary Bernoulli variables with means eta_j. The same induction uses coefficients (1-eta_j,eta_j), and the tail is o(1) if sum eta_j is separated from b by Omega(P) with m=O(P). This may allow an early/late rank decomposition.

## 3. Arithmetic upper envelope for f: delete ALL high primes in the next block

At each current post-high state (or original initial state for j=0), keep its original cutoff, full relevant high history and cost. Compute the LOW-only MIN shadow, deleting every high p>y. This shadow's horizon gain is <L by the even-multiple barrier, so it has fewer than L/2 low updates. At each plateau (t,C) let h_low be the least eligible low clock pair (time,prime), or infinity if missing. For any eligible high prime p, with p dividing C+sigma (sigma in {-1,+1}), compute its next parity clock h_p. Require h_p<=K and lexicographic h_p<h_low. Call this an admissible high candidate at the plateau.

The actual next high selection, if it exists, is the least admissible high clock at the FIRST shadow plateau possessing an admissible high candidate. Induction over the preceding low events proves this: before that plateau every actual choice equals the low shadow's choice, including ties; at that plateau the actual MIN choice is the least high clock. If no plateau has a candidate, the actual path terminates without another high.

For a tagged source at cost r<b, mark it risky if ANY admissible high candidate on ANY plateau would increase the chosen cost. For ALL, this is simply membership of p in the seen-high set. For RESIDUAL, for p<Q the old multiplicity must be >=a+1; for p>=Q use its previous pre-event C, the intervening high history, and the prospective E to classify the return exactly as in the parent note. The ghost is allowed to continue past the real first high; this overcounts risk, never removes an actual bad hit. Count a source at most once in each layer, even if it has many candidate clocks. Freeze true terminals and budget-excluded sources.

Let g[j,r] be the number of risky original sources in layer (j,r). Then f[j,r]<=g[j,r] by the exact shadow argument. Thus one can replace f by g in (2), obtaining an explicit sufficient arithmetic problem that does not require computing which high candidate wins against all other high candidates:

    liminf_(dyadic X) (1/N) sum_(j<m) max_(0<=r<b)(g[j,r]-eta*w[j,r])_+ <1.  (3)

The envelope reduces a step to divisibility of C+sigma and a finite LOW-only clock comparison, with a history-membership filter. The unresolved part is source-weighted aggregation on these ACTUAL history layers. CRT for fixed residues does not on its own control the dependence of the previously seen set or multiplicity on C. Equation (3) is not yet proved asymptotically. The next arithmetic target is to estimate this specific layer excess, preferably first for ALL (no multi-donor classification or sieve premise), and also for RESIDUAL as a fallback with smaller observed risk.

## 4. Finite tests and falsified stronger route

Compiled both standalone C++17 auditors with g++ -std=c++17 -O3 -Wall -Wextra -Werror. Run each binary on:
    256 1024 4096 16384 65536 262144 1048576 4194304
Files: research/min_stopped_budget_audit.cpp, research/min_stopped_ghost_audit.cpp.
Budget code verifies 6140 literal parity-GCD clock comparisons for X<=1024, exact mass conservation, absorption and total truncated cost. Ghost code checks every next high choice against the direct MIN wheel (including terminal cases), and asserts actual cost increment implies risk. Local compiled source blobs 59b69da34bbf144271aa2e82c76d7840a73a2483 and b196d4f1fb4e0632a0863eea238c9f33fa5f5b27; independently read back identical at a8f939e57b770d4419e85d470ee5c02c1efac833 and 7f43256538d43e3481dde75616073f4ce5ade1d5.

| X | P | hard killed | max residual cost | max ALL cost | ghost excess/N RESIDUAL eta=.2 | ghost excess/N ALL eta=.4 |
|--:|--:|--:|--:|--:|--:|--:|
|256|10|0|1|4|0|.0765625|
|1024|19|0|0|3|0|.00117187|
|4096|35|0|5|16|.00654297|.0401367|
|16384|64|4|14|27|.015625|.038501|
|65536|119|41|30|46|.0181763|.0440918|
|262144|213|144|29|51|.0270218|.0791794|
|1048576|390|344|56|82|.0619247|.127193|
|4194304|712|1081|84|127|.0408055|.181751|

Neither soft budget was exhausted by any source in these windows. At X=4194304, N=2097152, m=1424, residual b=356; actual longest prefix 189, total residual increments 2423648, ghost residual risky source-ranks 3127841, total ALL repeats 11810091, ALL risky source-ranks 14198948. The independent ghost comparator makes 33660789 checks at this window alone, counting next-high choices and terminal cases. Ghost risk peak across stages divided by N was .0413733 for RESIDUAL and .253734 for ALL. Actual max cost-increment fraction among still-budget-unexcluded sources (including frozen terminals) was .0307727 and .198897 respectively. Among currently MOVING sources only, both actual fractions reached 1 at this largest window: the proposed active-only uniform <1/2 rule is false. This is not a counterexample to (2) or (3). For actual rather than ghost flows, cumulative excess/N at eta=.2 RESIDUAL was .0198655, and at eta=.4 ALL .0767188.

At X=256 there are 123 twin terminals among 128 sources; at every other listed window all actual sources terminate at twins before m. The asymptotic clock prerequisite is not met at these scales, so the finite comparison values are diagnostics, NOT an asymptotic proof or a new finite twin certificate. In all runs y=7; growing LOW cutoff is only an asymptotic option.

Status PARTIAL. Exact stopped-layer and ghost-envelope deductions on paper, finite validation PASS, remote code readback verified, no new Lean proof. Main unchanged. The remaining analytic estimate (3) is the next explicit target, not a proved uniform risk bound.
