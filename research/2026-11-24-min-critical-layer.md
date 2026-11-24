# Exact stopped-budget kernel, critical layers, and first-hit marginal transport

Date: 2026-11-24 JST. Continuation of b5526abc16f8e64bf7697d5015d31e254f47c1ac (stopped MIN budgets and LOW ghosts). The new results below are finite identities and conditional asymptotic reductions on paper, not Lean-checked theorems. The twin-prime conjecture and the required arithmetic discrepancy estimate remain open.

## 1. Exact comparison identity (ALL and RESIDUAL)

Retain the canonical actual source M, cutoff K(M), high labels p>y, P=pi(B)-pi(y), N=X/2, m=2P, stopped cost b, and layer mass w[j,r], increment flux f[j,r], ghost risk g[j,r] of the parent note. Each source freezes after reaching its true terminal or b. Thus 0<=f<=g<=w and sum_r w[j,r]=N. Take fixed 0<eta<b/m with constant separation from b/m.

Define
    F_j(r) = Pr(Bin(m-j,eta)>=b-r)
    k[j,r] = Pr(Bin(m-j-1,eta)=b-r-1), 0<=r<b.

F_j(b)=1 and F_m(r)=1_{r=b}. The auxiliary binomial recurrence gives
    F_j(r)=(1-eta)F_(j+1)(r)+eta F_(j+1)(r+1).
The difference F_(j+1)(r+1)-F_(j+1)(r) is k[j,r].
Taking the difference of sum_r w[j,r] F_j(r) across a step and using exact layer transport therefore gives, after telescoping,

    K_b/N = F_0(0) + (1/N) sum_(j<m,r<b) k[j,r] (f[j,r]-eta*w[j,r]).    (1)

This is an equality for deterministic tagged sources; independence is used only to define the comparison kernel, not to model the MIN path. Replacing f by g and dropping negative terms gives two successively weaker upper bounds, the signed and positive kernel bounds:
    K_b/N <= F_0(0) + (1/N) sum k (g-eta*w)
          <= F_0(0) + (1/N) sum k (g-eta*w)_+.
Since sum_(r<b) k[j,r]<=1, the latter is no larger than the old maximum-excess bound F_0(0)+(1/N)sum_j max_r(g-eta*w)_+. Thus this improvement is uniform, not just empirical.

## 2. Only a critical strip is needed

Take ALL: b=P, eta=2/5. RESIDUAL also works with b=ceil(P/2), eta=1/5. Let W=sqrt(3m log P), P>=2, and
    S = {(j,r): 0<=j<m, 0<=r<b, |b-r-1-eta*(m-j-1)|<=W}.
The binomial point probability outside S is at most 2 P^-6 by Hoeffding's inequality (for m-j-1=0 the distribution is a point mass and the outside value is zero). For each j the sum of positive errors is <=sum_r g<=N. Consequently the contribution outside S, divided by N, is O(P^-5). Also F_0(0)=o(1) by Chebyshev. Thus
    K_b/N <= (1/N)sum_((j,r) in S) k[j,r](g[j,r]-eta*w[j,r])_+ + o(1).    (2)

For ALL, a source with a candidate at rank j>=1 has made exactly j high selections, so r<=j-1 before absorption, and j=0 has no repeat candidates. Thus in S a nonzero positive error requires
    P-j - (2/5)(2P-j-1) <= W,
    j >= P/3 - O(sqrt(P log P)).
For example all ranks j<P/4 can be discarded asymptotically, with an exponentially small error. The RESIDUAL counterpart has j>=P/8-O(sqrt(P log P)). This eliminates the early high-incidence regime without any arithmetic estimate on it. The new OPEN sufficient condition is that the liminf of the right-hand normalized strip sum (without o(1)) is <1. The canonical clock and pigeonhole argument then gives twin primes on an unbounded sequence of dyadic windows, with no reliance on the residual-sieve classification for ALL.

## 3. A genuine mixed-history counterexample

At X=256, B=43, LOW7, original M=303 and M=307 have the following first two high selections:
    M=303: (t,p,C_after)=(308,11,616), (340,17,646)
    M=307: (312,13,624), (340,17,646).
Both are at (j,r,t,C)=(2,0,340,646), with different original cutoffs K=530,537, both exceeding the next event times. Their identical next low event is p=3 at t=342, C_after=648; the next high is p=11 at t=343. For M=303 this is a repeat; for M=307 it is fresh. This is a counterexample on ACTUAL canonical MIN sources to determining the next repeat solely from (j,r,t,C), even where cutoffs do not affect that next step. Independently checked by literal parity GCD iteration. It is not a counterexample to the weighted bounds. One must preserve history incidences or upper-bound them.

## 4. Eliminate the source-specific cutoff in sufficiently large prefixes

Each next-high block, if it exists, consists of a LOW-only segment with elapsed time <3L and a final high wait <=2B. Let D=2B+3L. For mD<min_M(K(M)-s), a cutoff-free simulation of the first m high steps is identical to the canonical one, until actual termination. The same is true for all LOW-ghost candidate clocks tested at ranks j<m: the entire ghost low trace takes <3L and every eligible high clock waits <=2B. All these times are <=s+(j+1)D<K(M). The condition holds eventually because m=2P, P~B/log B, L=o(B) and min horizon length >=3X/4-2. Thus one common deterministic high-step map T(s), label ell(s) (or cemetery at termination), and ghost candidate set A(s) may be used at all ranks, independent of the initial M's cutoff. Terminal states have no high candidates. Here s denotes the physical pair (t,C), distinct from the initial time notation in the parent. The finite audit below keeps the ORIGINAL K(M), since this asymptotic prerequisite is not met there.

## 5. A second, layer-free route via linear first-hit marginals

This route treats ALL repeats and uses no per-source joint history or residual classification. Run the uncapped high-prefix map of section 4 to rank m. Let mu_j(s) be the total original-source mass at physical state s, and nu_(j,p)(s) the part of that mass that has NEVER selected p. At j=0, nu_(0,p)=mu_0. With cemetery convention and ell(cemetery)=bottom, the exact recurrences are
    mu_(j+1) = T_* mu_j,
    nu_(j+1,p) = T_*(1_{ell!=p} nu_(j,p)).
Equivalently nu is the transfer with killing at the first p selection. Thus the tagged incidence mass for p is W_(j,p)(s)=mu_j(s)-nu_(j,p)(s). This is additive across coalesced histories, whereas the repeat indicator itself is not a state function (section 3).

The total repeat-candidate incidence (counting distinct p per source-rank, not the number of plateaux where that p occurs) is
    I_j = sum_s sum_(p in A(s)) W_(j,p)(s).
This upper-bounds the number of ghost-risk sources, with or without budget absorption. The analogous exact total actual repeat flux on the uncapped process is sum_(s:ell(s)!=bottom) W_(j,ell(s))(s). This recurrence does not recover the joint cost-layer distribution; the following inequality avoids needing it.

At active rank j in ALL, the cost r=j-#seen is in [max(0,j-P),min(j-1,P-1)] if below b=P. Define lambda_j=max k[j,r] over that interval, zero for an empty interval. Since (g-eta*w)_+<=g, (1) implies

    K_P/N <= F_0(0) + (1/N)sum_(j<m) lambda_j I_j.    (3)

The sufficient condition liminf (sum lambda_j I_j)/N<1 is OPEN. It is less sharp than the full layer kernel bound, but requires only separate one-prime killed linear transfers. It is a new concrete target for arithmetic or operator estimates with no joint history bookkeeping. Another exact expression follows by propagating the first-hit mass nu_(i,p) restricted to ell=p forward under T: W_(j,p) is the sum of these disjoint first-hit source masses propagated from ranks i<j. This expresses I_j as a first-hit/future-candidate correlation. The formula is not a decorrelation theorem.

## 6. NEW arithmetic lemma: ghost-risk density in CRT residue cells

Here the ghost has NO cutoff as in section 4. Fix an even LOW modulus L=2 product_(3<=q<=y) q, a low residue class u=(t mod L,C mod L) with C even, and p>y, so gcd(p,L)=1. The entire LOW-only shadow relative trace (elapsed times and horizon gains) depends only on u: LOW clock periods 2q divide L, and the LOW divisibility checks have moduli q dividing L. The finite trace has a final plateau with no LOW clock and earlier plateaux with waiting lengths d_i to the next LOW event. By the established barrier/time bound, sum_i d_i<3L.

Choose residues (t mod p,C mod p) uniformly among the p^2 pairs, in the CRT cell fixed by u. Let A_(p,u) be the set of residue pairs for which p is an admissible high ghost candidate at some plateau. This property is determined by these residues together with u (including parity), since the p clock has period 2p. Write d_(p,u)=|A_(p,u)|/p^2.

At a fixed earlier plateau, a side sigma in {-1,+1} fixes precisely one residue of initial C modulo p by p | C+E_i+sigma. The p clock must occur strictly BEFORE the next LOW clock; p>y loses a tie. For the fixed time parity, at most d_i residues of initial t modulo p can place this p clock within that waiting interval. Therefore at most 2d_i pairs are eligible at that plateau. At the final plateau the two divisibility residues contribute at most 2p pairs (all time residues). Union bound and sum d_i<3L give the uniform density estimate

    d_(p,u) <= min(1, 2/p + 6L/p^2).    (4)

The final plateau alone has density 2/p; in particular the leading term does not grow with the number of LOW plateaux. The arithmetic lemma is an exact residue counting argument, not a statement that the actual source-tag distribution is uniform. It also applies to any subpopulation of tagged sources when expressing its discrepancy relative to uniform residue weights.

For a tagged population (e.g. a particular active cost layer, or all uncapped active sources at a rank), let W_(j,p,u) be its p-seen mass in low class u and W_(j,p,u)(v) the mass in pair v modulo p. Define signed discrepancy
    Delta_(j,p,u) = sum_(v in A_(p,u)) W_(j,p,u)(v) - d_(p,u) W_(j,p,u).
Then the exact incidence decomposes into a CRT baseline plus these signed discrepancies. For any Q=B/(log B)^alpha with fixed alpha>0 and L<=sqrt B, the large-label baseline is at most
    N sum_(Q<=p<=B prime) (2/p+6L/p^2) = o(N).
Indeed the first sum is O(log log B/log B) by prime counting and partial summation, and the second is O(L/(Q log Q)). For a particular layer the same bound is o(w[j,r]) in place of o(N). This resolves the unweighted large-label baseline uniformly over the history populations; the source-weighted discrepancies are NOT bounded here.

A concrete next step is to bound these discrepancies on the critical strip from section 2, separating the small p<=Q and large p>=Q bands. The separate marginal recurrence in section 5 gives an exact way to propagate the required weights; simply assuming uniform residue pairs is invalid. The baseline from (4) by itself is not sufficient to sum over O(P) ranks with the layer-free kernel, and the small-band baseline need not be o(1). Neither of these missing estimates has been proved.

## 7. Reproducible finite tests

New code research/min_layer_kernel_audit.cpp includes the parent research/min_stopped_ghost_audit.cpp. Local compiled code Git blob dc4885d497e8b219cd866fb53773ac4d0cdfb447, independent readback at 2a5558c2edfc09fecfac96ba600af4a5510becee; parent included code blob b196d4f1fb4e0632a0863eea238c9f33fa5f5b27. Compile from repo root:
    g++ -std=c++17 -O3 -Wall -Wextra -Wno-return-type research/min_layer_kernel_audit.cpp -o /tmp/min_layer_kernel_audit
    /tmp/min_layer_kernel_audit 256 1024 4096 16384 65536 262144 1048576 4194304
-Wno-return-type is used because the included parent's main is macro-renamed (its missing explicit return is valid only for actual main). Tests assert the numerical telescoping identity to absolute tolerance 1e-10, the two envelope inequalities, positivity bound <= old bound, and equality of union risk and nonzero distinct-label incidence. The residue density lemma (4) is a paper argument; the code does not test the CRT baseline directly. The uncapped marginal transfer recurrence is also a paper identity; finite I_j is calculated by direct source replay, preserving each K(M), not via common T or a matrix implementation. Numerical values below are floating-point diagnostics, not certified rational bounds.

| X | P | Old max excess/N (ALL, excludes initial tail) | ALL positive kernel bound incl tail | ALL marginal sum (excludes initial tail) | RES positive kernel bound incl tail |
|--:|--:|--:|--:|--:|--:|
|256|10|.0765625|.252799627|.22765|.370351736|
|1024|19|.001171875|.137672294|.0337204729|.215529226|
|4096|35|.0401367188|.0591656626|.124665106|.148359983|
|16384|64|.0385009766|.0144703161|.0871127324|.0994015741|
|65536|119|.0440917969|.00148342485|.0340965615|.0307640221|
|262144|213|.0791793823|.0000246463548|.0071600699|.00609921206|
|1048576|390|.127192688|5.21620244e-8|.000393898499|.000554032811|
|4194304|712|.18175106|1.38889586e-11|3.21075433e-6|5.46292515e-6|

At largest X the ALL initial binomial tail is 1.49108266e-14, signed kernel bound is 3.75134869e-12, and no source reaches the stopped budget. Actual active source-ranks counted: 31,563,637. At X=65536 the mixed-history scan found 3396 distinct keys (j,r,t,C,next time,next label) containing both fresh and repeat sources. Mixed-history scan limited to X<=65536; -1 indicates not tested. The strict asymptotic clock prerequisite fails in these windows, and the high lengths are short relative to P. Thus the very small kernel bounds largely reflect early termination and the auxiliary binomial weighting; they do not show that the needed asymptotic estimates are established. The new results are the exact comparison identity, critical-strip reduction, cutoff-free common map, first-hit marginal formula, and CRT-cell baseline.

Status PARTIAL, paper deductions and finite diagnostic tests PASS, no new Lean compilation or unconditional bound on the critical-strip discrepancy. Main untouched.
