# A166944 Issue #4 — First-merger genealogy and sharp 39-to-one low-wheel compression

2026-11-23 JST. Work branch `research/issue-4-terminal-survivor-positive-budget`, parent Issue #1. This continues `research/2026-11-23-exact-inverse-gcd-fold-and-merger-bilinear.md` and `research/2026-11-23-synchronous-state-coalescence-vs-distinct-carry-layers.md`.

**Scope:** the algebraic identities below are paper proofs; the constants 133 and 39 have exhaustive finite C++17 state-space certificates and independent partial literal-step checks, but are not yet checked in Lean. All numerical data come from the *original parity-dependent squarefree-clipped GCD*, not a randomized model. The asymptotic twin-prime and A166944 strict-record conjectures remain unsolved.

## 1. Cohort births, first mergers, and varying source deadlines

For even dyadic X, put B=ceil(sqrt(7X)), and take canonical sources M odd in [X,2X). The original source M is born **after** the update at `s(M)=M+2` with even `C_M(s)=2M−2`, is updated at each n>s through its own cutoff `K(M)=floor((7M−1)/4)`, and leaves the active population before step `K(M)+1`. The time-n clipped GCD transition is the deterministic map F_n(C) of the preceding note. Two simultaneously live sources that have equal states at the SAME time will remain equal until the earlier source expires. Since M<M' implies K(M)<K(M'), the earlier source is always the one that expires first.

For an unordered distinct pair M<M', define the **first coincidence** tau(M,M') as the earliest integer t in [s(M'),K(M)] at which the POST-STEP states C_M(t) and C_M'(t) agree, if such t exists. There are exactly two possibilities:

* A BIRTH merger: tau=s(M') and C_M(s(M'))=2M'−2=2tau−6. These are **odd-time deficit-six reset-manifold coincidences**. Births must be inserted AFTER step tau; unlike update mergers, their newly born source was not eligible for a q-hit at n=tau.
* A STEP/FOLD merger: tau>s(M'), the two pre-step states at tau−1 are different, and F_tau sends them to an identical post-step state. The exact inverse divisor enumeration in the preceding note governs these new coincidences. At fixed tau simultaneous distinct predecessor cohorts should be combined in ONE batch to avoid fictitious sequential pairs. Source deaths are applied before the next step.

A pair may merge only once; state equality can never split while both sources remain active. Let `h_M(n)=sum_(q prime >=13, q|d_M(n))q`, with zero on unit/low-only steps. Set

    R(M;tau)=sum_(tau<n<=K(M))h_M(n).

This is exactly the common future high-q incidence reward of a newly merged unordered pair, excluding the first-merger step itself. Even if that step has a high q, distinct pre-states are NOT counted in the pre-step joined collision energy at that time.

**NEW EXACT genealogical identity (paper):** writing J_equal for the earlier same-q, same-time, identical-*prestate* second moment, and A_X=sum_(M,n)h_M(n),

    BOXED: J_equal − A_X
         =2*sum_(unordered M<M' with first coincidence tau)R(M;tau).  (GEN-BIRTH)

All different terminal cutoffs and births are included, and there is no counting of any pair more than once at the first-coincidence level. The same identity holds for arbitrary nonnegative q-incidence rewards shared after coincidence, not just the sum of prime labels.

Let Gamma_(t,M) be the NUMBER of later sources M'>M whose FIRST merger with M happens at time t. Then the equivalent linear-in-future-reward form is

    BOXED: (J_equal−A_X)/2=sum_M sum_t Gamma_(t,M)R(M;t).       (GAMMA)

This is a possible form for a source-transport renewal estimate, but GAMMA without an independent bound on Gamma and its correlation with R is NOT an asymptotic upper bound.

### Source-span bound on the TOTAL number of first mergers (paper)

At any coincidence of M<M', G_M(t)=C_M(t)−(2M−2) and G_M'(t)=C_M'(t)−(2M'−2) are nonnegative and

    G_M(t)=G_M'(t)+2(M'−M) >=2(M'−M).

As M' ranges over odd later sources, at most floor(G_M(K(M))/4) such M' can ever coalesce with a fixed earlier source M. Hence, with P_X=number of unordered canonical source pairs that ever merge,

    BOXED: P_X<=sum_M floor(G_B(M)/4)<=W_X/4.        (SPAN)

This is a genuine deterministic bound, distinct from the earlier high-q hit energy bound. **But** showing P_X=O(XB) only via SPAN would require W_X=O(XB), already strong enough to imply twin infinitude by previous results. SPAN is an accounting check, not a shortcut to the missing arithmetic estimate.

## 2. Exhaustive original-GCD first-merger genealogy

The companion C++17 `research/first_merger_genealogy_audit.cpp` independently generates the exact original parity-specific event traces for every canonical source and then sweeps absolute time. Deaths are processed before each step, all event-state moves are applied as a single simultaneous batch, and new canonical sources are injected after that step. At every newly merged cohort, it counts ONLY pairs from DIFFERENT predecessor cohorts and uses a sorted list of start indices to charge the **earlier** source's independently precomputed high-prime-weight suffix through its own K(M). An independent Python file, `research/independent_literal_first_merger.py`, computes EVERY step without prime-clock jumps and directly compares EVERY unordered pair for X256/512/1024.

The C++ asserts `2*sum first-merger pair rewards == independently accumulated sum high q weight*m_n(c)*(m_n(c)-1)` as an EXACT 64-bit INTEGER, on every checked interval; it asserts SPAN and the old high-event-count regressions. Strict compilation: `g++ -std=c++17 -O3 -Wall -Wextra -Werror`.

**Terminology for the following table:** low-fold means that all moving predecessor cohorts arriving at the merged output have **only low-prime clipped increments** (possibly accompanied by a stationary d=1 predecessor). High-fold means exactly one moving predecessor has a high-prime increment; multi-fold means at least two moving predecessors have high-prime increments. These are cohort-level classifications, not assertions about every individual new pair. In particular, a high-fold output may also include two different low-only predecessor groups.

| X | new unordered first-merger pairs P_X | post-merge joined off-diagonal J_equal−A_X | birth contribution to first-merger future reward | low-fold contribution | high-fold contribution | multi-fold contribution |
|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | 43,541 | 6,493,384 | 15.2% |55.7%|25.3%|3.8%|
| 16,384 |251,465 |88,920,646 |12.4%|58.8%|24.1%|4.6%|
|65,536|1,613,083|1,220,739,642|9.1%|60.1%|22.3%|8.5%|
|262,144|8,997,530|14,298,372,900|7.5%|60.5%|26.5%|5.5%|
|1,048,576|47,348,338|116,430,915,444|6.1%|61.0%|26.9%|6.1%|

At X1048576, the exact **unordered** future reward is 58,215,457,722, and the four disjoint credits are birth3,544,325,187, low-fold35,490,907,791, high-fold15,636,978,816, multi-fold3,543,245,928. This sums exactly to the recorded total, and doubling gives the existing independently measured identical-prestate off-diagonal high-q collision energy 116,430,915,444. There were 18,585,269 full nonunit events across 524,288 original starts; of these 5,516,751 had a high prime factor. Max simultaneous cohort size 1,039.

**Important negative finding:** at X1048576, only 11,491,022,586 of 58,215,457,722 (19.7%) of the future q weight was attributable to the **first high event after the first merger**. Most of the inherited joined collision energy comes from the second and later shared high events. Merely estimating the immediate next high transition of a new merged cohort cannot close the second moment. Moreover, 16,762,428 of 47,348,338 newly merged unordered pairs (35.4%) have **no** subsequent shared high event, so it is helpful to distinguish first-merger frequency from its future high-q *reward*.

Normalized finite pair counts P_X/(XB) decrease from 0.0625 at X4096 to0.01666 at X1048576; average future high q reward per newly merged pair is 1,229.51 at B2710 (0.454B). These are only observations; neither P_X=O(XB) nor a uniform O(B) average reward follows automatically.

## 3. NEW universal low-only terminal inverse-degree theorem (finite exhaustive certificate)

Consider the **restricted** wheel containing exactly the primes S={3,5,7,11}, product P=1155 and period L=2310. For a fixed absolute time t and even positive initial state c, run the LOW-ONLY GCD until no S-prime divides c−1 or c+1. The previous exhaustive 2,668,050-state certificate showed this takes at most **133 elapsed clock steps**, with at most22 nonunit events and at most1156 growth. Let L_t(c) denote the resulting constant c-value; it coincides with the restricted update after exactly 133 steps.

The restricted deterministic map satisfies

    L_(t+2310)(c)=L_t(c),
    L_t(c+2310)=L_t(c)+2310,

as statements about the final even c, for sufficiently positive times and states (clock congruences are period invariant). Therefore the exact number of distinct preimages of ANY fixed output Y can be computed by tabulating all **2310 choices of t mod2310** and **1155 choices of even c mod2310** and finding the largest fibre cardinality in the reduced output residue class.

**NEW EXHAUSTIVE FINITE THEOREM:** the largest inverse fibre of this terminal low-only map has **exactly 39 distinct even inputs**, reached for time residue t≡1840 mod2310 and output Y≡2028 mod2310. Hence

    BOXED: #{c even: L_t(c)=Y} <=39.                         (LOW-INV)

For any finitely supported nonnegative (or signed) input cohort weight function w(c), and its output pushforward `(L_t)_*w(Y)=sum_(c:L_t(c)=Y)w(c)`, Cauchy–Schwarz gives the **SHARP** bound

    BOXED: sum_Y ((L_t)_*w(Y))² <=39 sum_c w(c)².           (LOW-L2)

The constant 39 is optimal for unrestricted input weights: choose unit weights on the 39 distinct preimages of a fixed extremal terminal output. This gives input L2 square39 and output L2 square1521, exact ratio39. An independent Python **literal one-step GCD** auditor checks six time residues including the maximum 39 at t mod2310=1840, output mod2310=2028, the 133-step low-only termination, and equivariance under c→c+2310. The standalone C++ enumerates **all 2,668,050 states**, finding no inverse fibre larger than39.

**COROLLARY on fresh merger creation in a high-free block:** For a fixed cohort with no births, expirations, or full-wheel high-prime events during the next 133 steps, low-only transport can introduce at most

    BOXED: New unordered pairs <= (39−1)/2 * sum_c w(c)² =19 sum_c w(c)².

Proof: the new unordered pair count is half the increase in the L2 squared population as state groups fold, and LOW-L2 bounds that increase. If some orbits have high events, expire, or enter during the interval, they must be separated as boundary/high-event pieces; LOW-L2 is NOT an unrestricted theorem for the full adaptive wheel.

### A finite-shift consequence

A single newly merged pair of predecessor states with **both** increments low-only has `d,e|1155` and `C_pre1−C_pre2=e−d`, hence `|C_pre1−C_pre2|<=1154`. The low-low first-merge creation bilinear form therefore uses only differences from the 16 low divisors of1155 (at most 120 unordered divisor pairs), independently of B. The exact gcd validity test from the preceding note is still required. The measured dominance of low-fold genealogical reward suggests working with this finite collection of **short-shift adaptive state correlations**, together with LOW-L2, instead of expanding all primes and all past CRT histories.

## 4. Next analytic question (still OPEN)

The difficult quantity is not the raw total count of first mergers: it is their correlation with the future shared high-prime reward. In first-merger form,

    J_equal−A_X = 2 sum_M sum_t Gamma_(t,M) R(M;t),

with Gamma counting newly merged later starts, and R(M;t) counting ALL future shared q-weight (not merely the first high event). The first/second-wave CRT constraints cannot be applied to the dynamically selected weights as if the histories were independent.

A potential proof route is a **source-weighted renewal estimate at high-event restarts**: use LOW-L2 to compress every high-free 133-step block (factor at most39 in L2 squared), explicitly account for births at reset-type z=6 and the finitely many low-fold shifts, then establish a genuinely arithmetic upper bound on the positive high-event *amplification* and its subsequent cumulative q-weight. In particular, a 39-fold worst-case bound per block does not imply global contraction: chaining it over many high events would explode. A successful estimate needs either high-clock phase dispersion for transported populations or a bound on how often resonant high folds recur for already concentrated cohorts.

If that yields the earlier positive collision estimate J_X=O(XB²*pi(B)), twin-prime infinitude follows from the previously proved clock criterion. The more direct, potentially weaker target sum_q max_n mu_(q,n)=o(X) remains open. Finite observations of short-shift dominance, merger rates, or growth/sink absorption do not establish either asymptotic statement.

## Reproduce

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/first_merger_genealogy_audit.cpp -o /tmp/genealogy
/tmp/genealogy 256 512 1024 4096 16384 65536 262144 1048576
python3 research/independent_literal_first_merger.py 256 512 1024

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/low_only_terminal_inverse_degree.cpp -o /tmp/low_inv
/tmp/low_inv
python3 research/independent_low_terminal_inverse.py
```

All four sources must be retained with this note to reproduce its checks. No changes to the repository default branch; no Lean kernel proof or claim of twin-prime/strict-record resolution.
