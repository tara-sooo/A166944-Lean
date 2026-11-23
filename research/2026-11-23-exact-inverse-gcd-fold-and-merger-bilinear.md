# A166944 — exact inverse clipped-GCD map, resonant folds, and first-merger bilinear energy

Date: 2026-11-23 JST. Scope: Issue #4, branch `research/issue-4-terminal-survivor-positive-budget`, following `research/2026-11-23-synchronous-state-coalescence-vs-distinct-carry-layers.md`. The arithmetic identities here are **paper proofs**. The companion Python is a **finite independent audit**, not a Lean proof. No twin-prime infinitude or OEIS A166944 record theorem has been proved.

## 1. Exact one-step inverse formula — stronger than a divisor bound

The original parity-specific GCD update at step `n` is

    a_n = n if n even, else n-2;
    sigma_n = +1 if n even, else -1;
    A_n = product of distinct odd primes p<=B dividing a_n,
    d_n(C) = gcd(A_n,C-sigma_n),
    F_n(C) = C+d_n(C)-1.

Here `C` is even and in the legal positive state range; `A_n` is squarefree and odd, although the formal wheel `L_B` may be enormous. Fix an even post-step output `Y`. If it has predecessor `C`, necessarily `C=Y-d+1` for the unique odd factor `d=d_n(C)`; hence `d | gcd(A_n,Y+1-sigma_n)`. More strongly, the exact set of predecessors is

    BOXED: F_n^{-1}(Y) = {Y-d+1:
         d|D_n(Y), C=Y-d+1 is an allowed even positive predecessor,
         gcd(A_n,Y+1-sigma_n-d)=d},
    D_n(Y)=gcd(A_n,Y+1-sigma_n).                       (INV)

Proof: substitute `C=Y-d+1` into the clipped-GCD rule. Conversely the displayed exact gcd equality makes `F_n(C)=Y`. The `gcd(...) = d` clause is **essential**: not every divisor of `D_n(Y)` gives a valid predecessor, because a different prime of `A_n` may divide `Y+1-sigma_n-d`. It follows unconditionally that

    BOXED: |F_n^{-1}(Y)| <= tau(D_n(Y))=2^{omega(D_n(Y))}.   (BRANCH)

Thus branching happens only at resonant post-state values `Y+1-sigma_n` sharing a prime with `a_n`. At even `n=30`, B>=5, post-state `Y=30`, `A_n=15`, the FOUR exact predecessors are `C=16,26,28,30`, giving increments `15,5,3,1` respectively; all map to 30.

## 2. Prime-only clock is an EXACT fold, not a general random map

Suppose `A_n=q` for a SINGLE odd prime q. Then

    F_n(C) = C+q-1 if C ≡ sigma_n modq,
           = C otherwise.

For every even `Y`, there are exactly

    2 inverse state classes if Y ≡ sigma_n-1 modq,
    0 if Y ≡ sigma_n modq,
    1 otherwise,

ignoring only the positivity/finite-domain cutoff. The two predecessors of a doubly-covered output are **`Y` and `Y-(q-1)`**. The q-hitting branch is the latter and the non-q-hitting branch is the former. Hence two distinct q-HITTING pre-states never newly merge at that prime-only clock; a newly merged pair contains a q-hit branch and a non-hit branch. This helps distinguish inherited multiplicity from freshly created multiplicity at a high clock.

For arbitrary finite nonnegative source weights `w(C)` on even pre-states and post-weights `w'(Y)=sum_(F_n(C)=Y) w(C)`, the exact L² increase is

    BOXED: sum_Y w'(Y)^2 - sum_C w(C)^2
          = 2 sum_Y sum_(d<e in valid inverse divisors)
                         w(Y-d+1) w(Y-e+1) >=0.       (ENERGY)

For a prime-only clock `A_n=q`, this simplifies to the explicit **additive-shift bilinear form**

    BOXED: L2_increase = 2 sum_(Y even, Y≡sigma_n-1 modq)
                                w(Y) w(Y-q+1).       (SHIFT)

This is an exact identity for a single update of one fixed active cohort, with no source births/deaths in that step. In the real family, starts enter at their `s(M)` and end at their `K(M)`; those boundary terms must be included when summing over time. It does NOT claim the bilinear form is small.

## 3. Uniform post-state inverse statistics are CRITICAL, but the actual source measure is not uniform

Because `A_n` is odd, `d_n(C)` depends only on `C mod A_n` and

    F_n(C+2A_n) = F_n(C)+2A_n.

The induced map on the `A_n` even residue classes modulo `2A_n` has exactly `A_n` inputs and outputs. Therefore, for the number `b_n(Y)` of inverse residue classes of each even output class,

    BOXED: average_Y b_n(Y) =1.                       (MEAN1)

From BRANCH, and CRT independence of the uniform output residues,

    BOXED: average_Y b_n(Y)^2 <= product_(p|A_n)(1+3/p).  (MEAN2)

For `A_n=q` prime, the EXACT second moment is `1+2/q` (one doubled class, one missing class, `q-2` single classes). The general upper bound is not asserted sharp.

The crucial distinction: uniform-average inverse branching is not the true collision probability of the **adaptively transported** canonical-start measure. A large fraction of source mass can accumulate precisely in exceptional resonant output classes. This reconciles these low one-step averages with the observed ~99.3% of synchronous q-clock energy coming from already coalesced pre-states at X=1048576. A naive application of MEAN1/MEAN2 at actual source locations would be incorrect.

## 4. Concrete new proof program: first-merger accounting

For two distinct original starts M,M', their first time τ of having an identical legal post-state (when both have started) is a UNIQUE first-merge event if it exists. After τ the forward GCD evolution agrees until the earlier canonical cutoff. Therefore any future high q-hit shared by the pair can be charged to τ exactly once. Let

    R(M,M') = sum_(high q hits at times n>τ, n<=min(K(M),K(M'))) q.

Then, with a suitable interpretation of `q`-hit weights in composite increments, the already studied joined off-diagonal q-clock energy has the exact genealogical decomposition

    BOXED: J_join - A_X = 2 sum_(unordered pairs that ever merge) R(M,M').  (GEN)

Every pair counted in J_join had already merged by its pre-event time; no pair is charged twice at the first-merge stage. Since at a single high event the sum of distinct high prime factors q is at most `(13/12)*(d-1)`, the future shared q-incidence mass is bounded by `(13/12)` times the remaining common growth after τ. This creates a *future-growth* charge complementary to the existing *past-growth* CHARGE2 inequality. It still requires an estimate on the number, timing and remaining lifetimes of first mergers; the identity alone does not imply a useful asymptotic upper bound.

How to analyze newly merged pairs: the exact valid predecessor list `INV` gives the cross-correlation bilinear terms in `ENERGY`. For a prime-only q clock the only new merge shift is `q−1` (`SHIFT`). Multiple-prime clocks have a finite divisor-pair expansion with shifts `e−d`, `d,e|A_n`. Aim to prove a **source-transport weighted** bound on sums of these resonance-restricted shifted products, possibly grouped into low-prime blocks of length <=133. Ordinary uniform CRT gives only the mean with respect to an artificial uniform state, not the transported source population. A bound strong enough to control first-merge creation AND future shared high-prime occupancy would close the dominant joined part of the earlier positive q-clock criterion.

Complementary open target (from previous note): over q>=13, `sum_q max_n mu_(q,n)=o(X)` suffices directly for twin infinitude via the previous 133-step high-event clock theorem; the stronger positive collision-moment `J_X=O(XB²*pi(B))` also suffices. The new inverse formulas make the source of crowding precise, but neither target has been proved.

## 5. Independent finite audit

`research/exact_inverse_gcd_fold_audit.py` is standalone and applies the literal parity-specific clipped GCD directly, without invoking the older event-jump scanner. Checked the inverse formula against **110,500 even positive input states** (`n=5..225`, `C=2..1000`), all relevant outputs, one-step periodic mean and second moments at `n=15,30,42,105,210,462`, and exact weighted L² merger identities with nonconstant source weights at `n=15,30,42,105,210` including the q=17 prime-only shifted-product identity. All PASS.

Selected finite inverse moments for B=53:

| step n | A_n | inverse-class mean | inverse-class second moment | maximum inverse classes |
|---:|---:|---:|---:|---:|
|15|13|1|1.153846|2|
|30|15|1|2.066667|4|
|42|21|1|2.047619|4|
|210|105|1|2.485714|8|
|462|231|1|2.229437|8|

These are **arithmetically checked examples** and not empirical evidence for the transported-state dispersion needed by GEN. No Lean compilation, no main modification.

Run:

```sh
python3 research/exact_inverse_gcd_fold_audit.py
```

### Mathematical caveat

The parity barrier for twin primes is not removed by the uniform local divisor formulas alone. Source-weight correlations on the dynamically selected resonant outputs are the genuinely new estimate. Related context: Tao, *254A notes 4: some sieve theory* (https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/); Friedlander-Iwaniec, *Asymptotic sieve for primes*, Ann. Math. 148 (1998), pp.1041-1065 (https://annals.math.princeton.edu/articles/13036). Their bilinear techniques are conceptual precedents, not proofs of GEN or any requested bound for our GCD dynamics.
