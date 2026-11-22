# A166944: universal seven-step regeneration after an even X=0 state

Date: 2026-11-23 JST. **Status: exact elementary paper theorem with exhaustive mod-30 integer certificate and finite squarefree insertion audits. Not a global insertion-mean estimate or proof of infinitely many twin primes. No Lean kernel check.**

Related: [squarefree prime first-hit regeneration](2026-11-23-squarefree-prime-first-hit-regeneration-and-fibre-transfer.md), [squarefree sqrt-wheel average reduction](2026-11-22-squarefree-sqrt-wheel-mean-reduction.md), [previous A166944 and Shevelev comparisons](2026-11-22-shevelev-dual-reset-commuting-diamond.md).

## 1. NEW UNIVERSAL paper theorem: no exceptional 3-step "bridge defect"

In the original parity-gcd or ANY clipped version with fixed odd wheel L, define D(n), d(n), X(n)=2n-D(n). The exact recurrence is

    n even: d(n)=gcd(n,X(n−1)+3), clipped by L if applicable;
    n odd:  d(n)=gcd(n−2,|X(n−1)−3|), clipped by L;
    X(n)=X(n−1)+3−d(n).

**Theorem (paper, universally valid):** Suppose n0 is EVEN and X(n0)=0. Starting immediately AFTER n0, the first index m>n0 with X(m)=6 exists and

    BOXED: m−n0∈{3,5,7}.

Before this first hit of X=6, all nonunit increments are ONLY 3 and 5, even if the original gcd is unbounded or the wheel contains many other primes. The total intervening horizon growth b=D(m)−D(n0) is

    BOXED: b=2(m−n0)−6∈{0,4,8}.

Since m−n0 is ODD, m is odd. The state at m is exactly a canonical-shaped state

    D(m)=2m−6=2(m−2)−2,

so v=m−2 is an odd artificial canonical start. The proof is finite mod30 and does not assume initial twin primality, original record attainability, old wheel factorization, any bound on p, or a special cutoff (unless it ends before m).

**Proof sketch with complete reachability state constraints:** For X<6 along a trajectory originating at even X(n0)=0, the only possible positive even deficits are X=0,2,4. Up to the first X=6, reachable states satisfy:
    step1 odd: X=0 or2,
    step2 even: X=0 or4,
    step3 odd: X=6 or0 or2,
    step4 even: X=0 or4,
    step5 odd: X=6 or2,
    step6 even: X=4,
    step7 odd: X=6.
This is checked by using odd-position gcd(X−3), which is 3 or1 in those states, and even-position gcd(X+3), which is 3 or5 whenever an even step is reached. A 7-factor never occurs in the reachable even-step states. The few possible 3- and5-gates are controlled by n modulo30 (2·3·5). Their exhaustive distribution for the FULL gcd (or any wheel containing 3 and5) at EVEN n0 modulo30 is:

    bridge length 3: n0≡0,2,6,12,14,20,24,26 mod30 (8 classes);
    bridge length 5: n0≡4,10,18,22,28 mod30 (5 classes);
    bridge length 7: n0≡8,16 mod30 (2 classes).

If the wheel omits3 and/or5, the bridge is even shorter: L active in {1},{3},{5},{3,5} gives mod30 bridge histograms {3:15}, {3:10,5:5}, {3:12,5:3}, and {3:8,5:5,7:2}, respectively. This checks all four relevant small-prime presence patterns. Note: these are exact parity gcd computations with the previous horizon D(n0)=2n0; the state bound is algebraic and not dependent on actual original-record history.

## 2. Stronger NEW early-phase minus-p regeneration, no bridge-quietness hypothesis

Use the earlier growth-adaptive SQUAREFREE insertion setting: old wheel L with growth h=G_L(M), insert fresh p>6h+7 (so p>=11), old frozen terminal horizon C=2M−2+h, and define

    a=(p+h−1)/2, eps=a mod2, u=(C+p+1)/2=M+a.

An EARLY-phase p-hit has eps=0, so u odd.

PLUS p|C+1: first p-hit is ODD at n=u+2 with X=6, therefore direct canonical seed v=u; set b=0.

MINUS p|C−1: first p-hit is EVEN at n0=u−1 with X=0. By universal theorem, within k=3,5,or7 further steps, the ACTUAL enlarged-wheel trajectory (with L and p) reaches X=6. Since during the bridge only 3- and 5-divisible increments occur, p>=11 CANNOT refire inside it; the bridge is IDENTICAL to the L-only bridge. Let b=2k−6∈{0,4,8}; the new canonical seed is

    BOXED: v=u+b/2 = (C+p+1+b)/2.                (R)

Consequently the four early-phase regeneration TARGET RESIDUES modp are exactly subsets of

    BOXED: v modp ∈{0,1,3,5};                    (AP)

PLUS gives residue0, MINUS gives residue1,3,or5 according to the 3/5 bridge. In the MINUS case the bridge length and b are determined purely by n0 mod30, independently of the many old prime factors of L.

A natural old cutoff K(M) can end during the ≤7-step bridge. Such a boundary piece then has extra growth b_partial≤8 and no new p-refire; no global completion before K is presumed.

## 3. Exact one-shot transfer after canonical regeneration, and its scope

Let H_L(v;K) be cumulative growth under the OLD L-only original parity recursion from seed (v+2,2v−2) through the ORIGINAL cutoff K=K(M). Assume that the regenerated seed v+2<=K.

If the enlarged trajectory does not have a second p-hit before K, then

    BOXED: Delta_p(M)=G_(Lp)(M)−G_L(M)
           = (p−1)+b+H_L(v;K).                      (T)

A sufficient, checkable no-refire criterion:
    PLUS b=0: H_L(v;K)<p+1, because post-first-p horizon ≡−2 modp;
    MINUS: b+H_L(v;K)<p−1, because post-first-p horizon ≡0 modp.
These are sufficient but NOT necessary because foreign L events can repeatedly preempt p clocks.

**Extension of deterministic fibre-weighted second-moment inequality:** Partition ONE-SHOT early p-hits into four groups S_r by target residue r∈{0,1,3,5} modp (PLUS r0, MINUS three others). For group r let N_r=|S_r|, W_r=sum_(M∈S_r)G_L(M), V_r the SET of distinct regenerated targets v. Because within each group b is fixed and

    v=(2M−2+G_L(M)+p+1+b)/2,

each collision v(M)=v(M') forces old frozen horizon C_L(M)=C_L(M'), so the old fibre energy yields

    sum_(v∈V_r) k_v² <= N_r+W_r/2.

Using (T), b≤8, and Cauchy-Schwarz,

    BOXED: sum_(M∈∪S_r) Delta_p(M)
      <= (p+7)*sum_r N_r
         +sum_(r∈{0,1,3,5})
            sqrt(N_r+W_r/2)
            *sqrt(sum_(v∈V_r)G_L(v)^2).             (F)

This is a genuine, non-probabilistic transfer estimate covering ALL early phase one-shot events and all 3/5 bridge outcomes. It is NOT yet an upper bound O(sqrt X) on an individual prime stage averaged over dyadic starts: restricted second moments G_L(v)^2 and unsafe/late/refire contributions remain uncontrolled.

## 4. Independent checks in genuine squarefree prime insertion stages

The exact C++ original parity-gcd stage auditor was extended to trace ALL early MINUS branches, not just 3-step-quiet cases. For dyadic intervals I_X (squarefree old wheels are all preceding odd primes, p inserted once):

    X          early MINUS      bridge k3   bridge k5  bridge k7
    4096            126             111         2         13
    16384           586             498        37         51

For stage samples that completed the bridge before cutoff, the stronger sufficient no-refire test b+H_L(v;K)<p−1 held in 67 and322 cases respectively; the exact identity (T) was verified for each such case. Actual p-refires among the early MINUS branches were just3 and26 cases, respectively (vs original 3-step-quiet classification 3 and22), so relatively few near-bridge false negatives remain.

A separate [stdlib Python modulo30 certificate](zero_deficit_bridge_exact_audit.py) enumerates all even residue classes and presence/absence of3,5, plus representative higher wheels. The C++ auditor [squarefree_prime_regeneration_audit.cpp](squarefree_prime_regeneration_audit.cpp) contains exact universal p-event residue checks at every event, and now also the 7-step bridge and transfer checks.

## 5. Next proof target

The prior proof obstruction had four categories: safe-plus, safe-minus-with-3-step-bridge, **safe-minus-bridge-defect**, and unsafe/late/refire. The **bridge-defect category is now eliminated in full**. Every EARLY safe p-hit canonically regenerates, and its target lies in one of FOUR fixed residues modp, with at most8 bridge growth.

The narrowed target is a short-interval **RESTRICTED FOUR-RESIDUE RENEWAL-ENERGY inequality** controlling

    sum_(r∈{0,1,3,5}) sqrt(N_r+W_r/2)
             sqrt(sum_(v∈V_r)G_L(v)^2)

plus a separate treatment of late-phase X=2p,2p+6; unsafe p<=6G_L+7; and genuine p-refires. The old first-split 2/p complete-lift count remains insufficient for dyadic windows whose length is much shorter than 2Lp.

Nothing in these local regeneration theorems proves the per-prime signed dyadic growth bound or twin-prime infinitude; the key unbounded-X average estimate is still open.
