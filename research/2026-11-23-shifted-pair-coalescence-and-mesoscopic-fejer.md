# A166944: shifted-source pair correlations, universal 55-residue reset root confinement, and mesoscopic decoupling of coalescing trajectories

Date: 2026-11-23 JST. Project: `tara-sooo/A166944-Lean`, assigned Issue #4 (parent #1), dedicated branch `research/issue-4-terminal-survivor-positive-budget`. This work follows `research/2026-11-23-reset-graph-coboundary-reverse-transfer-and-shifted-correlations.md` and the reset-origin CRT research notes. **Elementary statements below have paper proofs, not Lean-kernel proofs; all numerical tables are finite exhaustive original-parity clipped-squarefree-GCD computations. Twin-prime infinitude, the original strict-record A166944 conjecture and all new asymptotic estimates remain OPEN.**

## 1. EXACT shifted-source correlation split

For even X, B=ceil sqrt(7X), N=X/2, and odd canonical M_j=X+1+2j, let `P_j` be the finite sequence of actual **high-event RESET** nodes v=(t,z) in its FULL clipped squarefree wheel. Define h_B(v) using the already derived exact prime-candidate load

    h_B(v) = sum_(103<=q<=B prime) q*1{t mod q in U_(q,r,z)}
             - pi_[103,B]*u(r,z),

where r=t mod 2310 and U comes from the 3/5/7/11 low-only prefixes following a reset. Put `a_j=sum_(v in P_j) h_B(v)` and `S_X=sum_j a_j` (all starts with no high reset have a_j=0). These are NOT mean-centered by subtracting the sample mean.

Two distinct original starts j,k **coalesce** when `P_j ∩ P_k` contains at least one same absolute reset state (t,z); since the reset forward map is deterministic, after that state the two histories share the same future reset nodes, subject to their DIFFERENT canonical cutoffs. For each 1<=ell<N, the raw shifted sum splits EXACTLY as

    C_X(ell) = sum_(0<=j<N-ell) a_j*a_(j+ell)
             = C_X^join(ell) + C_X^disjoint(ell),

where joined pairs have intersecting P and disjoint pairs have nonintersecting P. The same equality holds for the sample-centered products, but the subsequent Fejer criterion uses the RAW products.

**Observed finite correlations X262144 (B1355, N131072; every odd original start enumerated):**

| start-index shift ell | #pairs with a shared reset state / #pairs | centered cross-product mean overall | joined contribution | disjoint contribution |
|---:|---:|---:|---:|---:|
| 1 | 41.1876% | 1,849,155 | 1,494,758 | 354,397 |
| 32 | 3.7798% | 545,226 | 138,182 | 407,044 |
| 256 | 0.6727% | 165,403 | 28,257 | 137,146 |
| 512 | 0.2359% | 86,989 | 15,152 | 71,837 |
| 1155 | 0.0246% | -1,202 | +5,027 | -6,229 |

Each mean in the last three columns uses the ALL-pair denominator N-ell (rather than the number of joined/disjoint pairs); hence they add exactly, modulo displayed rounding. Near ell=1, ~80.8% of the positive centered correlation comes from source pairs that actually share a reset state. At ell=32, it is ~25.3%, and at ell=256 ~17.1%; disjoint-path correlations therefore **cannot** be ignored. This distinguishes the structural coalescence contribution from genuinely separate arithmetic histories. Finite numbers do not imply an asymptotic mixing rate.

## 2. NEW universal 55-consecutive-residue root window (PAPER)

At any true high reset (t,z), z∈{0,6}, and every subsequent low-only restricted prefix with cumulative even growth e∈[0,100], the plateau has state C=2t-z+e. A high prime q>=103 is a candidate if it divides C-1 or C+1. Equivalently,

    2t ≡ z-e±1 (mod q).

Writing inv2=(q+1)/2 mod q and `k=(z-e±1-1)/2`, we have the **EXACT enclosure**

    BOXED: U_(q,r,z) ⊂ {inv2+k (mod q): -51<=k<=3}.          (A1)

This is a window of 55 CONSECUTIVE residues INDEPENDENT of `(r,z)`, the q-band, and the adaptive history. Its actual distinct subset U_(q,r,z) has 2..31 elements per prior 4620-state finite certificate. The enclosure follows only from z∈{0,6}, 0<=e<=100 even, and the two neighbors ±1.

**Same-prime pair exclusion:** If two (possibly from different source histories) high reset nodes (t,z),(t',z') both have q>=103 as a candidate, then subtracting the two root enclosures gives

    BOXED: q | (t'-t)-k for SOME integer k with |k|<=54.     (A2)

In particular, if t'<t+q and 55<=t'-t<=q-55, simultaneous q-candidacy is **IMPOSSIBLE**. This restriction is pointwise even for completely ADAPTIVE reset origins: the correlated histories do not invalidate the divisibility. The new auditor asserts A1 for every generated low-wheel rootset at all tested q and asserts A2 for every q shared by first-reset nodes in studied shifted pairs.

For a mathematical *uniform-phase benchmark* (not actual reset-origin equidistribution), fixing two low-wheel cells (r,z),(r',z') and a time translation delta, and uniformly varying the FIRST t mod q, the centered per-prime loads f_U(t)=q*1_{t in U}-|U| obey

    E_(t mod q)[f_U(t)*f_V(t+delta)]
       = q*|U ∩ (V-delta)| - |U|*|V|.                    (A3)

When `55<=delta<=q-55` the intersection vanishes by A2, so this benchmark covariance is **negative**, exactly `-|U|*|V|`. A3 is a correct arithmetic calculation for a uniformly varied artificial residue; it does NOT assert that actual pairs of reset times, or actual source-index pairs, have uniform modulo-q phases. Mixed-prime q!=q' correlations are not controlled by A2.

## 3. NEW mesoscopic Fejer theorem: joining paths can be discarded with a long enough window (PAPER)

For a general finite source-load sequence (a_j), and 1<=H<=N, let

    Q_H = sum_(n=0)^(N+H-2) (sum_(k=0)^(H-1) a_(n-k))^2,

with zeros outside 0<=j<N. The previous exact identities were

    |S_X|^2 <= (N+H-1)*Q_H/H^2,
    Q_H = H*sum_j a_j^2 + 2*sum_(ell=1)^(H-1)(H-ell)*C_X(ell).

Let `m_v` be the number of original starts visiting reset node v, `K_X=sum_v m_v^2` the collision energy, `F4_X=sum_j a_j^4` the **raw fourth moment**. Let `D_H` be the raw **DISJOINT-path** Fejer correlation

    D_H = sum_(ell=1)^(H-1) (H-ell)
            sum_(j: P_j ∩ P_(j+ell) = empty) a_j*a_(j+ell).

Since each joined pair j<k shares at least one node v, the number of distinct joined pairs of index separation <H is bounded by `(K_X - sum_v m_v)/2 <=K_X/2`. Also each source j participates in at most 2(H-1) such pairs. AM-GM and Cauchy then give an EXACT, nonasymptotic upper bound for their weighted correlation contribution:

    |2*sum_(ell<H)(H-ell)*C_X^join(ell)|
       <= 2*H^(3/2)*sqrt((K_X/2)*F4_X).                 (A4)

Similarly, Cauchy gives `sum_j a_j^2 <=sqrt(N*F4_X)`. Thus

    BOXED: Q_H <= H*sqrt(N*F4_X)
                    + 2*H^(3/2)*sqrt(K_X*F4_X/2)
                    + 2*|D_H|.                             (A5)

**New conditional theorem:** Take any mesoscopic H satisfying `B << H << X` (e.g. H=floor(B^1.5)). If the following three currently OPEN asymptotic estimates hold:

    (i)  F4_X = O(X B^4),
    (ii) K_X = o(X H),
    (iii) |D_H| = o(X B^2 H^2),

then (A5) gives `Q_H=o(X B^2 H^2)` and the Fejer/Cauchy bound gives

    BOXED: S_X=o(X B).                                   (A6)

In particular the empirically plausible **stronger** collision moment `K_X=O(XB)` implies (ii) for H=B^1.5; more flexible `K_X=o(X B^1.5)` already suffices at that H. For fixed H=B the same argument would require the stronger `K_X=o(XB)`. Hence increasing the averaging window is a mathematically useful choice: the joined-path term dies automatically under weak collision-energy and fourth-moment hypotheses, leaving the **nonjoining** two-source arithmetic correlation as the sole signed correlation target. Neither (i), (ii), nor (iii) is proved asymptotically here.

A stronger but more interpretable sufficient form of (iii) is `sum_(ell<H) |C_X^disjoint(ell)| = o(X B^2 H)`; the exact weighted signed criterion (iii) is weaker.

The result is a *reduction of the signed RESET-candidate discrepancy only*. Even establishing A6, one must separately prove enough control of reset frequency and CHARGED high-event run tails for the terminal mean-growth argument and twin primes. The A166944 record conjecture has an additional bridge.

## 4. Full finite GCD audit and moment scales

The new reproducible source `research/reset_shift_pair_audit.cpp` includes the preexisting sibling `research/reset_origin_dispersion_audit.cpp`; both must be in the same directory. It uses exact original parity-specific event-jump wheel and verifies against independent small literal-step GCD, historical event/growth/reset/signed-load regressions, universal root interval A1, every first-reset pair q coincidence exclusion A2, shared/disjoint cross-term exact decomposition, and multiple uncentered Fejer inequalities.

| even X | B | K_X/(XB) | F4_X/(XB^4) | Fejer upper |S_X|/(XB), H=B | Fejer upper, H=floor(B^1.5) |
|---:|---:|---:|---:|---:|---:|
| 4,096 | 170 | 0.07857 | 0.91972 | 0.12323 | 0.05609 (H capped at N) |
| 16,384 | 339 | 0.08567 | 4.67580 | 0.19611 | 0.10711 |
| 65,536 | 678 | 0.08726 | 9.12816 | 0.15165 | 0.02870 |
| 262,144 | 1,355 | 0.08830 | 11.60013 | 0.15358 | 0.02661 |
| 500,000 | 1,871 | 0.06929 | 7.53656 | 0.12120 | 0.01555 |

For X262144 the normalized block-energy test `Q_H/(X B^2 H^2)` fell from 0.046689 at H=B to 0.001026 at H=floor(B^1.5); for X500000 from 0.029160 to 0.000365. The longer-window improvement is finite and does not prove a limit as X→infinity. Moreover, at H≈N the Cauchy window bound becomes close to a restatement of the signed sum itself; the proposed H≈X^(3/4) intentionally remains **sublinear** in X.

At X262144 and shift ell1, source pairs that share a reset account for 41.2% of pairs but ~80.8% of centered correlation; at ell256 they account for 0.673% of pairs and ~17.1% of centered correlation. **Noncoalescing pairs are the dominant unsolved analytic object over moderate shifts.** The two largest q bands make a major contribution to raw correlations; no simple independence of distinct q is established by these data.

The source can optionally write fully enumerated per-start CSV for independent analysis via `--csv=/tmp/A166944_pairs`; the CSV is a diagnostic regenerated by the auditor, not a committed primary artifact. The checked source is the reusable artifact.

### Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/reset_shift_pair_audit.cpp -o /tmp/reset_shift_pair_audit
/tmp/reset_shift_pair_audit 4096 16384 65536 262144 500000
# optional source-level data
/tmp/reset_shift_pair_audit 262144 --csv=/tmp/A166944_pairs
```

No Lean kernel build or main merge. Issue #4 remains OPEN. The genuinely remaining proof conditions are (i)–(iii), and beyond that reset count / charged-run tails; none of those asymptotics has been established.
