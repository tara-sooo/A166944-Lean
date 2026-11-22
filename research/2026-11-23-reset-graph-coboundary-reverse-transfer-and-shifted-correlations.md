# A166944: exact reset-graph coboundary transport, reverse-branch variance dissipation, and a shifted-start cancellation criterion

Date: 2026-11-23 JST. Scope: `tara-sooo/A166944-Lean`, research branch `research/issue-4-terminal-survivor-positive-budget`, Issue #4 (parent Issue #1). Continues `2026-11-23-coalescence-signed-reset-load-and-multiplicity.md` and `2026-11-23-reset-origin-residue-dispersion-and-transport.md`. New inequalities are elementary **paper** proofs; data are finite original parity-specific clipped squarefree GCD audits. No new Lean kernel check, proof of twin-prime infinitude, or strict-record A166944 theorem. Main branch is untouched.

## 1. What the graph alone gives: an exact flow/coboundary identity

Let even X>=2048, B=ceil sqrt(7X), N=X/2, and let the source index j represent the odd M=X+1+2j. Along each actual full B-wheel GCD trajectory, record successive *high-event reset* nodes `v=(t,z)` where z=2t-C is 0 (even clock) or 6 (odd clock) and the clipped increment d contains an odd prime >=13. The next reset state is a deterministic function of (t,z), so the observed reset states form a time-increasing functional directed acyclic graph with successor F(v) where observed. Only the source-dependent cutoff K(M)=floor((7M-1)/4) limits how far a source traverses this graph.

At each observed node v define the exact centered high-prime candidate load from previous research:

    h_B(v) = sum_{103<=q<=B prime} q * 1{t mod q in U_(q,r,z)}
            - pi_[103,B] * u(r,z),   r=t mod 2310,

where U is the union of congruence classes from the low-wheel growth prefixes and u=|U| (2<=u<=31, independent of q>=103). Let m_v count all source visits, b_v count first-reset entries, f_v count actual source traversals v→F(v), and d_v=m_v-f_v count exits at v (some sources can stop at cutoff while others continue).

**EXACT node conservation** (all counts nonnegative):

    m_w = b_w + sum_(v:F(v)=w) f_v.                         (T1)

Define a finite *potential* on the actually observed graph by backward recursion

    Phi(v) = h_B(v) + Phi(F(v)),   Phi(cemetery)=0,        (T2)

where an observed sink has F(v)=cemetery. The graph is acyclic because absolute reset time strictly increases. Thus `h_B(v)=Phi(v)-Phi(F(v))`. Summing (T1), equivalently telescoping every genuine source path, proves

    BOXED: S_X = sum_v m_v h_B(v)
              = sum_v b_v Phi(v) - sum_(v:F(v) exists) d_v Phi(F(v)).   (T3)

Consequently the **rigorous boundary inequality** is

    BOXED: |S_X| <= sum_v b_v |Phi(v)| +
                     sum_(v:F(v) exists) d_v |Phi(F(v))|.              (T4)

This is a true structural transfer of the load from every reset visit to the first entries and source exits. Note that every load on an acyclic finite graph admits such a potential; **T2 alone is not a cancellation theorem**. For example, the artificial load h≡1 gives S_X=sum_v m_v>0 even on a merging graph. To prove the needed `S_X=o(XB)`, arithmetic information about Phi at first-reset injection and cutoff-exit states is essential.

On all tested *canonical* windows (X=2048,4096,8192,16384,32768,65536,125000,199998,262144,400000,500000), every observed vertex either had all its sources continue or none, giving zero mixed-cutoff vertices and zero exit-potential contribution in T3. This is an **observed finite property**, NOT asserted as a universal theorem. To exercise the exit term, a separate **synthetic truncation** of exact X4096 paths (every two out of three source trajectories forcibly stopped at their first reset) produced 190 mixed vertices and the correctly verified nonzero boundary: S=-2608, entry=-10777, exit=-8169, so S=entry−exit. This synthetic run is an algebra test and not a modification of the original recurrence.

## 2. A genuine but limited cancellation inequality from branch merging

Let W_w=sum_(v:F(v)=w) f_v be the incoming flow at a reset target w, and

    hbar(w) = (1/W_w) sum_(v:F(v)=w) f_v h_B(v),   W_w>0.

An exact weighted variance decomposition gives

    BOXED: sum_(v:F(v)=w) f_v h_B(v)^2 - W_w hbar(w)^2
          = sum_(v:F(v)=w) f_v (h_B(v)-hbar(w))^2
          = (1/(2W_w)) sum_(u,v:F(u)=F(v)=w)
                  f_u f_v (h_B(u)-h_B(v))^2 >=0.           (T5)

This is **actual quantified variance dissipation by coalescence**. Repeatedly classifying ancestors k reset edges before a shared target yields the same identity for that k-step conditional average, with true source-path multiplicities and deadline truncation.

| X | one-edge incoming variance *loss* | 4-reset-edges loss | 8-reset-edges loss | max |Phi| |
|---:|---:|---:|---:|---:|
| 16,384 | 11.85% | 14.71% | 17.35% (213 pairs) | 1,977 |
| 65,536 | 10.06% | 24.57% | 25.97% | 5,853 |
| 262,144 | 11.60% | 28.11% | 35.06% | 16,311 |
| 500,000 | 10.54% | 27.52% | 34.85% | 18,403 |

The 16,384 depth-8 number has few pairs and is not a robust asymptotic trend. Variance dissipation does **NOT** bound the signed mean: the constant component of h is invariant under conditional averaging. The one-step correlation of h on consecutive reset edges is close to zero but not negative (~0.045 at X262144). Thus T5 measures mixing of *differences between merging branches*, not proof of global signed arithmetic cancellation.

## 3. An alternative with a rigorous analytic inequality: shifted SOURCE correlations

Let the exact scalar load along the whole trajectory of source M=X+1+2j be

    a_j = sum_(reset nodes visited by M) h_B(v),
    0<=j<N=X/2; S_X=sum_j a_j.

The graph potential T2/T3 computes a_j from its first and exit reset nodes, without summing all internal loads. Zero-extend a_j outside [0,N-1]. For any integer 1<=H<=N define the **uncentered** short-shift quadratic form

    Q_H = sum_(n=0)^(N+H-2) [sum_(k=0)^(H-1) a_(n-k)]^2.

Each a_j occurs in exactly H windows, so Cauchy-Schwarz gives the **exact nonasymptotic Fejer/van der Corput bound**

    BOXED: |S_X|^2 <= (N+H-1)/H^2 * Q_H.                (T6)

A second exact identity expresses Q_H through RAW (not mean-subtracted) two-source correlations:

    Q_H = H*sum_j a_j^2
        +2*sum_(ell=1)^(H-1)(H-ell)
             sum_(j=0)^(N-ell-1) a_j a_(j+ell).          (T7)

Since B=Theta(sqrt X), a sufficient, **OPEN analytic criterion** for the signed reset-candidate discrepancy is

    BOXED: Q_floor(B) = o(X B^4).                        (T8, OPEN)

Then T6 gives `|S_X|=o(XB)`. A stronger but perhaps separable route is `sum_j a_j^2=O(XB^2 polylog B)` and a bound of `o(XB^4)` on the weighted raw two-point term in T7. The autocorrelation here refers to two original canonical starts separated by `2ell`: M and M+2ell. It is not a statement about independent artificial plateau phases. This is a concrete shifted-pair sieve/dispersion target, though still unproved and potentially very difficult.

For any given finite X, the code evaluates T6 directly from a rolling sum in O(N+H) time and compares with the previously verified signed S. **The code deliberately does NOT subtract the sample mean when evaluating Q_H or T6**, because that would assume the unknown cancellation.

| X | B=H | exact van der Corput upper bound / (XB) | observed |S_X|/(XB) | Q_B/(XB^4) |
|---:|---:|---:|---:|---:|
| 4,096 | 170 | 0.123227 | 0.015477 | 0.028055 |
| 16,384 | 339 | 0.196111 | 0.090357 | 0.073871 |
| 65,536 | 678 | 0.151650 | 0.008964 | 0.045064 |
| 262,144 | 1,355 | 0.153576 | 0.000547 | 0.046689 |
| 500,000 | 1,871 | 0.121198 | 0.007520 | 0.029160 |

These finite ratios are not monotone and do not prove T8. Nevertheless the nonasymptotic upper bounds, which require no knowledge of the signed sum S beyond the source loads, are materially below the scale XB in every tested window.

Additional diagnostic: sample-*centered* source-load autocorrelation at lag 1 is approximately 0.68–0.69 at large X; it decays with lag. At X262144, centered correlations are 0.202 at lag32, 0.061 at lag256, 0.032 at lag512, and -0.00045 at lag1155. The corresponding RAW correlations at those lags are 0.202, 0.061, 0.032, -0.00044; for X16384 at lag1155 raw correlation is +0.024 despite the centered value being -0.0019. **Only raw correlations enter the valid T7 criterion.** The decay is empirical, not an equidistribution theorem.

## 4. Implications, limits, and next proof target

Even if T8 is eventually proved, `S_X=o(XB)` controls the SIGNED arithmetic discrepancy of high-prime candidate loads after reset origins; to infer twin-prime infinitude we additionally need a bound on the total reset count R_X (for instance O(X(loglog B)^A) with fixed A) and a separate bound on long CHARGED high-event runs. These were already open in the predecessor notes. Candidate *activations* are an overcount of events, and proving their signed discrepancy alone cannot control the whole dynamic event count. In fact each reset can be followed by **at most one first subsequent high event** before the next reset; the arithmetic candidate bound is not itself a geometric bound on the number of reset epochs. Thus the graph analysis is useful for the arithmetic distribution subproblem, not sufficient to close the global twin-prime argument.

A focused potential next attack is to use arithmetic of **paired original starts** (M,M+2ell) to bound the weighted two-source correlations T7 on average over 1<=ell<B. Their first low-wheel states have explicit CRT descriptions, while later deep reset histories merge according to the graph. Another, complementary goal is bounding the distribution of the first-reset injection potential Phi(v_first) after transporting/merging without assuming a uniform distribution of v. The previous per-prime absolute discrepancy goal is stronger than needed; the new Fejer criterion aggregates the actual signed arithmetic load from the outset.

No Lean build or main branch change. Issue #4 stays open. The finite exhaustions, all equations and counterexamples are reproducible from the code below.

## 5. Reproduction and independent checks

The new source `research/reset_graph_coboundary_audit.cpp` includes the **existing sibling** `research/reset_origin_dispersion_audit.cpp`; both must be available (the sibling is already committed in this research branch). Compile and run:

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/reset_graph_coboundary_audit.cpp -o /tmp/reset_graph_coboundary_audit
/tmp/reset_graph_coboundary_audit 4096 16384 65536 262144 500000
```

The verifier checks the original literal-step parity-GCD against independent event-jump clocks on odd M=7..119, historical X-window event/growth/reset/signed-load regressions, exact source and node flow conservation, strictly increasing graph times, T3/T4 arithmetic, individual source-path telescoping, Jensen T5 and k-step conditional averages, and T6 for several H including H=B. The X4096 synthetic-cutoff test verifies a nonzero exit term. Additional all-start windows X=2048,8192,32768,125000,199998,400000 were run with the new code. No asymptotic estimates have been numerically extrapolated as theorems.
