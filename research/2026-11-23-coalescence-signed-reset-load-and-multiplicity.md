# A166944 squarefree wheel: merged reset states, multiplicity bias, and the signed scalar prime-load observable

Date: 2026-11-23 JST. Research Issue #4, parent #1, branch `research/issue-4-terminal-survivor-positive-budget`. Continues `2026-11-23-reset-origin-residue-dispersion-and-transport.md`. The algebra below comprises **paper identities**, not Lean-kernel proofs. The numerical checks are **finite exhaustive original parity-specific clipped squarefree GCD scans**, not asymptotic equidistribution, twin-prime infinitude, or the original A166944 strict-record theorem.

## 1. Exact passage from separate prime discrepancies to ONE signed scalar observable

As in the preceding note, even X>=256, B=ceil(sqrt(7X)), L=2310, I_X={odd M in [X,2X)}. A high-event RESET node v=(t,z), z in {0,6}, corresponds to post-event even state C=2t-z. The low-only {3,5,7,11} restricted continuation from v has finite set E_(r,z) of growth prefixes e, with r=t mod L and e<=100. For all primes q>=103, its q-activation residue set is

    U_(q,r,z) = { inv2_q*(z-e+1), inv2_q*(z-e-1) (mod q): e in E_(r,z) }

and its distinct cardinality u_(r,z) lies between 2 and 31 and is independent of q. This uses the previous finite 4620-case reset-manifold certificate. The candidate condition is a **possible q activation at some low-only plateau**, not a guarantee q fires at the next event; actual cutoff is overcounted.

Let V_X be the set of distinct reset nodes visited by canonical M, m_v the number of visits to v (different M). Define J_B={prime q:103<=q<=B}, J=#J_B, and

    F_B(v) = sum_(q in J_B) q * 1{t_v mod q in U_(q,r_v,z_v)},
    h_B(v) = F_B(v) - J*u_(r_v,z_v),
    R_X = sum_(v in V_X) m_v,
    A_q = sum_v m_v * 1{t_v mod q in U_(q,r_v,z_v)}.

All three F_B,h_B,m_v are exact arithmetic objects; h_B(v) is an **integer**, even though the individual per-prime phase mean u/q is fractional. Changing order of the finite sums proves the strong exact identity

    BOXED: sum_(q in J_B) q*A_q = J * sum_v m_v*u_v + S_X,
    S_X := sum_v m_v*h_B(v).                               (C1)

The preceding note used the stronger unsigned discrepancy `D_X=sum_q q|A_q-E_q|`, bounding `|S_X|<=D_X`. For controlling the **total weighted prime-activation budget**, only the ONE **signed scalar** S_X is required. Separate equidistribution of every prime q is unnecessary. This does NOT by itself control charged (non-reset) high-prime excursions.

### A sufficient conditional target

If, along an unbounded even-X sequence,

    R_X = O(X*(loglog B)^A) for a fixed A,           (OPEN R)
    |S_X| = o(XB),                                  (OPEN signed CRT)

then J=O(B/log B) and u_v<=31 yield

    sum_(q>=103) q*A_q
      <=31*pi(B)*R_X + |S_X|
      =O(XB*(loglog B)^A/log B)+o(XB)=o(XB).

This bounds the **first subsequent high q-candidate after each reset** in aggregate weighted mass. The finitely many q<103 contribute at most a fixed multiple of R_X, which is also o(XB). A charged-run tail theorem remains additionally necessary to obtain the full W_X=o(X²) criterion; neither conditional assumption is proved. In fact R_X=o(XB) already trivially handles the *number* of reset events; signed CRT gives more precise control of prime weights.

## 2. Exact support-versus-multiplicity decomposition

Let V=|V_X| and mean multiplicity mbar=R_X/V. With the same scalar h_B,

    BOXED: S_X = mbar * sum_(v in V_X) h_B(v)
                + sum_(v in V_X) (m_v-mbar)*h_B(v).       (C2)

The first term measures the prime-load bias of the DISTINCT occupied node set (all nodes counted once); the second measures the arithmetic covariance of the deterministic node load with the number of ancestral canonical starts that reach it. No stochastic model enters (C2).

For comparison with the preceding per-prime absolute discrepancy, define for each q

    f_q(v) = 1{t_v mod q in U_(q,r,z)} - u_v/q.

Then the stronger per-q identity

    A_q-E_q = mbar * sum_v f_q(v) + sum_v (m_v-mbar)*f_q(v)

is exact. By the triangle inequality, the full absolute q-wise discrepancy is bounded by the sum of the **support** and **multiplicity covariance** absolute q-wise errors, but there can be cancellation between the latter two at each q. The new scalar (C1) also permits cancellation ACROSS q, and empirically this is substantial.

## 3. Exact deadline-filtered deterministic transport (paper)

The reset-to-next-reset map F_B(t,z) is deterministic as soon as B and (t,z) are fixed (C=2t-z), ignoring the source-specific terminal cutoff. Along its domain the node time strictly increases. Let J_v(M)=1 if the FIRST high reset reached from canonical start M is node v, and f_v(M)=1 if M visits v. Since the terminal K(M)=floor((7M-1)/4), reaching the next node w at time t_w requires

    K(M)>=t_w  iff  M >= ceil((4*t_w+1)/7).               (C3)

This is a single SUFFIX condition in the source coordinate M. For every actually reachable node w,

    BOXED: f_w(M)=J_w(M)+ 1{M>=ceil((4*t_w+1)/7)}
                        * sum_(v:F_B(v)=w) f_v(M).       (C4)

The sum on the right is at most 1 for a given M, because each canonical start has one deterministic chain. Summing f_w(M) over M yields the exact reset multiplicity/occupancy transport. In this representation, **all past high-prime products disappear from the forward state**; their impact is retained in the injection J_w(M) and in the population weights m_v. Merging many histories may amplify an arithmetic bias of a node, so coalescence itself is NOT an equidistribution theorem.

## 4. Full finite audit: actual support distribution versus visits

Source `research/reset_scalar_transport_audit.cpp` includes the previously committed exact `research/reset_origin_dispersion_audit.cpp` and extends it with independent node support, multiplicity, scalar divisor load, directed successor, and complete source-by-source path bookkeeping. It builds with `g++ -std=c++17 -O3 -Wall -Wextra -Werror` and runs all odd canonical starts in each window; independent literal-step parity GCD M7..119 and stored full-event/high-event/reset/growth regressions pass. All node-wise, source-wise and q-wise versions of (C1)/(C2) agree exactly to arithmetic precision. The special `#pragma GCC diagnostic` in the source suppresses the unused return-value warning caused by renaming the prior standalone `main` during inclusion.

| X | total reset visits R | distinct nodes V | top 1% nodes' share of visits | q-wise absolute discrepancy / phase (nodes unweighted) | q-wise absolute discrepancy / phase (visits weighted) | SIGNED S / phase |
|--:|--:|--:|--:|--:|--:|--:|
| 4,096 | 2,865 | 466 | 8.17% | 12.83% | 19.09% | -4.50% |
| 16,384 | 14,422 | 1,912 | 13.08% | 8.61% | 17.66% | -12.32% |
| 65,536 | 73,941 | 7,771 | 15.75% | 5.42% | 15.96% | -0.86% |
| 262,144 | 360,413 | 31,510 | 20.26% | 3.23% | 9.90% | +0.044% |
| 500,000 | 705,758 | 60,504 | 19.88% | 2.97% | 10.40% | -0.592% |

The discrete reset SUPPORT set is more phase-like than the weighted VISIT multiset at these scales, while source coalescence concentrates visits: at X262144, the top 1% most visited states carry 20.26% of all visits. The exact multiplicity term in (C2) and its per-q version is therefore a necessary part of the analysis. At X262144, the absolute per-q q-weighted support term was 3.32% of the weighted phase benchmark, the multiplicity-covariance term 9.42%, and their actual combined q-wise error 9.90%. There is no justified assumption that all m_v are constant or independent of residue classes.

### Signed cancellation is far stronger than the q-wise absolute error

At X262144, summing q FIRST inside each actual node gives

    weighted candidate sum = 443,142,225,
    exact phase mean       = 442,947,909,
    signed scalar S_X     = +194,316,
    sum_v m_v*|h_B(v)|  = 259,845,732,
    sum_M |sum_(v on M path) h_B(v)| = 130,655,520.

Thus `|S|/phase=0.0439%`, much smaller than the per-q absolute discrepancy of 9.90%. The amount `sum_v m_v|h(v)|` is ~58.66% of phase, hence pointwise node loads are NOT generally small. Summing along each individual M path reduces this absolute total by about half, while across-start signed cancellation reduces the rest to 0.149% of the summed source-path absolute values. At X500000 the signed ratio was -0.592%, with 10.40% q-wise absolute discrepancy. The signed error is not monotonically small at all finite X: at X16384 it was -12.32%.

### Shape of the merged graph and a weak direction for local telescoping

For X262144, 22,768 observed distinct reset nodes have a known next-reset successor, 5,310 target nodes have more than one distinct predecessor, and the largest observed indegree is 19. At X500000 those figures were 44,284 / 10,313 / 23. The weighted **adjacent-edge** correlation of the centered scalar load h between predecessor and successor is only +0.045 and +0.037 at the two sizes, not an observed strong negative correlation. Therefore a simple one-step alternating-sign/telescoping conjecture is not supported. The observed strong signed cancellation is principally a population-level/global path effect.

The multiplicity collision energy `sum_v m_v^2` at X262144 is 31,363,015, much larger than `R^2/V=4,122,422` from uniform weights. Its effective state support `R^2/(sum m_v^2)` is about 4,142, versus 31,510 distinct states. A direct, generic large-sieve bound using this L² energy would be very wasteful at these sizes. Arithmetic information about the dependence of m_v and h_B(v) is the essential new ingredient.

## 5. What to prove next

The previous research demanded a strong bound on

    D_X = sum_q q*|A_q-E_q|.

The renewal-weight budget actually depends only on the **strictly weaker signed scalar discrepancy**

    |S_X| = |sum_v m_v*h_B(v)|.                           (OPEN)

Its exact division into support and multiplicity terms (C2) highlights two possible arithmetic approaches:

1. Quantify the distribution of the distinct occupied reset times t in fixed residue classes modulo 2310 against the fixed root patterns U_(q,r,z), using ordinary CRT/large-sieve ideas.
2. Establish **transported-weight decorrelation** between m_v, generated by the deterministic forward reset graph and the source deadline threshold (C4), and the centered prime-divisor observable h_B(v). Rather than bounding all q separately or forcing the individual state loads to be small, target the signed *global* sum. A bilinear/second-moment estimate on the first-reset injection and deterministic transport could supply this, but NO such estimate is currently proved.

Even a successful signed reset-origin lemma plus a bound on R_X leaves the earlier CHARGED high-event excursion tails unresolved. Both parts are needed for the original twin-prime sufficient condition W_X=o(X²), and the A166944 strict-record conjecture has its separate bridge problem. There is no Lean kernel theorem or main-branch change in this work.

## Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/reset_scalar_transport_audit.cpp -o /tmp/reset_scalar_transport_audit
/tmp/reset_scalar_transport_audit 4096 16384 65536 262144 500000
```
