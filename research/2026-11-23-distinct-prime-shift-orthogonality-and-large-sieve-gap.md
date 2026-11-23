# A166944: distinct-prime shifted reset correlations, exact CRT zero modes, ambient large-sieve bound, and weighted transport obstruction

**Date:** 2026-11-23 JST. **Project:** `tara-sooo/A166944-Lean`, dedicated branch `research/issue-4-terminal-survivor-positive-budget`, research Issue #4 and parent #1. Continues `2026-11-23-shifted-pair-coalescence-and-mesoscopic-fejer.md`. All new exact identities and inequalities below have **paper proofs** (the additive large sieve is a standard published theorem); finite claims are verified by reproducible C++17 using the **original parity-specific squarefree-clipped GCD**. No Lean kernel compilation, proof of twin-prime infinitude, or original A166944 strict-record theorem has been obtained. Main is untouched.

## 1. Precise source-pair / prime-pair decomposition

Set even `X>=2048`, `B=ceil(sqrt(7X))`, `N=X/2`, and `M_j=X+1+2j`. The actual FULL B-wheel reset graph assigns a path `P_j` of high-prime post-event RESET nodes `v=(t,z)`, `z∈{0,6}`. The source-specific terminal index is `K(M)=floor((7M−1)/4)`. The prior exhaustive 3/5/7/11-only finite-state certificate defines a fixed set of even growth prefixes `E_(r,z)⊂[0,100]` for each `r=t mod L`, `L=2310`. For primes `q∈J_B={103<=q<=B}` define

```
U_(q,r,z)={ inv2_q*(z−e+1), inv2_q*(z−e−1) mod q : e∈E_(r,z) },
u_(r,z)=|U_(q,r,z)|, 2<=u<=31, independent of q>=103,
f_q(v)=q*1{t mod q∈U_(q,r,z)}−u_(r,z),
a_(j,q)=sum_(v∈P_j) f_q(v),
a_j=sum_(q∈J_B) a_(j,q).
```

No sample-mean subtraction is performed. The earlier exact total signed reset-candidate discrepancy is `S_X=Σ_j a_j`.

For source displacement `ell` and **nonjoining pairs** `P_j∩P_(j+ell)=∅`, define raw two-source sums

```
C_dis^=(ell)=sum_(j nonjoining)sum_q a_(j,q)*a_(j+ell,q),
C_dis^neq(ell)=sum_(j nonjoining)sum_(q!=p) a_(j,q)*a_(j+ell,p),
C_dis(ell)=C_dis^=(ell)+C_dis^neq(ell).
```

Thus with Fejer weights `H−ell` we get the **exact** signed decomposition

```
D_H=D_H^=+D_H^neq,
D_H^* = Σ_(1<=ell<H)(H−ell) C_dis^*(ell).
```

The previously established deterministic Fejer/merger argument is

```
Q_H <= H*sqrt(N F4_X) + 2 H^(3/2)*sqrt(K_X*F4_X/2) + 2 D_H,
|S_X|^2 <= (N+H−1)*Q_H/H²,
F4_X=Σ_j a_j^4, K_X=Σ_v m_v².
```

The upper inequality **does not require** `|D_H|`; it uses the signed `D_H`. Consequently the condition `max(D_H,0)=o(XB²H²)` is enough, and is strictly weaker than the earlier `|D_H|=o(XB²H²)`. If `B<<H<<X`, `F4_X=O(XB⁴)`, `K_X=o(XH)`, and `max(D_H,0)=o(XB²H²)`, then `S_X=o(XB)` follows. These asymptotic hypotheses remain OPEN.

## 2. NEW exact distinct-prime CRT orthogonality, and its limitation

Fix two arbitrary low-wheel reset cells `(r,z)` and `(r',z')`, with r,r' in `Z/LZ`, z,z'∈{0,6}, and FIX an integer time difference `delta` satisfying `r+delta≡r' (mod L)`. For each q define `f_(q,r,z)(t)=q1{t modq∈U_(q,r,z)}−u_(r,z)`. For **distinct primes q!=p, q,p>=103**, the elementary Chinese remainder theorem implies

```
BOXED: Σ_(k=0)^(pq−1) f_(q,r,z)(r+Lk)
                          * f_(p,r',z')(r+delta+Lk) = 0.         (M1)
```

Proof: As k traverses a complete modulus pq, the residues `(r+Lk mod q, r+delta+Lk mod p)` traverse every pair of residues exactly once, because gcd(L,pq)=1 and gcd(p,q)=1. Both centered f functions have vanishing residue sum individually. This is TRUE FOR ANY FIXED delta, not only small or random delta. **It does not assert an actual dynamical reset pair uniformly samples those pq classes.**

For **the same prime q=p**, averaging t over one full modulus q yields the exactly different covariance

```
BOXED: (1/q) Σ_(t mod q) f_(q,r,z)(t)*f_(q,r',z')(t+delta)
       = q*|U_(q,r,z) ∩ (U_(q,r',z')−delta)|−u_(r,z)*u_(r',z'). (M2)
```

The universal root enclosure `U⊂inv2_q+[-51,3]` ensures no root intersection when `55<=delta<=q−55`, so in this nonresonant range the RHS is exactly `−u*u'`. In particular **equal-prime and distinct-prime components have different phase benchmarks**. The auditor exhaustively checks M1 at 240 finite full pq CRT periods for prime pairs (103,107), (103,109), (107,109), including both z values and several shifts, and M2 on eight q/shift cases including q211,delta100.

**NEW pointwise same-prime coincidence bound:** If actual two reset origins have `|delta|>54` and they both admit prime q>=103 as a candidate, then `q | (delta−k)` for some |k|<=54. For every threshold Q>=103, the number of such **distinct common primes q>=Q** for ONE fixed pair of reset nodes is at most

```
BOXED:  Σ_(k=-54)^54 floor( log(|delta−k|)/log Q )
      <= 109*log(|delta|+54)/log Q.                          (M3)
```

All `delta−k` are nonzero under |delta|>54; the estimate follows because a nonzero integer n has at most log|n|/log Q distinct factors >=Q. In the canonical window, |delta|=O(X)=O(B²). Thus for Q=B^theta with fixed theta>0, the count is O_theta(1), uniformly even for adaptive histories. M3 does not directly bound the weighted average q² cost of these sparse coincidences.

## 3. Actual adaptive pair-origin cells are sparse

The essential obstacle to naively applying M1 is the count of ACTUAL source pairs with fixed first-reset residue `r=t mod 2310` and fixed first-reset time offset `delta=t'−t`. In **nonjoining** source-index pairs, the resulting histogram is extremely sparse even WITHOUT conditioning on both reset deficit types z,z', prime choices or later history:

| even X | source-index lag ell | first-reset pairs in nonjoining source paths | distinct (r,delta) cells | singleton cell percentage |
|---:|---:|---:|---:|---:|
| 262144 | 32 | 55256 | 35970 | 64.48% |
| 500000 | 32 | 108172 | 67701 | 62.00% |

Finer conditioning on z,z' and the full history makes cells even sparser. A separate unconditional equidistribution statement for each (r,delta,q,p) cell is not a realistic immediate proof goal. Any useful arithmetic saving has to be obtained **after summing across cells, shifts and distinct primes**, without taking absolute values prematurely.

## 4. An UNCONDITIONAL ambient-time second-moment theorem from the additive large sieve

There IS a genuine global arithmetic estimate when **all integer reset times** are counted WITHOUT adaptive visit multiplicities.

For fixed cell r,z, the nonzero Fourier decomposition is

```
f_q(r+Lk)=Σ_(a=1)^(q−1) c_(q,a;r,z) exp(2πi aLk/q),
c_(q,a;r,z)=exp(2πi ar/q) Σ_(u∈U_(q,r,z))exp(−2πi au/q),
Σ_(a=1)^(q−1)|c_(q,a;r,z)|²=q*u_(r,z)−u_(r,z)²<=31q.   (M4)
```

Because multiplying the nonzero numerator a by L permutes the nonzero residues mod q, the different frequencies `aL/q (mod 1)` across all primes q∈J_B are separated by at least 1/B². The **dual additive large sieve** (Selberg–Montgomery–Vaughan) therefore yields, over any interval of `n_r` consecutive admissible k,

```
Σ_k |h_B(r+Lk,z)|² <= (n_r+B²) Σ_(q∈J_B)Σ_(a=1)^(q−1)|c|²
                         <=31 (n_r+B²) Σ_(q∈J_B) q.
```

Summing 2310 residue cells and both values z=0,6 gives the **explicit unconditional bound**, for ANY interval I of consecutive integer reset times,

```
BOXED: Σ_(t∈I) Σ_(z∈{0,6}) |h_B(t,z)|²
       <= 62 (|I|+2310 B²) Σ_(q∈J_B) q.                 (M5)
```

This is valid even at times not visited by canonical trajectories, because h_B(t,z) is defined purely arithmetically for all integer t. If |I|=O(X) and B²≈7X, then, by standard prime-counting bounds `Σ_(q<=B prime)q=O(B²/logB)`, it implies

```
BOXED: Σ_(t∈I,z) |h_B(t,z)|² = O(X B²/log B).           (M6)
```

Reference for the standard large-sieve theorem: Kiran Kedlaya, *An additive large sieve inequality*, Theorem 15.5, https://kskedlaya.org/ant/chap-largesieve.html ; alternatively Emmanuel Kowalski, *Two remarks on the large sieve*, eq. (3), https://people.math.ethz.ch/~kowalski/two-remarks-large-sieve.pdf . M5 is a new direct **application** to our fixed low-wheel candidate functions, not a novel large-sieve theorem.

**Crucial quantitative obstruction.** Let µ_v=m_v be the genuine reset-source multiplicities and `K_X=Σ_v m_v²`, with nodes restricted to an ambient time interval I of length O(X). By Cauchy and M6,

```
|S_X| <= sqrt(K_X * Σ_(t∈I,z)|h_B(t,z)|²)
      = O( sqrt(K_X * X B²/logB) ),
|S_X|/(XB) = O( sqrt(K_X/(X logB)) ).                       (M7)
```

To conclude S_X=o(XB) from M7 alone would require `K_X=o(X logB)`. Empirically `K_X≈0.07−0.09 XB`, MUCH larger than X logB. Thus the ambient large sieve alone cannot close our actual signed discrepancy even with the empirical collision-moment bound. A **transport-weight correlation** estimate is essential.

## 5. Exact Fourier energy of the real reset-transport population

For each `(r,z)` and q, define the actual nonnegative residue weights

```
m_(r,z,q)(b) = Σ_(visited v: r_v=r,z_v=z,t_v≡b mod q) m_v.
```

Orthogonality/Parseval (again exact, no probability) gives

```
Σ_(a=1)^(q−1) |Σ_(visited v in cell r,z) m_v exp(2πi a t_v/q)|²
  = q Σ_(b modq) m_(r,z,q)(b)²
       − (Σ_(b modq)m_(r,z,q)(b))².                        (M8)
```

Write `F_X` for the sum over r,z,q of the RHS and `C_X` for the summed Fourier coefficient energy `Σ_(r,z,q,a)|c_(q,a;r,z)|²`. The exact Fourier representation of S and ordinary Cauchy give `|S_X|<=sqrt(F_X*C_X)`. The latest C++ auditor evaluates both quantities by integer residue histograms and confirms this bound, as well as all historical source-load regressions.

| X | B | F_X/(X² log B) | sqrt(F_X*C_X)/(XB) | ACTUAL |S_X|/(XB) |
|---:|---:|---:|---:|---:|
| 4096 | 170 | 1.104 | 101.36 | 0.01548 |
| 16384 | 339 | 2.732 | 196.14 | 0.09036 |
| 65536 | 678 | 5.110 | 290.54 | 0.00896 |
| 262144 | 1355 | 8.325 | 370.80 | 0.00055 |
| 500000 | 1871 | 8.310 | 372.42 | 0.00752 |

**This is an informative failed attempted proof:** even the exact L² Fourier-energy Cauchy bound is hundreds of times the desired scale XB while the observed signed correction is tiny. Most of the arithmetic cancellation is **between Fourier modes**, not captured by either norm. An argument that bounds all frequencies separately by absolute values would lose the essential sign cancellation.

One independent deterministic structural observation is a forced anchor exclusion: at a RESET node `(t,z)`, for q>=103, if `z=0` and `q|t`, or `z=6` and `q|(t−2)`, q is NOT a candidate in the following low-only prefixes. This extends the last-fired-prime exception and is checked at every visited node. It permits alternative q-conditioned centering, but the finite signed improvement is inconsistent across X (e.g. at X262144 the adjusted |S| INCREASED from 194316 to about 874030), so it has not produced a universal cancellation estimate.

## 6. EXACT all-shift Fejer decomposition by prime diagonal/off-diagonal

For all tested X, the code verifies that at each visited reset node either **all visiting sources** have a next reset before their cutoff, or **none** do (no mixed-cutoff nodes). This is observed, NOT asserted as a universal theorem. Under this verified finite condition, two source paths meet iff they have the same last reset node. Their source indexes can be grouped by that last node, and the Fejer-weighted JOIN contribution computed **exactly in O(N)** using moving prefix sums in each group. The total all-source Fejer correlation is computed from rolling-window squares in O(N). The diagonal SAME-prime part is computed for every q similarly. Subtracting joined terms gives the full DISJOINT Fejer split without quadratic pair enumeration.

All quantities in the following table use `H=floor(B^1.5)`, truncated to N, and are normalized by `X*B²*H²`. They are RAW, not sample-centered; `D_H=D_H^=+D_H^neq`.

| even X | H | signed disjoint SAME q | signed disjoint DISTINCT q!=p | total disjoint D_H | joined contribution |
|---:|---:|---:|---:|---:|---:|
| 16384 | 6241 | −0.0001923 | +0.0047791 | +0.0045869 | +0.0018802 |
| 65536 | 17654 | −0.0000523 | −0.0005409 | −0.0005931 | +0.0011093 |
| 262144 | 49877 | −0.0000846 | −0.0002115 | −0.0002961 | +0.0008019 |
| 500000 | 80930 | −0.0000199 | −0.0002084 | −0.0002284 | +0.0004066 |

Thus the individual lag signs in Section 1 DO NOT describe the long-window sum; at the two largest tested X both signed disjoint contributions are negative. At X16384 the distinct-prime contribution remains positive and dominates the same-prime negative contribution. One therefore CANNOT replace the asymptotic theorem by a universal sign assertion at all finite X. The exact **one-sided** criterion `max(D_H,0)=o(XB²H²)` is more appropriate than bounding |D_H^neq| and |D_H^=| separately.

For individual shifts at X262144, the nonjoining RAW pair correlation per ALL `N−ell` pairs is:

| ell | same q | different q!=p | total |
|---:|---:|---:|---:|
| 1 | +10084.67 | +921.63 | +11006.30 |
| 32 | −1815.14 | +21700.29 | +19885.15 |
| 128 | −8920.24 | +23262.37 | +14342.13 |
| 256 | −8669.90 | +20966.52 | +12296.62 |
| 1155 | −4657.17 | −12485.90 | −17143.08 |

In particular, **distinct primes cannot be treated as numerically negligible** on these genuine adaptive source pairs. A fixed-cell artificially uniform CRT model would give ZERO for q!=p, but the actual reset-pair distribution is far from that model pointwise.

## 7. Next analytic problem, precisely stated

The remaining *new* analytic question is to control the **SIGNED** distinct-prime bilinear dispersion for real disjoint source paths. Schematically, for a fixed source lag ell, each ordered pair of actual reset nodes `(v,w)` from nonjoining paths contributes

```
Σ_(q!=p) f_q(v)*f_p(w).
```

Group those pairs by both low-wheel cell types, by their relative origin shift `delta=t_w−t_v`, and then by the first time origin `t_v` modulo `qp`. In each fixed `(ell,c,c',delta,q,p)` cell, M1 says the uniform-residue mean is exactly zero; hence the contribution is exactly the centered origin-residue *population discrepancy* against this zero-mode kernel. But the actual population may have only one sample per cell. A useful proof has to exploit **cancellation after the Fejer ell-average and q,p-average**, rather than bound every cell separately.

A productive route is a bilinear *dispersion method* on transported reset-populations, using the explicit 55-window root coefficients and working with nonzero mixed Fourier frequencies `a/q+b/p`. Crucially for q!=p these frequencies NEVER vanish modulo one, so there is no mixed-prime constant mode; nonetheless the frequencies can be as close as 1/(pq)≈1/X, which explains why individual incomplete intervals are hard. Large sieve gives an ambient-space mean-square bound M5 but loses approximately a factor B^1/2 at the weighted population stage. We need arithmetic cancellation beyond a global Cauchy inequality.

Even if `S_X=o(XB)` is proved, terminal twin-prime infinitude also requires control of the reset count R_X and of high-deficit CHARGED runs. No Lean compilation, no main merge. Issue #4 remains open.

### Reproduction

```
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/mixed_prime_shift_audit.cpp -o /tmp/mixed_prime_shift_audit
/tmp/mixed_prime_shift_audit 4096 16384 65536 262144 500000
```

The new C++ source includes the existing committed sibling `research/reset_origin_dispersion_audit.cpp` (the latter contains the exact original parity GCD event scanner, low-wheel prefix generator, and independent literal-step check). Strict compilation and all five finite scans passed. Independent validation compared raw all-source shifted correlation means with the previously generated per-source CSV for X65536/262144/500000, agreeing to displayed precision. Full period CRT tests: 240 distinct-prime cases and eight same-prime cases. Every visited reset vertex passed anchor-forbidden-prime and low-wheel width assertions; all verified scans had zero mixed-cutoff reset nodes. Source outcomes: paper-level theorem vs computational corroboration vs open asymptotic question are distinct.
