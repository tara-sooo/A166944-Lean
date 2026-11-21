# Cap B: short/long selective growth, exact first-hit factor sieve, and shared-divisor cooldown

2026-11-21 JST. **Status:** new paper deductions from the genuine gcd formulas and existing Lean results, and finite arithmetic audits. **Not a proof of the universal \(H\) bound, Cap B, or twin-prime infinitude; no new Lean kernel build.**

Executable Python 3 stdlib verifier: [`cap_b_H_factor_cooldown.py`](cap_b_H_factor_cooldown.py). Based on the user's actual `workspace.zip` files `mission_scan/twin_proof/cap_bound/AllIndices.lean`, `WeightReal.lean`, `slow_backward.md`, and the repository's `A166944/RebalancedCrossingGrowth210.lean`, `A166944/ReplayOffset210.lean`.

## 1. The existing H gate, and two distinct kinds of H expense

At a genuine moving-horizon first hit, let \(s<C=D(s)\), \(r>s\), \(g=r-s\), \(e=d(r)>1\), \(C'=C+e-1\). The event is in the selective-growth count iff

\[
e-1<3(g+1).
\]

Let \(H=\sum(e-1)\) over just these events, and split \(H=H_{\rm short}+H_{\rm long}\) by \(g\le10\) versus \(g>10\). The existing kernel-checked classification `large_relative_gap_cases` in `A166944/RebalancedCrossingGrowth210.lean` gives:

* **Short events:** \(g\le10\), \(e\le33\), so \(e-1\le32\).
* **Long events:** \(g>10\), \(e=p\) prime, with \(p(p-4)<6(C+1)\).

For a canonical first-hit path from \((M+2,2M-2)\), the existing trace bound in `ReplayOffset210.lean` yields

\[
3X_f+G\le13H+24,\qquad X_f=2s_f-C_f,\quad G=C_f-(2M-2).
\]

Substituting \(G=2T+6-X_f\), \(T=s_f-(M+2)\), and \(X_f\ge0\) gives \(4T\le26H+36\). Therefore

\[
\boxed{26H\le3M-45\implies 4s_f\le7M-1.} \tag{A}
\]

This is an H-only sufficient condition; **the upper bound on H is not yet proved.**

## 2. An exact earliest-hit formula from prime factors

For fixed even \(C\) and \(s<C\), a nonunit gcd at even \(r\) is possible exactly when some odd prime \(p\mid C-1\) divides \(r\), i.e. \(r\equiv0\bmod2p\). A nonunit gcd at odd \(r\) is possible exactly when an odd prime \(q\mid C+1\) divides \(r-2\), i.e. \(r\equiv q+2\bmod2q\).

Consequently the true next event index is **the least index \(r>s\)** among the first eligible terms of these finitely many progressions that do not exceed \(C\). The actual increment at this index is the **full** corresponding gcd, which may be composite. If no progression hits before \(C\), the moving horizon is quiet. The companion verifier uses complete trial division to factor \(C\pm1\), computes these exact first progressions, and cross-checks each listed nonunit event by the ordinary gcd formula at every intervening index. This is not a heuristic sieve; it is an exact reformulation.

A first gap \(g>2y\) forces \(q\nmid C-1\) and \(q\nmid C+1\) for **every odd prime \(q\le y\)**, since such a factor would force a first hit by distance \(2q\). In particular:

\[
g>10\implies C\bmod30\in\{0,12,18\},
\]

and

\[
g>14\implies \gcd(C-1,210)=\gcd(C+1,210)=1.
\]

In the latter case \(C\) is in exactly **15** of the 105 even residue classes modulo 210. More generally the fraction of admissible even horizon residue classes modulo \(2\prod_{3\le q\le y}q\) is precisely \(\prod_{3\le q\le y}(1-2/q)\). Counting such classes alone is not enough to bound visits by the **dynamically selected** horizons.

## 3. New composite-divisor and phase-sensitive return cost

Let \(i<j\) be ANY two nonunit events (not necessarily successive), whose increments \(e_i,e_j\) share an odd divisor \(q\ge5\), not necessarily prime. Let

\[
H_{ij}^{\rm between}=\sum_{i<k<j}(e_k-1)
\]

be the *total* intervening horizon growth, **not** the selective H above. Let \(\sigma_i=1\) for an even hit and \(\sigma_i=-1\) for an odd hit, and similarly \(\sigma_j\). By exact gcd divisibility, \(C_i\equiv\sigma_i\pmod q\) and \(C_j\equiv\sigma_j\pmod q\). Since \(q\mid e_i\),

\[
C_j-C_i=(e_i-1)+H_{ij}^{\rm between}
\quad\implies\quad
H_{ij}^{\rm between}\equiv1+\sigma_j-\sigma_i\pmod q.
\]

The intervening growth is even. For odd \(q\ge5\), the least nonnegative even numbers in the three residue classes \(-1,1,3\bmod q\) are \(q-1,q+1,q+3\). Thus

\[
\boxed{
H_{ij}^{\rm between}\ge q+1+\sigma_j-\sigma_i\ge q-1.
} \tag{B}
\]

This extends the earlier *prime-only* repeat-spacing lemma to composite gcd divisors (e.g. two increments divisible by 9 force at least 8 units of intervening growth), with a **phase-sensitive** improvement.

Immediate structural corollaries:

1. For **successive events** \(i,i+1\), \(\gcd(e_i,e_{i+1})\in\{1,3\}\). If their gcd is 3, the first hit is odd, the second even, the **second gap is exactly 1**, and a third consecutive event divisible by 3 is impossible.
2. For **three successive events**, \(\boxed{\gcd(e_i,e_{i+2})\le e_{i+1}}\). Indeed if their gcd \(q\ge5\), the middle event alone must supply \(e_{i+1}-1\ge q-1\).
3. Fix ANY odd divisor \(q\ge5\), and suppose it divides the increments at \(k\ge2\) event indices. Their disjoint intervening-growth windows satisfy, on summing (B), \(\sum H_{\rm between}\ge(k-1)(q+1)+\sigma_{\rm last}-\sigma_{\rm first}\). Their own \(k\) increments contribute at least \(k(q-1)\) to total growth G. Therefore

\[
\boxed{G\ge(2k-1)q-3.} \tag{C}
\]

This improves the earlier \(G\ge(2k-1)(p-1)\) for repeated prime \(p\) when \(k\ge3\), and works for composite \(q\) too. It uses **only exact divisibility and parity**, not a finite numerical search.

## 4. Quantitative two-class obstruction to the first Cap B crossing

At the official threshold \(M=45,895,573\), \(K=80,317,252\). The previously derived first-crossing bound says a capped first step crossing K needs **\(H\ge5,291,742\)** on its prefix (before the crossing event). This follows from \(2T+2X\le13H+18\), \(X\ge0\), and the square-gap bound \(g\le\lfloor\sqrt{4(C+1)}\rfloor\le25,348\) at the predecessor since \(C=D(s)\le2K\).

For any **long** event in that prefix, \(p(p-4)<6(C+1)\le6(2K+1)=963,807,030\). An odd prime satisfying this has \(p\le31,039\). For any short event \(e-1\le32\). If \(S\) and \(L\) are the *numbers of selective H-events* of short and long kind in the prefix, then

\[
\boxed{32S+31,038L\ge5,291,742}.\tag{D}
\]

Examples of the necessary trade-off:

* \(L=0\): at least **165,367** short H-events.
* \(S=0\): at least **171** long prime H-events.
* As a clean disjunction, **either \(S\ge1,000\), or \(L\ge170\)**.
* Equivalently another disjunction: **either \(S\ge50,000\), or \(L\ge119\)**.

For general records \(M\), with \(K=\lfloor(7M-1)/4\rfloor\), the corresponding universal paper upper bound per long-event increment is \(e-1\le1+\lfloor\sqrt{12K+10}\rfloor\). A sufficient **event-count** alternative to (A) is

\[
26\left(32S+[1+\lfloor\sqrt{12K+10}\rfloor]L\right)
\le3M-45
\quad\Longrightarrow\quad \text{Cap B},
\]

when S,L count all relevant selective H-events on that capped path. **This needed count bound is not established.**

## 5. Direct recurrence checks: H is small but long primes can dominate

The companion Python script computes the **actual** A166944 recurrence from n=3 through n=2,860,773, locating 18 attained canonical records \(7\le M\le2,860,771\), and replays each using the exact next-hit factorization formula. It additionally checks the published threshold's 37 certified first-hit events and a 26-event local replay from the separately certified larger record shape \(M=5,875,882,249\). Its pairwise shared-gcd phase checks all pass.

| Record M | Events | H short | H long | H total | G total |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 355,723 | 57 | 138 | 1,716 | 1,854 | 2,388 |
| 1,427,749 | 72 | 188 | 3,950 | 4,138 | 5,274 |
| 2,860,771 | 85 | 272 | 2,070 | 2,342 | 3,912 |
| 45,895,573 | 37 | 72 | 694 | 766 | 1,914 |
| 5,875,882,249 | 26 | 72 | 30,298 | 30,370 | 30,564 |

A single long event \(g=45,145,e=30,097\) in the largest record example accounts for 30,096 of its long H, but **increases** the offset X by \(2g-(e-1)=60,194\). Thus the aggregate H-count weights both helpful offset increases and low-offset resets; proving a small H/M bound is a strong condition. The local replay proves the event arithmetic; full historical certification of the larger two records is separately part of the existing project.

## 6. A precise failure mode of a finite mod-210-only H proof

The verifier exhibits a **25-event fake cycle** in the modulus-210 first-clipped-gcd model. Starting at \((s,C)=(147,192)\), it reaches \((357,402)\), with \(T=G=210\), increasing \(X\) from 102 to 312. At every step, the candidate satisfies \(r\le C\), \(g\le10\), the selective-H condition, and the full **mod-210 clipped** first-hit constraints at all earlier indices. Thus modulo 210 plus \(X\ge0\) cannot alone bound the number of short-H events.

The cycle is **not a real gcd trajectory**: its second and third events have \(e=13\) consecutively, violating (B) with \(q=13\) and \(H_{\rm between}=0\). This precisely demonstrates why additional prime-factor divisibility and cross-event cooldown must be represented. The full prime-factor modulus for all odd e<=33 is \(2\,\mathrm{lcm}(3,5,\ldots,33)=9,025,222,055,850\), which is too large for a naive finite-state expansion.

## 7. Remaining proof gap

The reductions (B)–(D) give an exact obstruction and a feasible target for future computational/Lean work, but **neither bounds S or L over all authentic large canonical records**. Events with arbitrarily many distinct long primes, and many short events whose increments vary, are not globally controlled. The finite checks do not prove an asymptotic estimate. In particular (A) is still a sufficient, not yet established, bound. Further work needs a quantified *multi-prime* packing or anti-return theorem (using the entire gcd factor phases and authentic record history), not another bound derived solely from mod-210 cycle-free potential.

Reproduce:

```sh
python3 research/cap_b_H_factor_cooldown.py
```
