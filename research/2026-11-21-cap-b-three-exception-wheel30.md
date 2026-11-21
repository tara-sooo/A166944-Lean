# Cap B: a stronger 30-wheel obstruction for three exceptional increment values

Date: 2026-11-21 JST. **Status:** conditional reduction and finite-arithmetic certificate; **not** an unconditional proof of Cap B, and **not yet a Lean kernel proof**.

Reproducible C++17 verifier: [cap_b_three_exception_wheel30.cpp](cap_b_three_exception_wheel30.cpp). This investigation reads directly from the user's 2026-11-21 `workspace.zip`, particularly `mission_scan/twin_proof/cap_bound/AllIndices.lean`, `CapSampleExact.lean`, `WeightReal.lean`, and `slow_backward.md`. The earlier 30-supported barrier in `slow_backward.md` uses the weaker \(\Delta D\le P-2=28\); this note strengthens that bound to **16** for the specific support \(P=30\).

## 1. Exact horizon-only supported transition wheel

For an ordinary first nonunit gcd event, let \(C=D(s)\) denote the horizon just before the event and \(e=d(r)>1\) the actual increment. The recurrence and the first-hit expression imply

\[
e\mid C-1\quad\text{or}\quad e\mid C+1,\qquad C'=C+(e-1).
\]

Every horizon \(C\) is even. If \(e\mid30\) and \(e>1\), then \(e\in\{3,5,15\}\). Define a potential \(U\) on the **15 even residues modulo 30**, as follows:

| \(C\bmod30\) | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 24 | 26 | 28 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| \(U(C)\) | 0 | 10 | 8 | 6 | 4 | 2 | 0 | 16 | 14 | 0 | 10 | 8 | 6 | 4 | 2 |

For every permitted supported transition \(C\mapsto C+(e-1)\) with \(e\in\{3,5,15\}\), the **18 exact allowed edges** all satisfy

\[
\boxed{(e-1)+U(C')\le U(C).} \tag{W}
\]

There is therefore no directed cycle of supported events. Telescoping gives, for **any** consecutive string of increments dividing 30,

\[
\boxed{\sum(e_i-1)\le16.} \tag{W1}
\]

The longest allowed supported string consists of **at most six nonunit events**. The six-event residue path \(14\to16\to20\to22\to24\to28\to0\) spends exactly 16 units of horizon growth. These are valid upper bounds for *all genuine first-hit trajectories*, since (W) only enforces necessary divisibility and is deliberately an overapproximation.

This uniform 16 is stronger than the previously used \(30-2=28\).

## 2. A sharper necessary exception count from absence of a slow interval

The actual Lean file `AllIndices.lean` establishes that, for any ordinary index interval \([i,j]\) with \(i\ge2\), \(D(j)\ge4\),

\[
9(D(j)-D(i))+32+8\lfloor\sqrt{D(j)+1}\rfloor\le4(j-i)
\]

implies that \(D(j)-1,D(j)+1\) are prime. `CapSampleExact.lean` shows that **one such interval** ending in \([M+2,K]\), \(K=\lfloor(7M-1)/4\rfloor\), implies all canonical capped paths obey Cap B.

Set \(s_0=M+2\) and \(R=\lfloor\sqrt{2K+1}\rfloor\). Since the established \(D(j)\le2j\) holds for all \(j\le K\), put

\[
\boxed{L=44+2R.}
\]

If all nonunit increments on an index block \((u,u+L]\) divide 30, (W1) gives \(D(u+L)-D(u)\le16\), and

\[
9\cdot16+32+8R=4L.
\]

That block itself satisfies the slow-interval criterion. **Therefore, in the absence of any slow interval, every disjoint block of length \(L\) within \([s_0,K]\) must contain an actual increment not dividing 30.**

For \(M=45,895,573\),

```text
s0 = 45,895,575
K = 80,317,252
R = 12,674
L = 25,392
K-s0 = 34,421,677 = 1,355 * 25,392 + 15,517
```

Thus **no slow interval forces at least 1,355 exceptional increments**. The earlier 28-unit bound used \(L=25,419\) and gave 1,354. This is a mathematically valid but numerically modest strengthening.

## 3. Same large exceptional value cannot reappear immediately

Suppose two successive *exceptional* values (not necessarily successive nonunit events) are the same odd prime \(p\ge61\). Every intervening nonunit increment divides 30, so its total horizon growth \(h\) is even and \(0\le h\le16\). If the two pre-event horizons are \(C,C_{\rm next}\), then

\[
C_{\rm next}-C=(p-1)+h.
\]

At both endpoints, \(p\mid C\pm1\) and \(p\mid C_{\rm next}\pm1\). Subtracting the appropriate quantities shows that \(p\) divides one of \(h-3,h-1,h+1\). These are nonzero odd integers of absolute value at most 17. Contradiction. **Thus successive exceptional values from \(\{p,q,r\}\subset[61,\infty)\) must differ.**

This generalizes the alternating constraint for two values, but three values no longer force a single alternating order.

## 4. Finite necessary-condition graph for three prime exceptions

Fix a set \(S=\{p,q,r\}\) of **three distinct primes between 61 and 109**, inclusive. Assume that all nonunit increments under consideration either divide 30 or belong to \(S\).

Represent an exceptional hit by the state

\[
(C\bmod 30pqr,\ e\in S),\qquad e\mid C-1\text{ or }e\mid C+1.
\]

From a hit \(e\), the next exceptional hit \(f\ne e\) must have pre-horizon

\[
C_{\rm next}=C+(e-1)+h,
\]

where \(h\) belongs to one of the **supported-only path sums explicitly enumerated from the residue \(C+e-1\bmod30\)** using the 18 edges from §1. We add *all* such transitions whenever \(f\mid C_{\rm next}\pm1\). This finite graph ignores the index \(s\), the full gcd's size and the actual earliest-hit ordering; it is therefore an overapproximation of true recurrence traces.

For all 12 primes between 61 and 109, there are \(\binom{12}{3}=\mathbf{220}\) unordered triples. The companion self-contained C++17 code creates each exact modular graph and performs a topological sort and longest-path dynamic programming. Its finite results are

```text
30-wheel: 15 residues, 18 supported transitions,
          maximum supported growth 16, maximum supported events 6

three-prime triples checked: 220
graphs containing a directed cycle: 0
maximum number of exceptional events on a path: 11
maximal triple: (67,71,73)
```

**Conditional theorem:** For any canonical \(M\ge45,895,573\), if throughout the ordinary index interval \((M+2,K]\) every nonunit increment either divides 30 or equals a member of **one fixed set \(S\) of at most three primes in \([61,109]\)**, then Cap B holds for that \(M\).

Reason: any failure of Cap B would exclude a slow interval and force at least 1,355 exceptions already at the threshold (and no fewer at larger \(M\)); yet the finite graph admits at most **11** exceptional hits, a contradiction. The purely arithmetic estimate for general \(M\) uses \(R\le2\sqrt M\), hence \(L\le44+4\sqrt M\), whereas \(K-(M+2)\) grows as \(3M/4\). This covers all \(M\ge45,895,573\).

This is **not the unrestricted Cap B theorem**, since actual exceptional increments can be composite or arbitrary primes well beyond 109, and four or more distinct exceptional primes have not been covered.

## 5. Why first-hit minimality is still important

If one merely allows an arbitrary even intermediate growth \(0\le h\le28\), instead of using the exact supported wheel, a modular graph of the triple \(\{71,73,109\}\) admits a 21-exception candidate path. But the first transition in one such candidate is

\[
C=846436,\quad e=73,\quad C'=846508,\quad
C_{\rm next}=846532.
\]

The proposed intervening supported growth is \(h=24\). At \(C'\equiv28\pmod{30}\), however, the support potential gives \(U(C')=2\), so **this candidate is impossible even before imposing the full earliest-gcd-hit condition**. The exact wheel is a powerful intermediate sieve between loose horizon-congruence arithmetic and expensive index-by-index gcd verification.

The remaining global proof task is to control **unboundedly many possible exceptional values and arbitrary composite exceptional increments**, or to exploit the actual index/record history to prohibit high-density varied exceptions. The finite alphabet theorem alone does not give a universal event count bound.

## 6. Verification and status

Reproduce with:

```sh
g++ -O3 -std=c++17 -Wall -Wextra \
  research/cap_b_three_exception_wheel30.cpp -o /tmp/cap_b_three_exception_wheel30
/tmp/cap_b_three_exception_wheel30
```

The 220-triple computation and the 11-event maximum were independently run in a local C++17 implementation with the same full residue graph and supported wheel, after verifying the 15-state potential separately. The companion committed code is a standalone implementation of that algorithm; its GitHub content was retrieved and matched after commit. **These are finite computations and paper deductions, not new Lean declarations.** Cap B and twin-prime infinitude remain open.
