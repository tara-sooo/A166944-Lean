# Cap B: overlap among large-prime positive-debt reuse windows

Date: 2026-11-21 JST. **Status: two finite-arithmetic overlap subcases excluded, NOT Cap B; no new Lean kernel proof.**

Reproduction source: [cap_b_overlap_finite_check.cpp](cap_b_overlap_finite_check.cpp), GNU C++17, no dependencies beyond the compiler. The preceding [mod-210 positive prime-debt potential](2026-11-21-prime-debt-mod210.md) and its [Python certificate](cap_b_prime_debt_210.py) define the debt and verify \(0\le V\le29\). The present work uses the actual first-hit event arithmetic but does not certify the remaining infinitely many mixed multi-window configurations.

## 1. Definitions and prerequisite arithmetic

A moving-horizon first-hit event is \((s,C)\to(r,C')\), with \(g=r-s\), \(e=d(r)\), \(C'=C+e-1\). For **prime \(p=e\ge61\)** let

\[
b=\max(0,\;g-(p-1)+V(r,C')-V(s,C)).
\]

We only count **positive** debts \(b>0\). The mod-210 certificate and first-hit minimality imply that a positive-debt prime event \(p\ge43\) can occur only when

\[
\gcd(C-1,210)=\gcd(C+1,210)=1.
\]

Proof: if a factor \(3,5,7\) divided \(C\pm1\), the first clipped hit would occur by distance 14. A genuine prime \(p\ge43\) event must then occur strictly before that clipped hit, hence \(g\le13\). But \(b\le\max(0,13-(p-1)+29)=0\), contradiction.

Call such \(C\) *inert*. Since \(C\) is even, its residue modulo 210 belongs to precisely

\[
\{0,12,18,30,42,60,72,102,108,138,150,168,180,192,198\}.
\]

Thus \(C\equiv0\pmod6\), and \(y=C/6\pmod{35}\) belongs to the 15-element set

\[
Y=\{0,2,3,5,7,10,12,17,18,23,25,28,30,32,33\}.
\]

Also \(p\mid C-1\) at an even hit, or \(p\mid C+1\) at an odd hit, so \(y\bmod p\) lies in **two** residue classes, \(y=\pm 6^{-1}\pmod p\) (since \(p\ge61\) is coprime to 6).

It follows by the pigeonhole principle that, for any three ordered positive-debt occurrences of the **same** \(p\), at pre-event horizons \(C_1<C_2<C_3\),

\[
\boxed{C_3-C_1\ge6p.} \tag{1}
\]

Furthermore \(V_{\rm before}=0\), \(V_{\rm after}\le29\) and \(g\le2p\), hence

\[
\boxed{b\le p+30.} \tag{2}
\]

Pair the later two positive-debt occurrences, and define the request

\[
I_p=[C_1,C_3),\qquad w_p=b_2+b_3\le2(p+30).
\]

From (1), \(w_p\le(1/3+10/p)|I_p|\le(91/183)|I_p|\) for \(p\ge61\). Requests of the same \(p\) are formed as \([C_1,C_3),[C_3,C_5),\ldots\): half-open, with no overlap within their own key. If the aggregate overlap multiplicity is at most two, then their **total demand** is at most \((182/183)\) times the aggregate horizon width. Triple-or-higher overlaps are the remaining issue.

## 2. Theorem candidate resolved by finite arithmetic: one request per distinct prime

**Statement:** Let \(p_1,\ldots,p_k\ge61\) be pairwise distinct primes, with exactly **one paired request** selected for each \(p_i\), witnessed by three positive-debt occurrences. Put \(A=\min_i C_{i,1}\), \(B=\max_i C_{i,3}\). Then

\[
\boxed{\sum_{i=1}^k(b_{i,2}+b_{i,3})\le B-A.} \tag{3}
\]

This bound allows *arbitrary overlap* of these \(k\) requests; it requires their occurrences to belong to the **same authentic event path**.

Paper cases, using (1)-(2) and horizon increments:

- \(k=1\): \(B-A\ge6p\ge2(p+30)\).
- \(k=2\): if \(P=\max(p_1,p_2)\), then \(B-A\ge6P\ge2(p_1+p_2)+120\).
- \(k\ge8\): all selected \(3k\) prime events have different pre-horizons. Inside \([A,B)\), all but at most the single event at \(B\) contribute their own \(p_i-1\) to horizon growth. With \(P=\max_i p_i\), this yields
  \[
  B-A\ge3\sum_i(p_i-1)-(P-1).
  \]
  This is at least \(2\sum_i(p_i+30)\) whenever \(\sum_{p_i<P}p_i\ge63k-1\). For eight distinct primes \(\ge61\), the seven smallest other primes sum to \(61+67+71+73+79+83+89=523\ge503\); adding larger distinct primes preserves the inequality.
- \(3\le k\le7\): a deficit would require **both**
  \[
  \sum_{p_i<P}p_i<63k-1,\qquad6P<2\sum_i p_i+60k.
  \]
  In particular \(P< (93k-2)/2\), so \(P\le317\) for these prime cases. These inequalities leave exactly **3,448 distinct sorted prime tuples**, classified by \(k\) as \(303,1215,1347,540,43\).

The supplied finite verifier exhausts these tuples. For each it sets \(W=\lfloor(D-1)/6\rfloor\), where \(D=2\sum_i(p_i+30)\), and searches all orderings of the \(3k\) required prime events with pre-horizons normalized to \(0\le y\le W\). It imposes:

1. a shared inert shift \(y+C_0/6\bmod35\in Y\);
2. per-prime residues \(6y\bmod p\) compatible with \(C\equiv\pm1\pmod p\);
3. for each same-prime triple \(y_3-y_1\ge p\);
4. after a selected \(p\)-increment, the next selected event's pre-horizon must have advanced by at least \(p-1\), i.e. by \(\lceil(p-1)/6\rceil\) in scaled coordinates.

The search *overapproximates* true gcd first-hit paths (it does **not** impose the exact index \(s\) or \(g\)). Therefore, rejecting every candidate in this larger class suffices for (3), conditional on the finite program being correctly implemented. The program reports **zero feasible tuples and zero unfinished searches**. This is a computer-checked finite arithmetic reduction, **not yet a Lean kernel theorem**.

## 3. A repeated-key minimal component also ruled out

Now select **two adjacent requests** for prime \(p\ge61\), witnessed by **five** ordered positive-debt \(p\)-events; also select **one request each** for two other distinct primes \(q,r\ge61\). The total selected demand is at most

\[
D=4(p+30)+2(q+30)+2(r+30).
\]

The two \(p\)-windows force \(C_{p,5}-C_{p,1}\ge12p\); the other windows force spans \(\ge6q,\ge6r\). Among the eleven selected events, all except possibly the latest contribute increments to the overall horizon width, which is therefore at least

\[
5(p-1)+3(q-1)+3(r-1)-(\max(p,q,r)-1).
\]

A deficit must violate both lower bounds. These restrictions imply \(\max(p,q,r)<310\), leaving exactly **2,184 candidate prime triples**, with \(q<r\). The same finite verifier searches five-event placements for \(p\), three for \(q\), three for \(r\), and enforces inert residues at **all eleven** events. **All 2,184 cases are excluded**, without an unfinished branch.

This eliminates one minimal pattern with a repeated prime key. **It does not eliminate multiple windows for several keys, nor more than two windows on one key.**

## 4. Reproduction

From the repository root:

```sh
g++ -O3 -Wall -Wextra -std=c++17 research/cap_b_overlap_finite_check.cpp -o /tmp/cap_b_overlap_check
/tmp/cap_b_overlap_check
```

Expected key output (wall time varies):

```text
single k=3 candidates=303 possible=0 unfinished=0
single k=4 candidates=1215 possible=0 unfinished=0
single k=5 candidates=1347 possible=0 unfinished=0
single k=6 candidates=540 possible=0 unfinished=0
single k=7 candidates=43 possible=0 unfinished=0
repeat(2,1,1) candidates=2184 possible=0 unfinished=0
PASS: all 5632 arithmetic candidates excluded
```

The executable returns nonzero if the candidate counts disagree, a feasible configuration is found, or a bounded search reaches its node cap. Local GNU C++17 validation: exit 0, no warnings with `-Wall -Wextra -pedantic`, approximately 5 seconds. The exact source was committed and read back from GitHub. The deterministic search is still a **finite computational certificate**, not a formal Lean proof.

## 5. All repeat counts for at most four distinct prime keys: a long-window bound

The inert-residue restriction provides an elementary **uniform bound for arbitrarily many repeated windows**, when the number of *distinct* participating primes is at most four.

For a fixed prime \(p\ge61\), a positive-debt event's pre-horizon \(C\) satisfies both \(C\bmod210\in\mathrm{inert}\) (15 residues) and \(C\bmod p\in\{-1,+1\}\) (two residues). Because \(\gcd(210,p)=1\), CRT gives **exactly 30 residue classes modulo \(210p\)**. Thus for any half-open horizon interval \(J=[A,B)\) of length \(L=B-A\), the number \(N_p(J)\) of candidate pre-horizons is bounded by

\[
N_p(J)\le\frac{30L}{210p}+30=\frac{L}{7p}+30. \tag{D1}
\]

Select *any number* \(m_p\) of adjacent paired requests for that key \(p\), using \(2m_p+1\) ordered positive-debt occurrences from \(C_{p,1}\) to \(C_{p,2m_p+1}\). Suppose **all requests for every selected key lie in \(J=[A,B)\)**, except that a request's final pre-horizon may equal \(B\). For each key, at most one of its \(2m_p+1\) selected event pre-horizons lies at \(B\); all the others lie in \([A,B)\). Hence \(2m_p\le N_p(J)+1\), and by \(b_i\le p+30\),

\[
\sum_{\text{paired debt of key }p}b_i
  \le 2m_p(p+30)
  \le (p+30)\left(\frac{L}{7p}+31\right). \tag{D2}
\]

For any set \(\mathcal P\) of \(d\) *distinct* prime keys, each with any number of adjacent paired requests, put \(A_{\mathcal P}=\sum_{p\in\mathcal P}(p+30)\) and
\(c_{\mathcal P}=\sum_{p\in\mathcal P}(p+30)/(7p)\). Summing (D2) gives

\[
\boxed{\quad B_{\mathrm{paired}} \le c_{\mathcal P}L+31A_{\mathcal P}.\quad} \tag{D3}
\]

The function \((p+30)/(7p)\) decreases with \(p\). The largest possible \(c_{\mathcal P}\) for \(d=4\) occurs at primes \(61,67,71,73\):

\[
c_{\mathcal P}\le
\frac{122290244}{148280447}
=0.8247226554\ldots<1.
\]

Therefore **for at most four distinct prime keys, with arbitrarily many paired reuse windows**, all selected paired debt is paid by \(L\) whenever

\[
\boxed{L\ge177\,A_{\mathcal P}.} \tag{D4}
\]

Likewise, for at most three keys, the maximum coefficient (from \(61,67,71\)) is \(1265781/2031239=0.623157\ldots\), so \(L\ge83\,A_{\mathcal P}\) suffices.

This is an elementary paper bound (CRT/counting plus previously established event prerequisites), not a new kernel-checked Lean theorem or a finite-program output. It leaves the shorter-width cases \(L<177\,A_{\mathcal P}\) for four or fewer keys, and arbitrary intervals with five or more participating keys. The \(d=5\) maximum coefficient already exceeds one, so (D3) alone cannot settle that regime.

## 6. What remains and a possible stronger sieve charge

The full overlap problem involves several distinct primes with **several paired windows per key**. A one-window-per-prime certificate does not automatically imply a multi-window Hall condition: windows of the same key are disjoint, but windows of other keys may bridge them.

A possible improvement exploits the same 15 inert residues. For fixed prime \(p\ge61\), the conditions \(C\bmod210\in\text{inert}\) and \(C\bmod p\in\{\pm1\}\) select **exactly 30** residue classes modulo \(210p\), by the Chinese remainder theorem. Thus the *average* admissible pre-horizon density is \(1/(7p)\), much smaller than the coarse triple-spacing density \(1/(3p)\). A periodic-discrepancy or Hall-with-credit bound derived from these residue classes may control arbitrary repeated-key overlap. No such uniform bound is established here.

As a check that repeats really can occur in the **local** first-hit dynamics, starting from the artificial state \((s,C)=(8,289,324,16,578,642)\) (\(X=2s-C=6\)), the prime \(61\) produces positive-debt events at pre-horizons \(16,578,642,\ 16,578,762,\ 16,579,008\), with debts \(28,40,12\). The first-to-third displacement is exactly \(366=6\cdot61\). This is an artificial initial state (not a certified A166944 canonical record).

**Unresolved:** the uniform global positive-debt budget, Cap B, the A166944 conjecture, and twin-prime infinitude.
