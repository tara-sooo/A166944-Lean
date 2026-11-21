# Cap B: signed-offset ledger for prime debt; first-use and small-prime audit

Date: 2026-11-21 JST. **Status: paper lemmas plus an executable finite certificate, NOT a Lean-kernel proof and NOT Cap B.**

Reproduction: [`cap_b_prime_debt_audit.py`](cap_b_prime_debt_audit.py) (Python 3 standard library only). This builds the complete 22,050-state mod-210 potential used in [`cap_b_prime_debt_210.py`](cap_b_prime_debt_210.py), checks the finite calculations below, and replays two authentic canonical local segments with the *unclipped* first-gcd event rule. The finite check has 58,232 graph edges and a potential \(V\in[0,29]\). The combinatorial deductions below are paper proofs, not new Lean declarations.

## 1. Event notation, correct global problem

At a first nonunit moving-horizon event \((s,C)\to(r,C')\), let
\[
g=r-s,\qquad e=d(r),\qquad C'=C+(e-1),\qquad X=2s-C.
\]
The old Lean development gives \(C\) even, \(X\ge0\), \(g\le2e\), and \(eg\le2(C+1)\) at genuine events. At an event,
\[
\boxed{\Delta X:=X'-X=2g-(e-1).} \tag{O1}
\]

For a **prime** increment \(p=e\ge11\), retain the mod-210 positive debt
\[
b=\big[g-(p-1)+V(r,C')-V(s,C)\big]_+.
\]
For all composite increments and \(e\in\{3,5,7\}\), the prior finite certificate with its paper tail argument pays travel without positive debt. For any canonical path from \((M+2,2M-2)\), write \(T=s_f-(M+2)\), \(G=C_f-(2M-2)\), and \(B=\sum b\). The known conditional budget reads
\[
T\le G+27+B. \tag{PB}
\]
Consequently the *separate* uniform condition \(4(G+B)\le3M-117\) would imply Cap B, but has not been proved. In particular, no argument here bounds \(G\) uniformly.

## 2. Positive prime debt, its offset increment, and the new signed ledger

For every event with a prime increment \(p\ge11\) and **positive** debt \(b>0\), using \(V_{\rm after}-V_{\rm before}\le29\) gives
\[
\begin{aligned}
2b
 &= 2g-2(p-1)+2(V_{\rm after}-V_{\rm before})\\
 &= \Delta X-(p-1)+2(V_{\rm after}-V_{\rm before})\\
 &\le \Delta X+59-p.
\end{aligned}
\]
Thus the fundamental *per-event* inequality is
\[
\boxed{2b+(p-59)\le\Delta X.} \tag{O2}
\]

In particular, **every positive-debt prime \(p\ge61\) increases the offset**:
\[
\boxed{\Delta X\ge p-57\ge4.} \tag{O3}
\]

For any finite true-event path (not just a canonical one), define the *downward-offset growth*
\[
G_\downarrow=\sum_{\Delta X_i<0}(e_i-1).
\]
Let \(B_{\ge61}\) be the total positive debt at primes \(p\ge61\) and \(P_{\ge61}\) the multiset of those occurrences, with multiplicity. Summing (O2) only over these events gives
\[
2B_{\ge61}+\sum_{i\in P_{\ge61}}(p_i-59)
 \le \sum_{i\in P_{\ge61}}\Delta X_i.
\]
The sum on the right is at most the sum of *all positive* offset increments, which is
\[
(X_{\rm end}-X_{\rm start})+\sum_{\Delta X_i<0}(-\Delta X_i).
\]
For every negative-offset event, \(-\Delta X_i=(e_i-1)-2g_i\le e_i-1\). Therefore:
\[
\boxed{
2B_{\ge61}+\sum_{i\in P_{\ge61}}(p_i-59)
 \le X_{\rm end}-X_{\rm start}+G_\downarrow.
} \tag{O4}
\]
**This bound handles arbitrary repetitions of arbitrarily many distinct primes, with no overlap multiplicity or Hall allocation.** It does *not* require pairing the second and third occurrences. Its important qualification is the endpoint-offset term.

For a *completed offset-return excursion*, i.e. \(X_{\rm end}\le X_{\rm start}\), (O4) gives the particularly clean result
\[
\boxed{2B_{\ge61}\le G_\downarrow,} \tag{O5}
\]
with strictly more credit from the positive terms \(p_i-59\). Thus all \(p\ge61\) positive debts on any such excursion, first-use and repeated, are simultaneously covered by at most half of the horizon increase on the *offset-decreasing* steps. No CRT overlap theorem is needed for these **completed** excursions.

The same argument applied to **all** positive-debt primes \(p\ge11\) yields a unified residual surcharge only for the finite set \(11\le p\le59\):
\[
\boxed{
2B+\sum_{\substack{i:\;p_i\ge61\\b_i>0}}(p_i-59)
 \le X_{\rm end}-X_{\rm start}+G_\downarrow
   +\sum_{\substack{i:\;11\le p_i\le59\\b_i>0}}(59-p_i).
} \tag{O6}
\]
The latter finite-prime surcharge is counted **per occurrence**, not once per distinct prime.

**Critical limitation:** Substituting \(X_{\rm end}-X_{\rm start}=2T-G\) into (O4)/(O6) and then into (PB) does **not** prove Cap B; the \(T\) terms cancel. The outstanding global task is to control the *unfinished final excursion* (large endpoint \(X\)), the small-prime surcharge, and/or \(G\) using more of the authentic record history. The strong part of (O4) is its no-overlap charge on **returns**, not a bound on arbitrary endpoints.

## 3. Positive prime \(p\ge43\) cannot land at \(X'=0\) or \(X'=6\)

The exact event package already in Lean says:
- at an **even** event with prime increment \(p\), \(X'\) is a nonnegative multiple of \(2p\);
- at an **odd** event, \(X'=6+2pk\) for some \(k\ge0\).

Suppose \(X'\in\{0,6\}\). Then \(g=(X'-X+p-1)/2\le(p+5)/2\) because \(X\ge0\). Hence
\[
b\le[(p+5)/2-(p-1)+29]_+=[(65-p)/2]_+.
\]
For every prime \(p\ge67\), this is zero. The remaining primes \(p=43,47,53,59,61\) are treated by a finite overapproximation.

The earlier mod-210 first-hit condition says **any positive debt with prime \(p\ge43\) has**
\[
\gcd(C-1,210)=\gcd(C+1,210)=1, \tag{I}
\]
since a 3/5/7-divisible horizon would trigger a genuine hit by gap 14, whereas such a prime event must precede that hit and would have \(g\le13\) and \(b\le0\).
At each inert residue \(C\bmod210\), the certified \(V(s,C)\) is zero for *all* \(s\bmod210\). To exhaust \(X'=0,6\), it suffices to enumerate \(C\bmod420\), even \(X\in[0,p+5]\), the prescribed parity of \(r=(C+X)/2+g\), and the potential at the successor state. This enumerates a **superset** of true first hits; it does not even impose \(p\mid C\pm1\).

The executable records the maximum *signed* net cost \(g-(p-1)+V'-V\):

| Prime \(p\) | 43 | 47 | 53 | 59 | 61 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Max reset net cost | -2 | -2 | -1 | -8 | -15 |

All five are negative. Therefore:
\[
\boxed{p\ge43,\ b>0\quad\Longrightarrow\quad X'\ge2p.} \tag{O7}
\]
For odd events, the stronger \(X'\ge2p+6\) holds. A large-prime positive debt always ends outside the \(X=0,6\) reset sector. This is a new finite-arithmetic structural implication and remains to be formalized in Lean.

## 4. Audit of \(p=31,37,41\) and six smaller prime keys

For a non-inert horizon, let \(g_0\le14\) be the first *clipped* gcd hit of a factor \(3,5,7\). A genuine prime \(p\ge11\) hit with \(b>0\) must have \(g<g_0\); its increment is not divisible by \(3,5,7\). Enumerating all \(22,050\) residue states, each possible \(g<g_0\), and the exact \(V\)-change for \(e=p\), the maximum signed costs are:

| \(p\) | 31 | 37 | 41 |
| --- | ---: | ---: | ---: |
| Max non-inert net cost | -2 | -7 | -10 |

For \(p\ge43\) non-inert cases are already excluded analytically. Thus **every positive-debt prime \(p\ge31\) has an inert pre-horizon**. The six primes \(11,13,17,19,23,29\) can still produce non-inert positive debt.

For each of those six small primes, independently enumerate residue states and \(1\le g\le2p\), stopping strictly before any earlier clipped hit. Denote by \(\nu_p\) the number of even \(C\bmod210\) classes which admit any *hypothetical* positive debt, and by \(\beta_p\) its maximum possible positive cost:

| \(p\) | 11 | 13 | 17 | 19 | 23 | 29 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| \(\nu_p\) | 43 | 41 | 31 | 32 | 28 | 17 |
| \(\beta_p\) | 41 | 42 | 46 | 49 | 52 | 58 |

These are **safe overapproximations** because the true \(p\)-first-hit congruence has been relaxed. Combining the eligible \(C\bmod210\) classes with \(p\mid C-1\) or \(p\mid C+1\) by CRT leaves at most \(2\nu_p\) classes modulo \(210p\). For a half-open pre-horizon interval of length \(L\), the number \(n_p\) of positive-debt events of that prime therefore obeys
\[
n_p\le \frac{\nu_p}{105p}L+2\nu_p,\qquad
B_{p,\mathrm{positive}}\le\beta_p\left(\frac{\nu_p}{105p}L+2\nu_p\right). \tag{S}
\]
This is valid for arbitrary repeat counts, but summing (S) gives the weak global coefficient \(\approx5.2995L+17,842\). It localizes the six exceptions without yet paying their total debt.

## 5. Independently recomputed first-use prime envelope

For a first crossing of Cap B let
\[
K=\lfloor(7M-1)/4\rfloor,\quad U=2K+1.
\]
For any prime event \(p\ge11\) before that crossing, existing first-hit lemmas give \(g\le2p\) and \(pg\le2U\). Thus its positive debt is bounded by
\[
f_U(p)=\max\big(0,\min(2p,\lfloor2U/p\rfloor)-p+30\big).
\]
Counting the **first** positive-debt event of each distinct prime once,
\[
\boxed{B_{\rm first}\le F_M:=\sum_{p\ge11\ {\rm prime}} f_U(p).} \tag{F}
\]
Terms with \(p(p-30)\ge2U\) vanish, so the sum is finite. The prime number theorem yields \(F_M=(7\log 2+o(1))M/\log M\) as \(M\to\infty\) (since \(U\sim(7/2)M\)). This is an explicit *upper envelope*, **not** a uniform Cap B proof.

At \(M=45,895,573\), the self-contained sieve gives
\[
K=80,317,252,\quad U=160,634,505,\quad
\#\{p:f_U(p)>0\}=2,052,\quad
\boxed{F_M=12,241,507.}
\]
The numerical value in the previous conversation is therefore reproduced exactly.

## 6. True-gcd segment checks and revised target

The verifier also recomputes actual first-gcd events from canonical coordinates. Here \(G_\downarrow\) sums \(e-1\) over events with negative \(\Delta X\); \(S_{\rm large}=\sum_{p\ge61,b>0}(p-59)\).

| \(M\) | Events | \(X_{\rm end}\) | \(G_\downarrow\) | \(B_{\ge61}\) | \(S_{\rm large}\) | \(2B_{\ge61}+S_{\rm large}\) | \(X_{\rm end}-6+G_\downarrow\) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 45,895,573 | 37 | 6 | 1,154 | 144 | 184 | 472 | 1,154 |
| 5,875,882,249 | 26 | 60,276 | 296 | 15,091 | 30,052 | 60,234 | 60,566 |

Both pass (O4). The first segment returns to \(X=6\), so (O5) applies. The second segment is a genuine **unfinished large-offset excursion**, showing concretely why the endpoint term in (O4) matters.

### Revised proof program

1. **Completed excursions:** (O4)/(O5) already control *all* prime \(p\ge61\) positive debt without any overlap allocation, even if many distinct primes repeat simultaneously.
2. **Finite smaller-prime surcharge:** improve (S), perhaps using actual first-hit alternation and signed negative-credit rather than gross positive-event counts; the six keys below 31 are the non-inert exceptions.
3. **Unfinished terminal excursion:** prove an upper bound on \(X_{\rm end}\) or its excursion surplus, specifically for authentic canonical capped paths, using the record-history/first-hit constraints; otherwise the \(X\) term in (O4) cancels the travel target.
4. **Horizon growth:** the uniform control of \(G=C_f-(2M-2)\) or an equivalent two-variable endpoint barrier remains necessary for Cap B.
5. **Lean:** formalize the finite potential, offset ledger, reset-sector lemma, and finally the missing global bound. No new Lean build was executed for this research note.

**Current mathematical status:** Cap B, the unconditional global debt budget, the A166944 conjecture and twin-prime infinitude remain open. The signed-offset ledger replaces an unbounded overlap/Hall problem on **completed excursions** with a short telescoping proof; it leaves the terminal excursion and small-prime surcharge unresolved.
