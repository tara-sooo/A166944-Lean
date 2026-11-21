# Cap B continuation: a uniform dual mod-210 potential and an improved fixed-sample gate

Date: 2026-11-21 JST. **Status: mathematical reduction + fully reproducible finite arithmetic verification; not a Lean kernel proof of the new finite certificate, not an unconditional proof of Cap B or twin-prime infinitude.**

**Executable certificate:** [`cap_b_dual_weight210.py`](cap_b_dual_weight210.py), Python 3 stdlib only. It rebuilds the actual 450-value `WeightData.lean` potential, asserts the SHA256 `bcbf78aa63d6835881fe3514c2813af743b690b76278cc0a5fe3b6e8e3ff75b2` of its row-major bytes, performs the new exact 22,050-state acyclicity check, and tests all 3,883,994 necessary first-hit residue edges with odd increments \(3\le e\le55\). This was independently reproduced from the user's `workspace.zip` (`WeightCore.lean`, `WeightData.lean`, `WeightReal.lean`, `WeightCertificate.lean`, `WeightedCut.lean`). A local Python execution of the finite model passed, and the committed source was retrieved from GitHub with exact content match.

## 1. Original coefficient-9 certificate and integer slack

For an actual moving-horizon first event \((s,C)\to(r,C')\) put \(e=d(r)\), \(g=r-s\), \(C'=C+e-1\). The repository's existing, Lean-kernel checked `CapWeight.step_bound` states

\[
4g+W(s,C)\le9(e-1)+W(r,C'),
\quad 0\le W\le32.
\]

Define the nonnegative **integer** slack

\[
\lambda=9(e-1)+W(r,C')-W(s,C)-4g\ge0.
\]

All 450 original \(W\)-values are even, and every \(e\) is odd, hence every \(\lambda\) is even.

The analytic estimate for large increments is

\[
\lambda\ge9(e-1)-32-8e=e-41, \tag{1}
\]

using the already Lean-proved \(g\le2e\). Therefore **no increment \(e\ge57\) can have zero slack**.

## 2. Full first-hit mod-210 zero-slack graph

The new state is \((s\bmod210,C\bmod210)\), with \(C\) even: exactly \(210\cdot105=\mathbf{22,050}\) states.

For every odd \(3\le e\le55\), generate **all** possible first-hit edges \(1\le g\le2e\) satisfying `WeightCore.allowedEdge(s%30,C%30,e,g)`. This is already a necessary condition for every genuine event by `WeightReal.allowedEdge_of_step`. Add the further necessary mod-7 checks **whenever \(7\mid e\)**:

- \(e\mid C-1\) on an even hit, or \(e\mid C+1\) on an odd hit (hence \(C\equiv\pm1\bmod7\));
- \(e\mid r\) on an even hit, or \(e\mid r-2\) on an odd hit (hence the corresponding \(r\) congruence modulo 7).

Retain only those edges for which \(\lambda=0\). The directed graph is an **overapproximation** of genuine zero-slack paths: other prime factors and the true full gcd have not been imposed.

Complete finite results:

| Quantity | Verified |
| --- | ---: |
| States | 22,050 |
| Zero-slack residue edges | 33,049 |
| Graph has a directed cycle | **No** |
| Maximum number of consecutive zero-slack events | **27** |
| Maximum horizon growth during such a string | **214** |
| Maximum total index travel during such a string | **476** |

In particular, the old primorial \(Q=200560490130\) bound for a zero-slack string can be replaced by the much smaller **214**. This is a mathematical assertion after verifying the finite graph; it is not yet a kernel-checked Lean theorem.

## 3. Dual potential and the uniform whole-path inequality

Run reverse dynamic programming on the acyclic graph, with an edge of increment \(e\) weighted by \(e-1\):

\[
U(v)=\max\left(0,\ \max_{v\to w,\ \lambda=0}\bigl((e-1)+U(w)\bigr)\right).
\]

This defines a nonnegative integer potential \(0\le U\le\mathbf{214}\) on all 22,050 states.

For \(\lambda=0\) edges, the definition automatically gives \(e-1+U_{\rm after}\le U_{\rm before}\).

For all **positive**-slack edges with \(e\le55\), the finite script exhaustively checks

\[
\boxed{e-1+U_{\rm after}\le17\lambda+U_{\rm before}.} \tag{2}
\]

It tests **3,883,994** eligible finite edges; the maximum positive ratio
\((e-1+U_{\rm after}-U_{\rm before})/\lambda\) is exactly **17**, occurring e.g. at the residue edge \(s\equiv151,C\equiv106,e=3,g=5\), where \(\lambda=4\) and the numerator is 68.

For **all odd \(e\ge57\)**, no finite check is needed. From \(\lambda\ge e-41\), \(U_{\rm after}\le214\), and \(U_{\rm before}\ge0\),

\[
17\lambda-(e-1+U_{\rm after}-U_{\rm before})
\ge17(e-41)-(e-1+214)=16e-910\ge2.
\]

Thus (2) holds for **every genuine event, with no bound on its prime factors or size**. Sum over any real first-hit path. With

\[
T=s_f-s_0,\quad G=C_f-C_0,\quad
\Lambda=\sum_i\lambda_i,
\]

the original weight identity and new dual potential give

\[
4T+W_0+\Lambda=9G+W_f,\qquad
G+U_f\le17\Lambda+U_0.
\]

Eliminating \(\Lambda\) gives

\[
\boxed{68T\le152G+17(W_f-W_0)+(U_0-U_f).} \tag{3}
\]

This is an **unrestricted** travel/growth inequality. In particular the asymptotic travel coefficient is \(152/68=38/17\approx2.235294\), compared with the existing Lean result \(9/4=2.25\). No fixed alphabet or event-count restriction remains.

## 4. Canonical initial states keep the same additive constant

An authentic canonical record \(M\ge5\) has \(M\equiv1\bmod6\). At \(s_0=M+2,\ C_0=2M-2\), the 35 residue classes for \(M\bmod210\) satisfying this condition were **all** checked:

\[
\boxed{17(32-W(s_0,C_0))+U(s_0,C_0)\le544.} \tag{4}
\]

From \(W_f\le32,\ U_f\ge0\) and (3), every canonical path obeys the new **whole-path certificate**

\[
\boxed{68T\le152G+544,}\qquad
\boxed{4T\le\tfrac{152}{17}G+32.} \tag{5}
\]

This strictly improves the coefficient of the previously proved `CapWeight.ratio94`, \(4T\le9G+32\), while **retaining the additive constant 32**.

For the actual threshold \(M=45,895,573\), the initial potentials are \(W_0=12,U_0=0\). Consequently the tighter special-case coefficient is

\[
4T\le(152/17)G+20. \tag{6}
\]

## 5. Improved fixed-sample sufficient condition, 2333 -> 2335

Let \(K=\lfloor(7M-1)/4\rfloor\) and suppose \(M\ge45,895,573\) is a genuine canonical record. **Conditional on the new finite dual certificate**, the old sufficient sample

\[
1000D(K)\le2333M
\]

can be relaxed to

\[
\boxed{1000D(K)\le2335M\quad\Longrightarrow\quad\text{Cap B}.} \tag{7}
\]

Here is an explicit inequality proof, not just a numerical experiment:

If Cap B failed, split the capped path at the first event \(s\le K<r\). The new bound (5) on the prefix and the existing square-gap bound \(g=r-s\le R:=\lfloor\sqrt{4(D(K)+1)}\rfloor\) imply

\[
68(K+1-(M+2))\le152G+544+68R,\qquad
G=D(K)-(2M-2).
\tag{8}
\]

The sample assumption implies \(1000G\le335M+2000\). For \(M\ge45,895,573\), elementary squaring shows
\(R\le\lfloor M/1000\rfloor\): write \(b=\lfloor M/1000\rfloor\ge45895\); then
\(D(K)<2335(b+1)\), so \(4(D(K)+1)\le9340(b+1)\le b^2\).

Also \(4(K+1-(M+2))\ge3M-8\). Multiplying (8) by 1000 therefore gives the impossible chain

\[
1000(51M-136)
\le 1000(152G+544+68R)
\le50988M+848000
<51000M-136000,
\]

where the last strict inequality holds for \(M>82,000\).

Thus (7) holds for all stated canonical records, provided the new 22,050-state certificate is formalized or otherwise accepted as a complete finite calculation. **The sample inequality itself remains unproved for arbitrary canonical records.**

## 6. Optional numerical diagnostic for the first-crossing predecessor

For the particular threshold \(M=45,895,573\), one can retain the predecessor's actual mod-210 state rather than bound by the worst-case canonical additive 32. Since \(W_0=12,U_0=0\), a first crossing must satisfy

\[
\boxed{
68(K+1-s_0)
\le152G+\max_{a\bmod210}
\{17(W(a,C)-12)-U(a,C)\}
+68b(C),\quad C=2M-2+G,
} \tag{9}
\]

where \(b(C)\) is the least of \(\lfloor\sqrt{4(C+1)}\rfloor\), 6 if \(3\nmid C\), and 10 if \(C\bmod5\in\{1,4\}\).

Using only (9), the script independently verifies the necessary condition

\[
\boxed{G\ge15,389,916.} \tag{10}
\]

Further using all prime factors of \(C\pm1\), the exact last hit at or before \(K\), and the first hit after \(K\), a separate local enumeration of candidate predecessor residues excludes all \(G<15,393,654\). This is a **numerical fixed-\(M\) diagnostic**, not a universal Cap B theorem: at that genuine record, the known actual \(G=1914\) is vastly smaller.

## 7. Remaining task

The proposed new lemma (2) and acyclic 22,050-state zero-slack certificate are especially suitable as finite-checker inputs for Lean. The paper-level universal bound (5) and fixed-sample upgrade (7) are strong, concrete consequences, but neither supplies the still-missing **uniform upper bound on the true \(D(K)\)**. Therefore the unconditional Cap B theorem and twin-prime infinitude are **not solved**.
