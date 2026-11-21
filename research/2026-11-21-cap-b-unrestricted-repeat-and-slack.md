# Cap B beyond a fixed exception alphabet: repeat-spacing, zero-slack barriers, and a modular first-breach threshold

2026-11-21 JST. **Status:** paper-level general deductions from existing Lean theorems and a reproducible 450-state arithmetic check; **Cap B and twin-prime infinitude remain OPEN**. No new Lean kernel build was performed.

Reproducible Python 3 verifier (stdlib only): [`cap_b_saturation_audit.py`](cap_b_saturation_audit.py). Its potential table is regenerated using exactly the edge algorithm in the uploaded workspace's `mission_scan/twin_proof/cap_bound/event_weights.py`, `generate_potential.py`; the resulting **450 integers exactly matched** the user's attached `WeightData.lean` in a local comparison. Essential archive sources: `WeightReal.lean`, `WeightCertificate.lean`, `WeightedCut.lean`, `FirstCut.lean`, and the existing common-multiple barrier `A166944/RecordBarrier.lean`.

## 1. Which part of the old alphabet approach is unnecessary

For every real first-hit moving-horizon event, write \(e=d(r)\) (odd, \(e\ge3\)), \(g=r-s\), and \(C'=C+e-1\). The existing Lean theorem `CapWeight.step_bound` already establishes

\[
4g+W(s,C)\le 9(e-1)+W(r,C'),\qquad 0\le W\le32. \tag{1}
\]

It follows that every first-hit path, with travel \(T=s_f-s_0\) and horizon growth \(G=C_f-C_0\), satisfies the already-kernel-proven **unrestricted**

\[
4T\le 9G+32. \tag{2}
\]

For \(e\ge9\), \(g\le2e\) immediately gives \(4g\le8e\le9(e-1)\). Thus only \(e=3,5,7\) need amortization to establish (2); classifying long lists of larger primes cannot improve its right-hand coefficient without a *different* use of event structure. The previous fixed 3- and 4-prime alphabet arguments remain correct conditional cases but are not the shortest route to a general travel/growth statement.

## 2. Arbitrary-alphabet repeat-spacing lemma

Suppose the same **prime** \(p\ge5\) occurs twice, consecutively among the \(p\)-events (intervening event values completely unrestricted). Let \(C_1,C_2\) be the pre-event horizons and let \(H\) be the sum of intervening horizon increments \(e_j-1\). Then

\[
C_2-C_1=(p-1)+H,\qquad C_1,C_2\equiv\pm1\pmod p.
\]

Every increment \(e_j-1\) is even, so \(H\) is even. Consequently

\[
H\equiv -1,\ 1,\ \text{or }3\pmod p,
\]

and each residue class's **least nonnegative even representative** is respectively \(p-1,\ p+1,\ p+3\) for odd \(p\ge5\). Thus

\[
\boxed{H\ge p-1.} \tag{3}
\]

If \(p\) occurs \(k_p\ge1\) times in any path, the \(k_p-1\) disjoint intervening intervals together with its own \(k_p\) increments yield the **unrestricted frequency cost**

\[
\boxed{G\ge(2k_p-1)(p-1).} \tag{4}
\]

More globally, let \(N_{\ge7}\) count all prime-valued increment events \(p\ge7\), and let \(k_7\) count those with value \(7\). Since every other such prime is at least 11,

\[
G\ge 6k_7+10(N_{\ge7}-k_7)=10N_{\ge7}-4k_7,
\quad
G\ge12k_7-6.
\]

Three times the first inequality plus the second gives

\[
\boxed{15N_{\ge7}\le2G+3.} \tag{5}
\]

This bound has **no alphabet-size or prime-value restriction**. The local gcd verifier independently checked (3) on complete authentic segments at \(M=5419\), \(45895573\), \(5875882249\). Formula (5) is weaker for travel than the pre-existing (2), but it is a genuine diversity/frequency constraint.

## 3. The per-event slack: expensive composites and large primes

Set

\[
\lambda_i=9(e_i-1)+W(s_{i+1},C_{i+1})-W(s_i,C_i)-4g_i\ge0.
\]

All \(W\)-values in `WeightData.lean` are **even**, so \(\lambda_i\) is a nonnegative even integer. Write \(\Lambda=\sum_i\lambda_i\). Telescoping (1) gives the exact identity

\[
\boxed{4T+W(s_0,C_0)+\Lambda=9G+W(s_f,C_f).} \tag{6}
\]

Every odd composite \(e\ge9\) has a prime divisor \(f\ge3\) with \(f^2\le e\). The Lean-proved first-hit factor bound gives \(g\le2f\). As \(W_{\rm pre}\le32\), \(W_{\rm after}\ge0\),

\[
\lambda_i\ge9(e-1)-8f-32\ge16. \tag{7}
\]

For any odd \(e\ge43\), even without factoring \(e\),

\[
\lambda_i\ge9(e-1)-8e-32=e-41. \tag{8}
\]

Therefore the genuinely unrestricted refined path inequality is

\[
\boxed{
4T+16N_{\mathrm{composite}}+
  \sum_{\substack{i:e_i\text{ prime}\\e_i\ge43}}(e_i-41)
\le9G+32.
} \tag{9}
\]

Here the large-prime sum and composite-event count are disjoint. This is new paper-level strengthening of the existing kernel-checked 9/4 potential identity: large exceptional increments **spend strictly positive slack**, irrespective of how many distinct values appear.

## 4. A strict asymptotic coefficient below 9/4 — tiny but unrestricted

The finite 450-state check in the companion script reconstructs the exact \(W\) table and verifies the first-hit residue condition for every allowed \(e\le39\). For \(e\ge41\), (1) holds automatically by \(4g+W_{\rm pre}\le8e+32\le9(e-1)\).

The same finite table gives:

- For \(e=37,41,43\), every mod-30-permitted first-hit edge has \(\lambda_i\ge30\) (all three exact minima are 30).
- For composites, (7) gives \(\lambda_i\ge16\).
- For \(e\ge45\), (8) gives \(\lambda_i\ge e-41\).

It follows that **every zero-slack event is an odd prime \(e\le31\)**. Further, every *positive*-slack event satisfies

\[
\boxed{e-1\le15\lambda_i.} \tag{10}
\]

Proof of (10): for \(e\le31\) use \(\lambda_i\ge2\) and \(e-1\le30\); for \(33\le e\le43\) use (7) or the three finite checks; and for \(e\ge45\) use \((e-1)\le15(e-41)\le15\lambda_i\).

Let

\[
Q=2\prod_{\substack{3\le p\le31\\p\text{ prime}}}p
=\boxed{200560490130}.
\]

Any consecutive segment **entirely made of zero-slack events** has every \(e_i\mid Q\). The usual common-multiple barrier, using the fact that \(C\bmod Q\) moves strictly forward without crossing the next multiple of \(Q\), bounds the segment's horizon growth by \(Q-2\). (The initial \(C\) is even; each \(e_i\) is odd; and \(e_i\mid C\pm1\).)

There are at most \(\Lambda/2\) positive-slack events, hence at most \(\Lambda/2+1\) zero-slack segments. Their total growth is at most \((\Lambda/2+1)(Q-2)\); the positive events contribute at most \(15\Lambda\) by (10). Therefore

\[
G\le15\Lambda+\left(\frac{\Lambda}{2}+1\right)(Q-2)
=\frac{Q+28}{2}\Lambda+Q-2.
\]

Combining with (6) and \(0\le W\le32\) yields the **unrestricted strict-slope estimate**

\[
\boxed{
4T\le\left(9-\frac{2}{Q+28}\right)G+
34-\frac{60}{Q+28}.
} \tag{11}
\]

It beats the coefficient \(9/4\) by \(1/[2(Q+28)]\) in the travel/growth ratio. The improvement is around \(2.5\cdot10^{-12}\) on the \(T/G\) coefficient and only manifests beyond a giant additive scale. The finite exclusion of 37/41/43 has **not** been formalized in Lean. Without that new finite check one may instead use \(Q=2\prod_{3\le p\le41}p=304250263527210\) and the weaker, purely paper-analytic bound

\[
4T\le\left(9-\frac{1}{Q+38}\right)G+
33-\frac{40}{Q+38}.
\]

Both are far too weak, at the known threshold, to settle Cap B. Their significance is that **the alphabet restriction has disappeared completely**.

## 5. Sharper exact first-breach necessary condition at M=45,895,573

Let \(M=45895573\), \(s_0=M+2\), \(H_0=2M-2\), \(K=\lfloor(7M-1)/4\rfloor\), \(G=D(K)-H_0\). If a genuine capped path first crosses \(K\), let \((s,C)\to(r,C')\) be its crossing step, with \(s\le K<r\) and \(C=D(K)=H_0+G\).

The existing `WeightedCut.path_bound` on the prefix yields

\[
4(s-s_0)\le9G+W(s,C)-W(s_0,H_0).
\]

The regenerated \(W\) table gives \(W(s_0,H_0)=12\). Let

\[
W_{\max}(c)=\max_{0\le t<30}W(t,c),\qquad
b(C)=\min\left(
\lfloor\sqrt{4(C+1)}\rfloor,\
\begin{cases}6,&3\nmid C,\\+\infty,&3\mid C,\end{cases}\
\begin{cases}10,&C\bmod5\in\{1,4\},\\+\infty,&\text{otherwise.}\end{cases}
\right).
\]

The bounds \(g\le6\) or \(g\le10\) arise from a forced 3- or 5-divisor first hit; the square-root branch is `FirstCut.step_gap_le_sqrt`. Therefore crossing requires

\[
\boxed{
4(K+1-s_0)\le9G+W_{\max}((H_0+G)\bmod30)-12+
4b(H_0+G).
} \tag{12}
\]

Every \(G\) is even. The companion program evaluates (12) for all relevant even \(G\), with the lower part excluded by monotonic coarse bounds, and finds

\[
\boxed{\text{first crossing requires }G\ge15,289,326.} \tag{13}
\]

At the minimum \(G=15,289,326\), necessarily \(D(K)\equiv0\pmod{30}\); the right-hand slack budget in (12) is exactly **20**. The path prefix's composite-event count is therefore at most **one**, and no prime event \(p\ge67\) can occur in the prefix (by (9)).

For comparison the earlier fixed-sample sufficient test `1000*D(K)<=2333*M` permits \(G\le15,283,227\). Thus this exact-cut numerical obstruction excludes another range of possible growth values but does not rule out all \(G\).

A useful local dichotomy: if \(D(K)\bmod30\notin\{0,12,18\}\), then \(b(C)\le10\), whence (12) forces \(G\) to be around 15.299 million instead of 15.289 million. The only way a first crossing can occur at the smallest admissible \(G\) is for both \(C-1\) and \(C+1\) to avoid 3 and 5.

## 6. Status

The paper deductions (3)–(13) and local Python check are reproducible. The strict-slope theorem (11), the prime-repeat frequency formula (5), and the modular-cut refinement (12) are **not new Lean declarations**. Existing Lean code supplies (1), (2), the first-hit divisor-gap bounds, and the ordinary-index slow-interval implication.

The obstruction to unconditional Cap B remains a **uniform upper bound on the genuine horizon growth \(G=D(K)-(2M-2)\)**, or a different way to force a twin-prime horizon before the cutoff. None of these new lower bounds on the cost of crossing gives that upper bound. For the certified record \(M=45895573\), actual \(G=1914\), orders of magnitude below the necessary hypothetical value in (13).
