# Cap B continuation: correct-direction offset target, a 28-reset local witness, and a selective large-gap budget

Date: 2026-11-21 JST. **Status:** exact arithmetic deductions from existing Lean theorems, plus finite direct-gcd checks. **Neither Cap B nor twin-prime infinitude is proved.** The user-uploaded `workspace.zip` was reopened and `AllIndices.lean`, `CapSampleExact.lean`, `WeightReal.lean`, `canonical_toll.md`, `slow_backward.md`, and the existing public Lean source were inspected. The companion runnable arithmetic certificate is [`cap_b_offset_direction_audit.py`](cap_b_offset_direction_audit.py) (Python 3 standard library only).

## 1. The direction of the missing inequality

Let \(M\) be an authentic canonical record; set \(s_0=M+2,\ C_0=2M-2,\ K=\lfloor(7M-1)/4\rfloor\). Define the **ordinary index offset** \(X(n)=2n-D(n)\); at any moving-horizon event state \(X(s,C)=2s-C\). Every event has gap \(g\) and horizon increase \(e-1\). Therefore

\[
X_f=6+2T-G,\quad\text{i.e.}\quad \boxed{G=2T+6-X_f}. \tag{1}
\]

The previous coefficient-two/9/4/38/17 potentials are upper bounds of the form \(T\le cG+O(1)\); they do **not** upper-bound \(G\) in terms of distance. To prove the strong cutoff sample \(1000D(K)\le2335M\), one instead needs an **absolute lower bound on** \(X(K)\).

Precisely, because \(D(K)=2K-X(K)\),

\[
1000D(K)\le2335M
\iff
1000X(K)\ge2000K-2335M.
\]

For odd \(M\), this is exactly

\[
\boxed{
1000X(K)\ge
\begin{cases}
1165M-1500,&M\equiv1\bmod4,\\
1165M-500,&M\equiv3\bmod4.
\end{cases}
} \tag{2}
\]

At the certified record \(M=45895573\), \(K=80317252\), \(D(K)=91793058\), and \(X(K)=68841446\simeq1.49996M\), comfortably above the \(\simeq1.165M\) threshold.

The *terminal quiet interval* is crucial: an authentic path may end at offset 0 or 6 and then have ordinary unit increments until \(K\), in which case \(X(K)\) increases by 2 **per unit index**. The paper condition (2) is therefore a quantitative terminal-quiet/anti-reset statement, not a consequence of the event-path upper-travel potentials alone.

## 2. A stronger local reset obstruction even with twin-prime-shaped M

The attached archive's `canonical_toll.md` already proves that synthetic canonical-form starts can admit arbitrarily many exactly first-hit low-offset resets when \(M\) is chosen by CRT. It does **not** require that \(M\) is an authentic record.

Here is an additional explicit witness that **both \(M,M-2\) are prime**, even though the true record-history hypothesis fails.

Take \(M=404983\), where \(404981\) and \(404983\) are prime by complete trial division; start the **synthetic** first-hit process at

\[
(s,C)=(404985,809964),\qquad X=6.
\]

There are **28 consecutive exact first nonunit gcd hits**, each inside its then-current horizon, such that the post-event offset remains in \(\{0,6\}\). The ordered \((g,e)\) values are

```text
(2,5), (1,3), (119,239), (1,9), (2,5), (4,3),
(8,23), (4,9), (6,13), (5,5), (1,3), (3,7),
(6,13), (14,29), (1,9), (5,5), (1,3), (9,19),
(11,29), (2,5), (1,3), (1,3), (5,5), (1,9),
(2,5), (4,3), (5,11), (1,3).
```

For every event the verifier checks \(\gcd(j,C-1)=1\) (even \(j\)) or \(\gcd(j-2,C+1)=1\) (odd \(j\)) for all earlier indices in that gap, then the exact nonunit gcd at its event. The resulting state is

\[
(s_f,C_f)=(405210,810414),\qquad T=225,\quad G=450,\quad X_f=6.
\]

In the **actual A166944 recurrence**, however, \(d(404985)=1,\ D(404985)=713832\), so this synthetic state is **not** an attained canonical record state. This proves that **having twin primes \(M-2,M\) and enforcing all future local first-hit gcd tests is not by itself enough to cap the number of low-offset returns**. Any global anti-return theorem will need the **actual attained-record property**, a quantitative mass budget for returns, or another global ingredient. It does not disprove Cap B.

Three further small synthetic twin-prime-start examples show why a cutoff growth sample is stronger than a terminal prime-pair/barrier conclusion:

| M | K | last event state (s,C) | G | 1000*C > 2335*M? | C-1,C+1 prime? |
| ---: | ---: | ---: | ---: | :---: | :---: |
| 349 | 610 | (474,828) | 132 | yes | yes |
| 601 | 1051 | (738,1428) | 228 | yes | yes |
| 823 | 1440 | (978,1950) | 306 | yes | yes |

All three have \(M,M-2\) prime and a quiet interval before \(K\); all are **below the official record threshold** and are not purported counterexamples to the universal sample with its full hypotheses. They illustrate that an early *twin-prime horizon* can occur despite a relatively large \(G\). The archive's kernel-proved `CapWeight.Sample.cap_iff_twins_at_cutoff` states the exact terminal prime-pair criterion under its authentic-record assumptions, whereas the 2335 sample is only sufficient.

## 3. A more promising selective alternative: charge only large-relative-gap growth

The existing Lean theorem `A166944Research.replay_index_offset_le_of_large_gap_growth210` in `A166944/ReplayOffset210.lean` implies for any canonical first-hit path with its natural `ResidualPhaseTrace210`:

\[
\boxed{3X_f+G\le13H+24}, \tag{3}
\]

where the natural number \(H\) is the sum of horizon increments \(e_i-1\) over exactly those events satisfying

\[
e_i-1<3(g_i+1).
\]

This \(H\) is `trace.growthAtLargeGaps` in the existing Lean definitions. Unlike \(G\), it ignores rapid horizon jumps with small gaps. Equation (3) comes from the proved general inequality \(3X_f+G\le3X_0+13H+6\), using \(X_0=6\).

Using \(2s_f=C_f+X_f\), \(C_f=2M-2+G\) and (3),

\[
12s_f=6(C_f+X_f)\le12M+36+4G+26H.
\]

Thus the following is a valid paper corollary of existing Lean theorems, requiring no new 22,050-state finite certificate:

\[
\boxed{
4G+26H\le9M-39\quad\Longrightarrow\quad
4s_f\le7M-1.
} \tag{4}
\]

If the separate Cap A bound \(C_f\le3M+4\), hence \(G\le M+6\), were also proved, it would suffice to establish

\[
\boxed{26H\le5M-63.} \tag{5}
\]

The 26/5 criterion is less restrictive than bounding *all* of \(G\) at \(0.335M\); it allows \(H\) up to roughly \(0.192M\), and under Cap A, the remaining growth can come from *fast* events that contribute little travel.

**Existing classification already helps:** `ResidualPhaseEvent210.large_relative_gap_cases` proves each event counted by \(H\) is either (i) \(g\le10,\ e\le33\), or (ii) \(g>10\), \(e\) is prime (no proper factor), and \(e(e-4)<6(C+1)\). Bounding the aggregate \(H\) across arbitrarily many events remains open; a large number of small events, or many distinct long-gap prime events, is still possible under the currently proved local inequalities.

Direct genuine-event checks (not new Lean proofs):

| Authentic record M | events checked | G | H | \(X_f\) |
| ---: | ---: | ---: | ---: | ---: |
| 45,895,573 | 37 | 1,914 | 766 | 6 |
| 5,875,882,249 | 26 | 30,564 | 30,370 | 60,276 |

Both examples have \(H\) tiny compared with \(M\), despite different terminal offsets.

## 4. First crossing makes the missing H bound quantitative

Suppose a capped path has a **first** event \((s,C)\to(r,C')\) with \(s\le K<r\). Let \(G=C-(2M-2)\) and \(H\) be the selective growth **up to its predecessor**. Let \(R=\lfloor\sqrt{4(C+1)}\rfloor\). The existing single-step gap bound gives \(g=r-s\le R\), hence \(s\ge K+1-R\). Substitution in (3) yields

\[
\boxed{
2G+13H+6R\ge6(K-M-2).
} \tag{6}
\]

At the official threshold \(M=45895573\), if \(G=15393654\) (a previously analyzed near-minimal crossing candidate), then \(R=20706\), and (6) requires

\[
\boxed{H\ge13509117\approx0.878G.}
\]

Therefore any *near-minimal-growth* first Cap B violation must spend almost all its growth on events where waiting time is long relative to growth. This converts the large-scale problem into a concrete density/packing question involving the existing short-event / long-prime-event dichotomy.

For larger \(G\) the required \(H/G\) becomes weaker; thus ruling out the narrow near-minimal band does not by itself establish Cap B.

## 5. What remains open

Two legitimate proof routes emerge:

1. **Direct sample / anti-reset route:** establish \(X(K)\) above the explicit threshold (2) for every genuine canonical record, or prove a slow interval / terminal twin-prime horizon before \(K\). Local twin-prime starting conditions alone do not control repeated resets (the exact 28-event example).
2. **Selective-growth route:** prove Cap A and the bound (5), or prove the mixed bound (4) directly, for every relevant capped path. This focuses effort on the events classified in `large_relative_gap_cases` rather than on every unit of horizon growth.

Neither the required \(X(K)\) lower bound nor the uniform \(H\) control is currently proved. Both routes are at least expressed in the **correct direction**, whereas a travel-upper-bound potential alone never forces a horizon-growth upper bound.

Reproduce the explicit arithmetic checks:

```sh
python3 research/cap_b_offset_direction_audit.py
```
