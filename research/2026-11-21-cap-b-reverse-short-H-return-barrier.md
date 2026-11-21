# Cap B: reverse-CRT return barrier for short selective-H event runs

Date: 2026-11-21 JST. **Result:** a finite-arithmetic lemma governing low-offset returns from *any* moving-horizon state, plus exact local gcd witnesses of both remaining return mechanisms. This is **not** a Lean-kernel proof and **not** a proof of unrestricted Cap B or twin-prime infinitude.

## Reproducible certificate

Run `python3 research/cap_b_short_H_reverse_return.py` (Python 3 standard library only). [Source](cap_b_short_H_reverse_return.py), committed with exact GitHub remote readback and matched to the locally executed 5,680-byte ASCII source (FNV-1a 32-bit checksum `af04d480`). The program exhaustively enumerates **110,466** necessary-condition CRT prefixes, contains **no artificial depth cap**, and checks true unclipped gcds at all event/intermediate indices for several synthetic witnesses.

The underlying event rule and terminology were read from the user's attached `workspace.zip`: `mission_scan/twin_proof/cap_bound/WeightCore.lean`, `WeightReal.lean`, `AllIndices.lean`, `slow_backward.md`, and from existing `A166944/RebalancedCrossingGrowth210.lean` and `ReplayOffset210.lean`.

## 1. Why an event has a quantized **post-offset**

Let \((s,C)\to(r,C')\) be a genuine first nonunit event, \(g=r-s\), \(e=d(r)\ge3\), \(C'=C+(e-1)\), and \(X=2s-C,\ X'=2r-C'\). The exact gcd formula implies:

* On an **even** hit, \(e\mid r\) and \(e\mid C-1\). Write \(r=e b,\ C-1=e a\); then \(a\) is odd and \(2b-a-1\) even, giving \(X'=e(2b-a-1)\equiv0\bmod 2e\).
* On an **odd** hit, \(e\mid r-2\) and \(e\mid C+1\). Writing \(r-2=e b,\ C+1=e a\) yields \(X'=e(2b-a-1)+6\equiv6\bmod 2e\).

Hence

\[
\boxed{X'\equiv0\bmod2e\text{ (even hit)},\quad X'\equiv6\bmod2e\text{ (odd hit)}.}\tag{1}
\]

In particular, if \(X'\le10\) and \(e\ge7\), the new offset must be \(0\) or \(6\), respectively. This is a general paper lemma using exact divisibility; no finite arithmetic is needed.

## 2. Exhaustive reverse-CRT lemma at offset ≤10

A **short selective-H event** means, exactly as in the existing Lean classification,

\[
1\le g\le10,\quad 3\le e\le33\text{ odd},\quad e-1<3(g+1).
\]

Fix the **terminal** offset \(X_f\in\{0,2,4,6,8,10\}\) and terminal index modulo 6 (6 choices each, **36 roots**). Enumerate all proposed short-only words **backwards**, keeping their reverse cumulative travel \(T\) and horizon growth \(G\). Before prepending an event, the post-offset of that proposed event is

\[
X_{\rm after}=X_f+G-2T,\quad
X_{\rm before}=X_{\rm after}+(e-1)-2g\ge0.
\]

Its parity is determined by terminal index residue and accumulated travel. The hit must obey (1), and the terminal index \(s_f\) must satisfy the corresponding congruence \(s_f\equiv T\) (even hit) or \(s_f\equiv T+2\) (odd hit) modulo \(e\). Join these with generalized CRT.

After **every** modulus enlargement, the verifier rechecks the entire proposed word in forward order: all intermediate indices have projected gcd \(1\), and every hit has projected gcd exactly its proposed \(e\). The working modulus is \(\mathrm{lcm}(6,e_1,\ldots,e_k)\). Every genuine word projects to one such prefix; extra prime factors can only remove candidates. Since all branches terminate and the program imposes no depth cutoff, the following **uniform arithmetic** statement holds:

\[
\boxed{
\begin{gathered}
X_f\le10,\ \text{all events short selective-H}\\
\Longrightarrow\
\#\text{events}\le22,\quad
\sum(e-1)\le180,\quad
\sum g\le86,\quad
X_{\rm start}\le16.
\end{gathered}
}\tag{2}
\]

The maximum *growth* 180 is attained by a genuine 20-event local first-hit path from \((s,C)=(117649232195,235298464380)\), with \(X_{\rm start}=10\), \(T=85\), and \(X_f=0\). Altering the initial index to \(117649232194\) and the first gap from 9 to 10 gives \(T=86\), still \(G=180\) and \(X_f=0\). Starting at \((51171392,102342768)\) gives a genuine 12-event local path from \(X=16\) to \(X_f=0\). The 22-event length is a safe **upper bound** of the congruence overapproximation; it is not asserted to be achieved by a full-gcd path.

## 3. The corresponding high-offset forward bound is false

An explicit *true full-gcd* 42-event short-H-only path starts at

\[
(s,C)=(4066542049924,5776231270430),\quad
X=2356852829418,
\]

and ends at

\[
(s_f,C_f)=(4066542050110,5776231270752),\quad
T=186,\quad G=322,\quad X_f=2356852829468.
\]

Every earlier unit gcd and all 42 nonunit increments are independently checked by the executable. The offset **increases by 50**, so there is no conflict with the reverse return barrier (2). This witness demonstrates why the earlier **31-event** forward bound for starting offsets \(X\le10\) cannot be applied to arbitrary high-offset starts.

These local initial states are **not asserted to be attained record states** in the original A166944 recurrence.

## 4. Exact structure of any high→low return

Suppose a genuine path starts with \(X>16\) and ends at \(X\le10\). By (2), it **cannot** consist solely of short selective-H events. At least one event of the following types must occur:

1. **Fast/non-H:** \(e-1\ge3(g+1)\) (regardless of gap);
2. **Long selective-H:** \(g>10\), which the already kernel-proved `large_relative_gap_cases` classifies as a **prime increment**, with \(e(e-4)<6(C+1)\).

Both mechanisms are genuine in the *local gcd* model; one exact first-hit step each suffices:

| Type | Pre-state (s,C) | Gap g | Increment e | Offset |
| --- | --- | ---: | ---: | --- |
| Fast | (200,304) | 2 | 101 | 96 → 0 |
| Long prime H | (1482,2928) | 35 | 101 | 36 → 6 |

The first example satisfies \(e-1=100\ge3(2+1)\). The second satisfies \(100<3(35+1)\) and \(g>10\). In both cases all intermediate gcds are 1 and the full gcd at the specified hit is 101.

A one-step consequence not relying on (2): a short H event has \(X_{\rm before}-X_{\rm after}=e-1-2g<g+3\le13\), with even offsets, so a single short H event can lower offset by **at most 12**. The reverse CRT result strengthens this to *whole uninterrupted short-only runs whose final offset is low*.

## 5. What this does, and does not, settle

Previous paper bounds from the existing Lean `ReplayOffset210.lean` imply that **a first Cap B crossing at \(M=45895573\) requires \(H\ge5,291,742\)** on its predecessor prefix, with selective growth \(H=\sum(e-1)\) over events satisfying \(e-1<3(g+1)\). The reverse finite lemma proves that *low-offset-ending uninterrupted short-H blocks* cost at most **180** each.

But a path can have many such blocks, and a short-H run ending at **high** offset can be longer and cost more (42-event witness). The present reduction therefore does **not** globally bound H. A full argument must control (i) the count/cost of fast events that reset high offset, (ii) the count/cost of long-prime H reset events, and (iii) short-only runs ending at high offset. These quantities must be related to **authentic attained record history**, not merely to a freely chosen synthetic state. This is the remaining global proof gap.

Potential Lean target: a reverse-CRT finite certificate deriving (2) from `IsMovingHorizonStep`, followed by the trivial case-split barrier of §4. The finite checker itself has been run in Python, **not** verified by the Lean kernel.
