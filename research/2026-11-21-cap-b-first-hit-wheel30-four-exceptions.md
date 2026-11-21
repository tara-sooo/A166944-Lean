# Cap B continuation: 450-state first-hit wheel and four exceptional primes

**2026-11-21 JST.** Status: **proved paper reductions + locally executed C++17 finite arithmetic certificate; NOT an unrestricted proof of Cap B and NOT a new Lean kernel theorem.**

Reproducible source: [`cap_b_wheel30_four_exception_audit.cpp`](cap_b_wheel30_four_exception_audit.cpp). Read the user's supplied workspace ZIP, specifically `mission_scan/twin_proof/cap_bound/AllIndices.lean`, `CapSampleExact.lean`, `WeightReal.lean`, `WeightCore.lean`, and `slow_backward.md`. This continues the preceding [three-prime wheel experiment](2026-11-21-cap-b-three-exception-wheel30.md).

Run:

```sh
g++ -O3 -Wall -Wextra -Wpedantic -std=c++17 \
 research/cap_b_wheel30_four_exception_audit.cpp -o /tmp/cap_b_wheel30_four
/tmp/cap_b_wheel30_four
```

A local GNU C++17 run of the implementation passed its assertions in ~2.4 seconds and used ~312 MiB peak RSS. The complete source was committed to GitHub and checked by remote readback. No Lean executable or kernel run was used here.

## 1. The exact mod-30 first-hit graph is smaller than the horizon-only wheel

At a genuine moving-horizon state \((s,C)\), where \(C=D(s)\) is even, a nonunit event at \(r>s\) with increment \(e=d(r)\) obeys

\[
e=\begin{cases}\gcd(r,C-1)&r\text{ even},\\
\gcd(r-2,C+1)&r\text{ odd},\end{cases}
\quad C'=C+e-1.
\]

The existing theorem `WeightReal.allowedEdge_of_step` records that all earlier gcds are one. If the true increment divides 30 and exceeds 1, then \(e\in\{3,5,15\}\) and it occurs **at the first nonunit clipped gcd with 30**, within at most 10 indices. The clipped first-hit function is deterministic on the **450 states** \((s\bmod30,C\bmod30)\) with \(C\) even. For each state, take its first clipped hit and, if present, create the edge for that supported increment \(e\).

The exact 450-state graph has **360 forced clipped edges**, is acyclic, and its longest supported-only paths satisfy simultaneously

\[
\boxed{\#\text{supported events}\le5,\quad
       \sum g\le19,\quad
       \sum(e-1)\le16.} \tag{H}
\]

The independent *horizon-only* 15-state congruence model in the earlier note allowed six events, so the genuine first-hit restriction improves the step bound by one and additionally controls the **index distance**.

These bounds apply to any consecutive string of actual events whose increments all divide 30. A full gcd may see other prime factors earlier than the clipped hit: this only terminates the supported-only string sooner.

## 2. A very small coefficient-two travel potential

Perform reverse dynamic programming on that acyclic 450-state functional graph with edge weight \(g-2(e-1)\). Define

\[
W(u)=\max\{0,\ g-2(e-1)+W(v)\}
\]

on every forced edge \(u\to v\), and \(W=0\) at sinks. The finite certificate checks **every edge inequality**

\[
g+W(v)\le2(e-1)+W(u),\quad 0\le W\le4.
\]

At the canonical start \(s_0=M+2,\ C_0=2M-2\), with \(M\equiv1\pmod6\), one has \(W(s_0,C_0)\le3\) (checking the five possible \(M\bmod30\) values).

**Every odd composite increment is also paid without extra debt.** If its least prime factor is \(f\ge3\), then \(e\ge f^2\) and the existing Lean first-hit factor-gap lemma gives \(g\le2f\). Hence

\[
g-2(e-1)+W_{\rm after}-W_{\rm before}
\le2f-2(f^2-1)+4\le-6.
\]

The only possible positive coefficient-two debt belongs to **prime increments \(p\ge7\)**. For every such prime event, \(g\le2p\), so

\[
g-2(p-1)+W_{\rm after}-W_{\rm before}\le6.
\]

Telescoping along any genuine canonical path gives the **general paper-level bound**

\[
\boxed{T\le2G+3+6N_{\mathrm{prime}\ge7},} \tag{P}
\]

where \(T=s_f-(M+2)\), \(G=C_f-(2M-2)\), and \(N_{\mathrm{prime}\ge7}\) counts its prime-increment events with \(p\ge7\), including repeats. This competes with the earlier mod-2310 bound \(T\le2G+3+11N_{\mathrm{prime}\ge13}\): the mod-30 certificate has a smaller per-exception cost (6 instead of 11), but counts the prime increments 7 and 11 as exceptions.

**Unresolved:** a global bound on \(G\) or the exceptional-prime count sufficient to yield unrestricted Cap B.

## 3. Why a full horizon period proves all fixed-alphabet cases

Fix any even \(P\) divisible by each allowed odd increment \(e>1\). If \(C\) is even and \(e\mid C-1\) or \(e\mid C+1\), write \(u=C\bmod P\). Then \(u\) is even. If \(u=0\), no such \(e\) is possible. Otherwise the positive even distance \(P-u\) is at least \(e-1\): the closest even residue below a multiple of \(P\) congruent to \(+1\pmod e\) is \(P-(e-1)\), and the closest congruent to \(-1\pmod e\) is \(P-(e+1)\). Consequently

\[
\boxed{u+(e-1)\le P.} \tag{R}
\]

The unwrapped horizon residue strictly increases along each permitted event, and a path reaching \(P\equiv0\pmod P\) cannot have another allowed event. This is the elementary arithmetic underlying existing `RecordBarrier.lean` common-multiple barriers.

Thus for a *fixed finite alphabet*, exact dynamic programming on \(0,2,\ldots,P\), initialized with score zero at **every** possible starting horizon, computes a bound for any actual event path regardless of the original absolute horizon. It uses only necessary horizon divisibility, so its event counts may exceed those of genuine first-hit paths.

## 4. Four exceptional primes: the complete period yields 12, not 11

Take the supported increments \(\{3,5,15\}\) and exactly four allowed exceptional primes

\[
S=\{61,67,71,73\},\quad
P=30\cdot61\cdot67\cdot71\cdot73=635487630.
\]

The C++17 DP scans **all 317,743,816 even horizons** in one period (using approximately 303 MiB for the byte-array DP). Every permitted horizon event is an edge \(C\to C+e-1\) whenever \(e\mid C-1\) or \(e\mid C+1\); an exceptional prime edge adds one to the score. The precise maximum is:

\[
\boxed{N_{S}\le12.} \tag{F}
\]

This maximum is first reached at horizon residue \(C=443748\); one maximizing path starts at \(C=442892\) and contains 19 total events, 12 exceptional.

This genuinely extends the earlier **three-prime** finite verification to one four-prime alphabet, without claiming coverage of all possible sets of four primes. It also shows the three-prime maximum 11 does **not** extend verbatim to four primes in the horizon-only model.

Using (H), any actual path restricted to these seven increment values has at most 12 exceptional events and 13 supported-only strings. The pre-existing first-hit factor gap bound gives \(g\le2p\le146\) on the four-prime exceptions. Therefore

\[
\boxed{T\le 12\cdot146+13\cdot19=1999.} \tag{I}
\]

Consequently **Cap B holds for every canonical path whose post-record increments belong to \(\{3,5,15,61,67,71,73\}\), provided \(M\ge2669\)**, since \(4T\le7996\le3M-9\). In particular it holds under this alphabet restriction at the official threshold \(M\ge45895573\).

This conditional result relies on the C++17 finite result (F) plus the paper argument, not on a new Lean proof.

## 5. First-hit minimality rejects one longest horizon word

The DP's 12-exception maximizing horizon word can be reconstructed as:

```text
pre-C    increment
442892    73
442964     5
442968    71
443038    73
443110     3
443112    71
443182    73
443254    71
443324     3
443326    15
443340    67
443406     5
443410    61
443470     3
443472    67
443538    71
443608    67
443674     5
443678    71
```

The verifier enumerates **every** integer initial index \(s\) with \(C/2\le s<C\) at \(C=442892\), and applies the **actual, unclipped** gcd rule on each following event, with \(g\le2e\). Requiring the first four event increments of the displayed word gives:

| Step | Candidate pre-step indices | Matching genuine first hits | Distinct next indices |
| ---: | ---: | ---: | ---: |
| 1 (73) | 221446 | 4183 | 1517 |
| 2 (5) | 1517 | 303 | 303 |
| 3 (71) | 303 | 9 | 9 |
| 4 (73) | 9 | 0 | 0 |

Therefore **this specific** 12-exception horizon word is impossible as an actual first-hit trajectory. This does **not** exclude all other horizon words of length 12, nor prove any improved universal maximum below 12. It demonstrates exactly where the extra index/gcd information can strengthen the coarse four-prime DP.

## 6. Remaining open arithmetic

The unrestricted Cap B theorem allows arbitrarily many distinct exceptional increments and odd composites not dividing 30. The finite alphabet bound (F) cannot limit their total universally. The general budget (P) still contains both \(G\) and \(N_{\mathrm{prime}\ge7}\); neither is uniformly small enough yet.

Potential next direction: replace the coarse horizon DP with a symbolic/finite-index first-hit filter, retaining sufficient \((s,C)\) information to exclude long words with many varying primes, and combine the resulting exceptional-prime density with \(G\). Cap B and the twin-prime conjecture remain **open**.
