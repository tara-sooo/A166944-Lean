# Cap B continuation: short-H runs followed by exactly one fast low-offset return

**2026-11-21 JST.** Status: locally executed, reproducible complete finite arithmetic certificate for a **restricted macro**, with exact genuine local first-gcd witnesses; **not yet Lean kernel-checked**, **not a proof of unrestricted Cap B**.

Executable, standalone Python 3 audit: [`cap_b_short_fast_bridge.py`](cap_b_short_fast_bridge.py). Exact locally executed source SHA-256: `65b9c5f6107f16c574d1f6038f5fbdc67366b2bb7e8e314796f12e8938fb4406`; 5233 bytes. The same contents were committed and verified by GitHub fetch/readback using FNV-1a 32-bit `403dc14c` and full string comparison.

The finite sieve uses the moving-horizon first-gcd formula from the user's uploaded `workspace.zip`, particularly `WeightReal.lean`, `WeightCore.lean`, `AllIndices.lean`, and the short/long selective-growth definition and classification from `A166944/RebalancedCrossingGrowth210.lean`.

## 1. Restricted two-stage macro

Consider a true moving-horizon state \((s_0,C_0)\) with even \(C_0\) and \(X_0=2s_0-C_0\in\{0,2,4,6,8,10\}\). Follow **any number** (possibly zero) of consecutive **short selective-H events**, each with

\[
1\le g\le10,\quad 3\le e\le33,\quad e\ \mathrm{odd},\quad e-1<3(g+1).
\]

Then allow **exactly one fast event**, meaning \(e-1\ge3(g+1)\), which finishes with \(X_{\rm final}\le10\). **There must be no other event types between the initial low offset and this return.** This entire object is called a *short-fast macro* below.

## 2. New terminal offset maximum for low-start short-H strings

A complete generalized-CRT enumeration was run over all 36 initial pairs \((X_0,s_0\bmod6)\). At each prefix, all unit-gcd positions and all earlier nonunit events were rechecked modulo the full least common multiple of encountered increments. The verifier explicitly enumerates **214,780** prefix nodes, without path-length cutoff.

Beyond the prior length/growth/travel bounds, the new terminal-offset computation gives

\[
\boxed{X_{\rm short,end}\le138.} \tag{A}
\]

For the **canonical residue** root \(X_0=6,\ s_0\equiv3\bmod6\), consisting of 5,123 prefix nodes,

\[
\boxed{X_{\rm short,end}\le90.} \tag{B}
\]

Other previously established bounds remain \(H_{\rm short}\le234,T_{\rm short}\le152\) for all roots, and \(H_{\rm short}\le204,T_{\rm short}\le129\) for the canonical root.

These finite estimates overapproximate the true recurrence, because they do not require primality of the initial record or full attainment history, and extra prime divisors can only discard paths.

## 3. Arithmetic fast-return bound and extra CRT tightening

For a single fast event from offset \(X\) to offset \(X'\), the exact update is

\[
e-1=2g+(X-X'),\quad e-1\ge3(g+1).
\]

Thus \(g\le X-X'-3\) and

\[
\boxed{e\le3(X-X')-5.} \tag{C}
\]

For odd \(e\ge7\), the exact event divisibility implies \(X'\equiv0\bmod2e\) on an even hit and \(X'\equiv6\bmod2e\) on an odd hit. Hence any fast hit with \(X'\le10\) has **exactly \(X'=0\) (even hit) or \(X'=6\) (odd hit)**.

Using (A) alone gives \(e\le409\); the canonical root (B) alone gives \(e\le265\).

The finite program then appends **every arithmetically eligible fast return** to each short-only prefix, joins the full-gcd congruence for the return increment by generalized CRT, and rechecks all preceding unit and hit indices under the newly enlarged modulus. This is a complete *necessary-condition* test for every genuine macro.

| Root condition | Candidate prefixes examined | CRT-consistent candidate last hits | Entire-word projected-gcd passes | **Maximum final fast increment** |
| --- | ---: | ---: | ---: | ---: |
| All initial X≤10 | 108 high-X prefixes (X≥96) | 5,272 | 768 | **283** |
| Canonical congruence X=6,s≡3 mod6 | 5,123 prefixes (all) | 45,647 | 14,947 | **239** |

For the first row, why is it enough to check just 108 prefixes with \(X\ge96\)? If \(X<96\), its even value is at most 94, and (C) immediately gives \(e\le3(94)-5=277<283\). The exact length-214,780 prefix enumeration already covers those discarded smaller-offset cases; hence maximum 283 is global.

Consequently:

\[
\boxed{\text{Every genuine short-fast macro has final }e\le283.}\tag{D}
\]

With the canonical initial residue:

\[
\boxed{e\le239.}\tag{E}
\]

**Both maxima are sharp even for full local first-hit gcd arithmetic**, not merely for the CRT overapproximation.

- **Global e=283 witness:** synthetic \((s_0,C_0)=(124860554,249721102)\), \(X_0=6\), 17 consecutive short-H events with \(T=88\), then the fast step \((g,e)=(90,283)\), ending \((s_f,C_f)=(124860732,249721464)\), \(X_f=0\). Every intermediate gcd=1 and every stated hit exact; 18 total events.
- **Canonical-residue e=239 witness:** synthetic \((s_0,C_0)=(1703085153,3406170300)\), \(X_0=6,s_0\equiv3\bmod6\), 15 consecutive short-H events with \(T=90\), then fast \((g,e)=(77,239)\), ending \((1703085320,3406170640)\), \(X_f=0\). Every gcd checked; 16 total events. **The starting value \(M=s_0-2\) is not asserted to be a genuine A166944 record.**

The exact witness words are embedded in the executable verifier.

## 4. An actual macro has bounded H, G, T — but the macro count is open

For each complete short-fast macro:

\[
\boxed{
H_{\rm macro}=H_{\rm short}\le234,\quad
G_{\rm macro}\le234+282=\mathbf{516},\quad
T_{\rm macro}\le152+135=\mathbf{287}.
} \tag{F}
\]

The fast event is **not** part of H. For the first macro starting at the canonical residue, the corresponding bounds are \(H\le204,G\le204+238=442,T\le129+87=216\).

Suppose, conditionally, a path could be partitioned into exactly \(m\) of these macros, followed by at most one terminal short-only string, **and no long-H events and no other interruptions**. Then \(H\le234(m+1)\). Combined with the previous H-only gate \(26H\le3M-45\), this would imply Cap B whenever

\[
\boxed{6084(m+1)\le3M-45.} \tag{G}
\]

At \(M=45895573\), \(m\le22629\) is sufficient. **No upper bound on the actual number of macros is established**; this is a conditional arithmetic reduction, not a general theorem for all capped paths.

## 4b. Stronger macro lemma: **any number of consecutive fast events**

The single-fast terminal restriction is unnecessary for a **coarser but stronger-in-scope** budget. After the low-start short-H-only prefix, allow **any nonempty number \(n\)** of consecutive fast events, with no intervening H events, ending at \(X_{\rm end}\le10\).

Let the fast-tail start offset be \(Y\le138\), from (A), and let the total travel, horizon growth and offset decrease on the fast tail be \(T_F,G_F,\Delta=Y-X_{\rm end}\). Summing the fast inequality \(e_i-1\ge3(g_i+1)\) gives

\[
G_F\ge3T_F+3n,\qquad \Delta=G_F-2T_F.
\]

Consequently

\[
\Delta\ge T_F+3n\ge4n,\quad
T_F\le\Delta-3n,\quad
G_F=2T_F+\Delta\le3\Delta-6n.
\]

As \(0\le X_{\rm end}\le Y\le138\) and \(n\ge1\), the fast tail always satisfies

\[
\boxed{n\le34,\quad T_F\le135,\quad G_F\le408.} \tag{F1}
\]

Combining with the 31-step/234-growth/152-travel short-H prefix yields a **fully general short-then-fast-only return macro** (the fast tail may have 1,2,...,34 events):

\[
\boxed{\#\mathrm{events}\le65,\quad H\le234,\quad G\le642,\quad T\le287.} \tag{F2}
\]

For the **first canonical-residue root** \(X_0=6,s_0\equiv3\bmod6\), \(Y\le90\) and the sharper 26/204/129 short-H bounds imply

\[
\boxed{\#\mathrm{events}\le48,\quad H\le204,\quad G\le468,\quad T\le216.} \tag{F3}
\]

This conclusion **does not** assert that every true low-offset return consists of a short-only segment followed by a fast-only tail. A *long prime-H event*, or interleaving short-H/fast/short-H after the first fast event, breaks this macro grammar. Bounding the number and mass of such interleavings remains open.

The proofs of (F1)–(F3) use finite fact (A)/(B) plus *elementary signed offset accounting*, not another numerical graph calculation. The 283 and 239 exact **individual fast-increment** bounds in §3 apply only when the fast tail has **exactly one event**; they are **not** asserted for every event in the multi-fast case.

## 5. Why the low-start hypothesis matters: an infinite fast reset family

For **every odd \(e\ge7\)** (prime or composite), define

\[
s=3e+1,\quad C=5e-1,\quad r=s+1=3e+2,\quad C'=6e-2.
\]

Then \(C\) is even, \(s<r\le C\), and the single event has **exact** gcd

\[
\gcd(r-2,C+1)=\gcd(3e,5e)=e.
\]

There are no intervening indices. The pre- and post-offsets are

\[
\boxed{X_{\rm before}=e+3,\quad X_{\rm after}=6.} \tag{H}
\]

Since \(e-1\ge6=3(g+1)\) for \(g=1\), this is always a **fast non-H reset**. It can return arbitrarily high offsets to 6 **in one index**, even for arbitrarily large composite increments. It is an exact local first-gcd construction, not an authentic attained record path.

Thus **neither a prime-only reset argument nor a positive lower bound on the reset travel distance is possible without additional hypotheses**. The finite e≤283 result really exploits the *immediately preceding low-start short-H history*. Multi-event resets, long-prime-H resets, paths originating at already high X, and the genuine record-history constraint remain the open global challenge.

## 6. Reproduction

```sh
python3 research/cap_b_short_fast_bridge.py
```

The local execution successfully verified all expected counts and both full-gcd witnesses. The new finite bound (D)/(E) has **not been transferred to the Lean kernel**. The unrestricted Cap B lemma and the twin-prime conjecture remain unproved.
