# Cap B: a mod-2310 terminal-excursion barrier and a sharper prime-debt cutoff

Date: 2026-11-21 JST. **Status: finite arithmetic certificate plus paper-level reductions, NOT a Lean kernel proof and NOT a proof of Cap B.**

Full reproducible C++17 source: [`cap_b_terminal_excursion_2310.cpp`](cap_b_terminal_excursion_2310.cpp). From repo root:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -pedantic \
  research/cap_b_terminal_excursion_2310.cpp -o /tmp/cap_b_terminal_excursion_2310
/tmp/cap_b_terminal_excursion_2310
```

The program constructs the finite residue graph, verifies **every** required graph-edge inequality, confirms acyclicity, checks the low-offset exception search, and replays three actual canonical post-record segments using unclipped first-gcd hits. It exits nonzero if any assertion fails. The mathematical bridge from these finite computations to all genuine event steps is explained below. The repository's established Lean inputs include `moving_horizon_step_gap_le_twice_increment_factor` and `moving_horizon_step_gap_mul_increment_le_twice_horizon` in `CanonicalGrowth.lean`, and the first-hit/offset normal forms in `ReplayOffset210.lean`.

## 1. Mod-2310 graph and a new coefficient-two potential

Use \(N=2310=2\cdot3\cdot5\cdot7\cdot11\). Every genuine moving-horizon state has even \(C\); the finite state is \((s\bmod N,C\bmod N)\), hence \(2310\cdot1155=\mathbf{2,668,050}\) states.

For each state, compute the *first clipped* gcd hit by considering the prime factors \(3,5,7,11\) of \(N\). A hit from any of these primes necessarily occurs within 22 indices if it occurs at all. At even \(r\), the clipped gcd is \(\gcd(r,C-1,N)\); at odd \(r\), it is \(\gcd(r-2,C+1,N)\). If the first clipped gcd equals one of \(e\in\{3,5,7,11\}\), create the unique forced edge

\[
(s,C)\ \longrightarrow\ (r,C+e-1)\pmod N,\qquad
w=g-2(e-1),\quad g=r-s.
\]

If the first clipped gcd is composite, there is no forced small-prime edge. A genuine event of increment \(e=3,5,7,11\) **must** follow exactly its associated forced edge: an earlier clipped nonunit gcd would have been a genuine earlier nonunit gcd, and at the actual event the clipped gcd equals \(e\).

The finite verifier reports:

| Parameter | Result |
| --- | ---: |
| Residue states | 2,668,050 |
| Forced small-prime transitions | 2,230,860 |
| Directed cycles | **0** |
| Maximum length of a forced small-prime path | **22 transitions** |
| Maximum nonnegative weight-to-terminal potential \(W\) | **9** |
| Maximum \(W(M+2,2M-2)\) for \(M\bmod6=1\) | **3** |

Here \(W\) is defined by backward dynamic programming on the acyclic functional graph,

\[
W(u)=\max(0,w(u\to v)+W(v))
\]

at a vertex with an outgoing edge, and \(W=0\) at sinks. Thus for all forced small-prime steps,

\[
\boxed{g+W(r,C')\le2(e-1)+W(s,C).} \tag{1}
\]

In particular, **a genuine moving-horizon path cannot contain more than 22 consecutive increments drawn from \(\{3,5,7,11\}\)**, regardless of its initial residue state. This is conditional on the compiled finite certificate being sound; no new Lean theorem is asserted.

**All composite increments are paid too.** If \(e\) is an odd composite, let \(f\ge3\) be its smallest prime divisor. Then \(e\ge f^2\) and the already-Lean-proved first-hit factor bound gives \(g\le2f\). Because \(0\le W\le9\),

\[
g-2(e-1)+W_{\rm after}-W_{\rm before}
\le2f-2(f^2-1)+9
=11+2f-2f^2\le-1. \tag{2}
\]

Thus (1) holds for **every composite increment** as well as \(3,5,7,11\).

For a prime event \(p\ge13\), define

\[
b^{(2)}=\max(0,g-2(p-1)+W_{\rm after}-W_{\rm before}).
\]

Since \(g\le2p\), \(b^{(2)}\le2+9=\mathbf{11}\). Telescope along any canonical capped path. With \(T=s_f-(M+2)\), \(G=C_f-(2M-2)\), and \(N_{\ge13}\) the number of prime-increment events \(p\ge13\), the certificate and the existing fact \(M\bmod6=1\) imply

\[
\boxed{T\le2G+3+\sum b^{(2)}
       \le2G+3+11N_{\ge13}.} \tag{3}
\]

This counts exceptions in **units per event**, rather than charging up to \(O(\sqrt C)\) for a large prime event as in the preceding mod-210 positive-debt potential. It is a new alternative accounting route, not a substitute for a global \(G\) bound.

## 2. A congruence barrier: there is no exceptional debt from \(X\le10\)

Put \(X=2s-C\ge0\), which is even in every genuine state. If a prime \(p\ge13\) has **positive** coefficient-two debt, \(b^{(2)}>0\), then \(W_{\rm after}-W_{\rm before}\le9\) forces

\[
g\ge2p-10,\qquad h:=2p-g\in\{0,\ldots,10\}. \tag{4}
\]

At an even hit \(p\mid r\), \(p\mid C-1\), and \(2r=C+X+2g\). Therefore

\[
p\mid X+2g+1,\qquad\text{equivalently } p\mid X-(2h-1). \tag{5e}
\]

At an odd hit \(p\mid r-2\), \(p\mid C+1\), and

\[
p\mid X+2g-5,\qquad\text{equivalently } p\mid X-(2h+5). \tag{5o}
\]

The shifts in (5e)/(5o) are odd integers between \(-1\) and \(25\). For even \(X\in\{0,2,4,6,8,10\}\), each difference is a **nonzero odd integer of absolute value at most 25**. Hence **no prime \(p\ge29\) can generate positive debt from \(X\le10\)**.

The only remaining primes are \(p=13,17,19,23\). Exhaustive mod-2310 computation uses the parity of \(C/2310\), the 22-step small-prime clipped first-hit cutoff, both parity-specific congruences (5e)/(5o), and every possible \(h\in[0,10]\). It checks **3,255 arithmetic candidates** and finds zero positive costs. This *overapproximates* true first-hit events because the full gcd is not imposed for each candidate. Consequently, for **every genuine event**, even with an increment not dividing 2310,

\[
\boxed{
X(s,C)\le10\ \Longrightarrow\
g+W(r,C')\le2(e-1)+W(s,C).
} \tag{6}
\]

Thus from a low-offset state there are **no unpaid prime exceptions at all**. This is a finite-arithmetic paper implication, not yet kernel-checked.

For primes \(p\ge29\) and positive \(b^{(2)}\) at an arbitrary offset \(X\), the same congruence gives the *seeding constraint*

\[
\boxed{X\ge p-1.} \tag{7}
\]

Indeed \(X-(2h-1)\) or \(X-(2h+5)\) is an odd nonzero multiple of \(p\). If \(0\le X<p-1\), its absolute value would be less than \(p\), because the possible shifts lie in \([-1,25]\), contradiction. Large-prime exceptions cannot begin while the offset is still small.

## 3. An integer bound on growth of the offset in any one event

No finite-state table is needed here. The known event inequalities are

\[
g\le2e,\quad ge\le2(C+1),\quad \Delta X=X'-X=2g-(e-1).
\]

Let \(R\ge1\) be an integer with \(C+1\le R^2\). If \(e\le R\), then \(\Delta X\le3e+1\le3R+1\). If \(e\ge R\), then \(gR\le ge\le2R^2\) implies \(g\le2R\), hence \(\Delta X\le4R-e+1\le3R+1\). Thus

\[
\boxed{\Delta X\le3\lceil\sqrt{C+1}\rceil+1.} \tag{8}
\]

This also applies to any prefix whose horizon is bounded above by a common \(C\).

## 4. How long must a first Cap B violating *terminal excursion* be?

Suppose a capped canonical event \((s,C)\to(r,C')\) is the **first** one crossing
\(K=\lfloor(7M-1)/4\rfloor\), so \(s\le K<r\), and put \(G=C-(2M-2)\). Then \(C=D(K)\), since the increments from \(s+1\) through \(K\) are all 1.

Choose \(R=\lceil\sqrt{C+1}\rceil\). The last-event gap satisfies \(g\le2R\), so \(s\ge K+1-2R\). Write \(t\) for the **last prefix state with \(X(t)\le10\)**; it exists because the canonical origin has \(X=6\). If \(q\) events lie strictly after that state and end at predecessor \(s\), (8) gives

\[
X_s\le10+q(3R+1).
\]

But

\[
X_s=2s-C
\ge2K-2M+4-G-4R.
\]

Therefore any first crossing must satisfy

\[
\boxed{q(3R+1)\ge2K-2M-6-G-4R.} \tag{9}
\]

At \(M=45,895,573\), if \(G<3M/8\), then \(G\le17,210,839\), \(C+1\le109,001,984\), \(R\le10,441\), and (9) yields

\[
\boxed{q\ge1,648.} \tag{10}
\]

That is: **a first Cap B failure at the platform threshold with small horizon growth needs at least 1,648 consecutive first-hit events after the last \(X\le10\) state, without returning to \(X\le10\)**. Combined with the 22-run small-prime bound, this suffix requires at least \(71\) events whose increments lie **outside** \(\{3,5,7,11\}\). This is a *necessary* condition only; it does not rule out such an event sequence.

## 5. Large-offset counterexample to an overstrong square-root increment claim

The condition \(p^2\le C+1\) is **false** for positive prime debt events on long excursions. The verifier independently checks the genuine local first hit

\[
(s,C)=(296451300,\ 592874280)
\to
(r,C')=(296483776,\ 592905370),
\quad e=p=31091,\quad g=32476.
\]

Its offsets are \(X=28320\), \(X'=62182\). In the earlier mod-210 coefficient-one potential, the event has positive debt \(1386\), yet

\[
p^2=966650281>592874281=C+1.
\]

Indeed \(C-1=19069\cdot31091\) and \(C+1=592874281\) is prime; a full-gcd scan confirms that every index \(s<j<r\) is unit and \(d(r)=31091\). This example is a local first-hit event arising after a synthetic initial-shaped path, **not an authenticated difference-record history**, and not a Cap B counterexample.

The exact replacement for the false bound is offset-dependent: the existing Lean theorem `moving_horizon_step_index_offset_reset` in `ReplayOffset210.lean` implies, for any \(e\ge5\) event that does **not** return to \(X'=0\) or \(6\),

\[
\boxed{3e^2\le e(X+1)+4(C+1).} \tag{11}
\]

This explains why large \(X\) allows \(e^2>C+1\), and why square-root bounds based only on \(C\) cannot control an unfinished excursion.

## 6. Reproducible controls and remaining Cap B gap

The C++ verifier reports:

```text
PASS: every prime>=13 event from X<=10 has nonpositive 2-growth debt; finite candidates=3255
PASS: mod=2310 states=2668050 small-prime-edges=2230860 max_run=22 Wmax=9 canonical_Wmax=3
M=5419 steps=9 T=75 G=54 Wstart=3 debt=0 prime>=13_events=1 small_events=8 composite_events=0
M=45895573 steps=37 T=957 G=1914 Wstart=0 debt=0 prime>=13_events=14 small_events=22 composite_events=1
M=5875882249 steps=26 T=45417 G=30564 Wstart=3 debt=0 prime>=13_events=5 small_events=18 composite_events=3
PASS: local first-hit counterexample to p^2<=C+1 without low-offset assumptions
PASS: first crossing with G<=3M/8 at M=45895573 requires >=1648 consecutive events since the last X<=10 state
Cap B remains open.
```

The stronger coefficient-two potential pays *all events* on these **three finite control segments**, but in general synthetic first-hit histories can contain positive \(b^{(2)}\) at primes \(p\ge13\); the universal bound still needs the exception term in (3). Moreover, large \(X\) can arise on segments with zero coefficient-two debt, because the \(2G\) term alone permits offset growth up to \(3G+12\). Thus the remaining principal mathematical obstruction is an upper bound for **the authentic terminal high-offset excursion and/or its horizon growth**, not merely the number of prime exceptions.

The gap to Cap B remains substantial. Neither (3), (6), nor (9) excludes arbitrarily long terminal excursions, and the user-facing theorem \(4s_f\le7M-1\) is **not proved**.
