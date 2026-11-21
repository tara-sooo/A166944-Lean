# Cap B continuation: direct low-offset returns, rough horizons, and sharp long-prime drift

2026-11-22 JST. **Status:** new paper lemmas derived from the exact first-hit arithmetic and the Lean-proved `large_relative_gap_cases` / `units_lt_twice_factor`, backed by executable finite checks; **no new Lean kernel compilation; Cap B and twin-prime infinitude remain open.**

Executable audit: [`cap_b_longH_roughness_audit.py`](cap_b_longH_roughness_audit.py). It imports the already committed [`cap_b_interleaved_return_audit.py`](cap_b_interleaved_return_audit.py) for the two previously certified local event traces. The executable was run locally from the actual source, and the 5,589-byte script was committed and fetched back with matching length, FNV-1a `225006b2`, and full-string comparison. Exact source basis includes the user-uploaded `workspace.zip` files `mission_scan/twin_proof/cap_bound/AllIndices.lean`, `WeightReal.lean`, `canonical_toll.md`, and the public repository's `A166944/RebalancedCrossingGrowth210.lean`, `ReplayOffset210.lean`.

## 1. A sharp 35% drop bound for **long** selective-H prime events

For a moving-horizon event with gap \(g>10\) and increment \(e=p\) counted by the selective-growth variable H, the existing Lean theorem `large_relative_gap_cases` proves \(p\) is prime. Put \(h=p-1\). Membership in H says \(h<3(g+1)\), hence \(g\ge\lfloor h/3\rfloor\).

If \(p\equiv1\bmod6\), write \(h=6k\). Then \(g\ge2k\), giving \(40g\ge80k\ge78k=13h\).

If \(p\equiv5\bmod6\), write \(h=6k+4\). For \(k\ge6\), \(g\ge2k+1\), hence \(40g\ge80k+40\ge78k+52=13h\). For \(k\le5\), primality forces \(p\le29\), and \(g\ge11\) gives \(40g\ge440>13h\). For \(p=3\), the claim is immediate.

Therefore **for every genuine long H event, with no bound on its prime value or starting offset,**

\[
\boxed{40g\ge13(p-1),\qquad
X_{\rm after}-X_{\rm before}=2g-(p-1)\ge-\frac7{20}(p-1).} \tag{1}
\]

The coefficient 7/20 is **sharp in full local first-gcd arithmetic**: \((s,C)=(479,780)\), \(g=13\), \(p=41\), \(r=492\). Every intervening gcd is one, \(\gcd(492,779)=41\), and \(X:178\to164\), a drop of 14 out of \(p-1=40\).

For **short H** events (\(g\le10\)), the best uniform drift loss remains \(\le h/2\), from \(h<3(g+1)\implies h\le4g\). For **fast/non-H** events, any loss is \(\le h\). Thus every actual interval, whatever the interleaving, satisfies the **sharp split-class ledger**

\[
\boxed{
X_f\ge X_0-F-\frac12 H_s-\frac7{20}H_l,
} \tag{2}
\]

where \(F\) is fast growth, and \(H_s,H_l\) are short-H and long-prime-H growth.

## 2. Improved completed / unfinished up-jump ledger

Select disjoint excursions initiated by a long-H prime \(p\ge13\) at low offset \(X\le10\) that lands at \(X'\in\{2p,2p+6\}\). Each excursion ends at its first subsequent \(X\le10\), or remains unfinished at the terminal endpoint. Let \(J=\sum(p-1)\) over initiating events, \(N\) count them, \(G=F+H_s+H_l\) be whole-path growth.

Each excursion needs a subsequent offset reduction of at least \(2p-10\). By (2), a completed excursion costs

\[
F_{\rm after}+\tfrac12H_{s,\rm after}
+\tfrac7{20}H_{l,\rm after}\ge2p-10.
\]

For the at-most-one unfinished final excursion add \(\max(0,X_f-10)\) to the left. The following event intervals are disjoint and exclude all initiating jumps, which already contribute \(J\subseteq H_l\). Summing yields:

\[
\boxed{
47J\le20G-10H_s-13H_l+160N+
20\max(0,X_f-10).
} \tag{3}
\]

When all excursions are completed, the terminal-offset term is zero. This replaces the preceding (weaker) split-blind ledger \(5J\le2G-H+16N+2\max(0,X_f-10)\).

The independent local first-gcd audit checks the two known record starts:

| Record-shaped M | jump J | N | H short | H long | LHS \(47J\) | RHS of (3) | slack |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 45,895,573 | 72 | 1 | 72 | 694 | 3,384 | 28,698 | 25,314 |
| 5,875,882,249 | 30,168 | 2 | 72 | 30,298 | 1,417,896 | 1,422,326 | 4,430 |

The second case includes one unfinished excursion with final \(X_f=60,276\). The new normalized slack 4,430 is below the preceding bound's slack \(482\cdot20=9,640\). The new estimate charges long-H *return* events more tightly; it does not charge every H event as an initiating low-offset jump, so a global H upper bound remains open.

## 3. A general hierarchy: long first-hit gaps force **almost-twin-prime horizons**

Let \(s<C=D(s)\) and \(r=s+g\) be the first nonunit gcd hit. For every odd prime divisor \(q\mid(C-1)(C+1)\), the existing `AllIndices.units_lt_twice_factor` lemma applied to the \(g-1\) preceding unit indices gives

\[
g-1<2q,\qquad\text{thus}\quad \boxed{q\ge g/2}. \tag{4}
\]

Fix an integer \(k\ge2\). If

\[
\boxed{g^k>2^k(C+1),} \tag{5}
\]

then every prime factor of each of \(C-1,C+1\) is larger than \((C+1)^{1/k}\). Either neighbor therefore has at most \(k-1\) prime factors counted **with multiplicity**, since \(k\) factors would have product exceeding \(C+1\).

- \(k=2\): both horizon neighbors are prime, recovering the familiar slow/quiet factor obstruction.
- **\(k=3\):** both horizon neighbors are *prime or semiprime* (i.e. at most two prime factors counted with multiplicity). This is a new intermediate **almost-twin-prime** barrier usable for any first hit, including one starting at high offset.

This is not a theorem saying infinitely many twin-prime or almost-twin-prime pairs exist. It characterizes horizons **when a long first-hit gap actually occurs**.

## 4. Strong direct-low return restrictions at the official cutoff

Suppose a long H prime \(p\ge13\) starts at \(0\le X\le10\) and **directly returns low**: \(X'\le10\). Exact event divisibility forces \(X'=0\) with an even hit, or \(X'=6\) with an odd hit. The exact gaps are

\[
g=\tfrac{p-1-X}{2}\quad(\text{even},X'=0),
\qquad
g=\tfrac{p+5-X}{2}\quad(\text{odd},X'=6),
\]

so always \(g\ge(p-11)/2\).

For the official threshold \(M=45,895,573\), any hypothetical capped prefix has \(C\le2K=160,634,504\), \(K=80,317,252\). A direct-low event with \(p\ge2189\) satisfies

\[
g^3\ge((p-11)/2)^3 >8(2K+1)\ge8(C+1).
\]

By §3, **both \(C-1\) and \(C+1\) must be prime or semiprime**. Moreover, the hit side contains \(p\), and the existing \(gp\le2(C+1)\) bounds \(p\le25,353\), while \(C-1\ge91,791,143\). Consequently that hit side is **exactly a semiprime \(p\,q\), with \(q\) prime**.

The hit parity forces the cofactor \(q\) modulo four:

\[
\boxed{
\begin{cases}
C-1=pq,\quad q\equiv3\bmod4 &\text{even hit},\\
C+1=pq,\quad q\equiv1\bmod4 &\text{odd hit}.
\end{cases}
} \tag{6}
\]

Indeed in the first branch \(r=p(q+1)/2\) must be even; in the second, \(r-2=p(q+1)/2\) must be odd. These conditions are verified with **full gcds**, not merely modulo-30 candidates.

The semiprime barrier is *not vacuous*. Two exact **synthetic local** direct-low first hits with the **canonical start residue** \(X=6,s\equiv3\bmod6,C\equiv0\bmod12\), and with \(C\) in the official cutoff's numerical range, are:

| Pre-state (s,C) | gap | p | post X | \(C-1\) factorization | \(C+1\) |
| --- | ---: | ---: | ---: | --- | --- |
| (45,896,517; 91,793,028) | 1,103 | 2,213 | 0 | \(2213\cdot41479\) | prime |
| (46,093,527; 92,187,048) | 1,107 | 2,221 | 0 | \(2221\cdot41507\) | prime |

Both real local first hits pass each intervening gcd=1 test. Neither state is claimed to equal the actual A166944 \(D(s)\) nor to belong to the true capped replay.

## 5. A small wheel brake: successive direct long hits force p ≡ 1 (mod 12)

A canonical state starts at \(X=6,s\) odd, hence \(C=2s-6\equiv0\bmod4\). A return-compatible low state after an \(e\ge7\) hit has either \(X=0,s\) even or \(X=6,s\) odd; in **both** cases \(C\equiv0\bmod4\).

Therefore **any one-step direct transition between these reset-compatible low states** must have

\[
C'=C+(e-1)\equiv0\bmod4
\quad\Longrightarrow\quad
\boxed{e\equiv1\bmod4}. \tag{7}
\]

For two successive *long-gap* events, \(g_i,g_{i+1}>10\), the first-hit divisor-3 bound forces both pre-horizons \(C_i,C_{i+1}\) divisible by 3 (otherwise a 3-hit appears within six indices). Since \(C_{i+1}=C_i+(p_i-1)\), this forces

\[
\boxed{p_i\equiv1\bmod3}. \tag{8}
\]

Together, if the first event is a direct low reset and **the next event is also long**, its increment necessarily satisfies

\[
\boxed{p_i\equiv1\bmod12}. \tag{9}
\]

If instead \(p_i\equiv5\bmod12\), the next hit is at gap at most 6. The exact synthetic local chain \(13\to37\to29\) at start \((27543,55080)\) illustrates this: the first two primes are 1 mod 12, and after 29 (5 mod 12) the next hit has gap 1 and increment 3.

## 6. No-go theorem: arbitrarily large direct H with **zero** offset drift in local arithmetic

For each sufficiently large prime \(p\equiv1\bmod4\) construct **an integer M, not required prime or attained**, satisfying:

- \(M\equiv1\bmod6\);
- \(2M-1\equiv0\bmod p\), i.e. \(M\equiv(p+1)/2\bmod p\);
- \(M\equiv0\bmod q\) for every prime \(5\le q\le p+4\), \(q\ne p\).

The moduli are coprime, so ordinary CRT gives arbitrarily large positive solutions \(M\). Set

\[
s=M+2,\quad C=2M-2,\quad g=(p-1)/2>10,\quad r=s+g.
\]

Because \(p\equiv1\bmod4\), \(g\) is even and \(r\) odd. At the desired hit,

\[
d(r)=\gcd(r-2,C+1)
=\gcd(M+g,2M-1)
=\gcd(2g+1,2M-1)=p.
\]

At all earlier odd-index tests, the candidate factor divides \(2g'+1<p\); at earlier even-index tests, it divides \(2g'+7\le p+4\). By the CRT conditions, the respective horizon neighbor has **no** common factor at any of those preceding indices (prime 3 is excluded by \(M\equiv1\bmod6\), all other eligible primes \(q\ne p\) by \(M\equiv0\bmod q\); \(p\) divides only \(C+1\)). Hence this is a **genuine local first nonunit gcd hit**, and its post-offset is

\[
\boxed{X_{\rm before}=X_{\rm after}=6,\qquad H=p-1.}\tag{10}
\]

There exist arbitrarily large primes 1 mod 4 (an elementary classical fact), so the amount H in **one** direct-low long event can be unbounded while *offset drift is exactly zero*. The script verifies p=37,41,61,73,97,109,157, with increasing CRT initial integers.

**Crucial limitation:** these constructed M are composite (indeed multiples of 5), and **not** genuine attained twin-prime records. This does not refute \(H\le(3M-45)/26\) for actual canonical records, because the constructed M is enormous relative to p. It shows that **an offset-only potential cannot bound direct-low H based solely on the local first-hit rule**. Authentic record history, or a global arithmetic packing theorem for the visited rough/almost-twin-prime horizons, remains indispensable.

## 7. Status and exact next obstruction

We have (1) a sharp loss coefficient for high-origin long-H events, (2) a stronger completed/unfinished excursion ledger, (3) a general roughness/almost-prime hierarchy, and (4) arithmetic congruences restricting consecutive large direct returns. All apply to genuine first-hit segments, and their finite diagnostics have been reproduced.

The missing global assertion is now concrete: **the actual attained-record replay cannot visit an enormous weighted number of low-offset rough/semiprime horizons in succession, or else its high-origin H contributions must be compensated by fast growth / terminal offset sufficiently to prevent Cap B.** Neither statement is currently proved. The direct-return CRT family shows why purely local offset bookkeeping cannot close this gap.
