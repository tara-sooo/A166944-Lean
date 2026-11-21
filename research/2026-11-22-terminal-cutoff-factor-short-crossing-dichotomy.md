# A166944 terminal-cutoff factor obstruction: an exact short-hit / canonical-return dichotomy

2026-11-22 JST. **Research status:** two new paper lemmas (exact factorized first-hit map and post-cutoff short-hit vs canonical-return dichotomy), a direct finite C++ audit of 499,997 **artificial** canonical-shaped starts, and an independent direct-gcd cross-check. This is **not** a proof of Cap B or twin-prime infinitude; new lemmas have **not** been compiled in Lean.

Sources: the original user-provided `A166944-Lean.zip`, specifically `mission_scan/twin_proof/cap_bound/CapSampleExact.lean` (`cap_iff_twins_at_cutoff`), `mission_scan/twin_proof/cap_bound/AllIndices.lean` (`first_hit_bound`, `twins_of_slow_interval`), `mission_scan/twin_proof/index_window/ConditionalIndexCheck.lean` (`no_internal_new_record_of_relaxed_index`), and [`A166944/Lemmas.lean`](../A166944/Lemmas.lean). Preceding [high-growth terminal F-envelope note](2026-11-22-high-growth-terminal-f-envelope.md) proved that the slow route is equivalent to a sufficiently long terminal unit suffix.

## 1. The exact prime-factor formula for the NEXT nonunit hit

Let a local state after index `s>=2` have even horizon `C>=6`. Until the next nonunit event, the parity-dependent gcd is

`d(r)=gcd(r,C-1)` for even `r>s`; `d(r)=gcd(r-2,C+1)` for odd `r>s`.

For each odd prime `p|C-1`, let

`j_minus(s,p) = s + (((-s) mod (2*p)) or (2*p)).`

This is the first **even multiple** of p strictly after s. For each odd prime `p|C+1`, let

`j_plus(s,p) = s + (((p+2-s) mod (2*p)) or (2*p)).`

This is the first **odd** index r>s with `r-2=0 mod p`.

**Exact next-hit theorem (paper):**

`J(s,C)=min( min_{p prime|C-1} j_minus(s,p), min_{p prime|C+1} j_plus(s,p) ).`   (1)

The next event is at exactly `J(s,C)`, with the gcd of the appropriate parity as its increment. The proof is a two-way divisibility implication: a nonunit gcd has an odd prime divisor of the appropriate horizon neighbor, and each such prime forces its first hit at its listed congruence index. This is an **exact** first-hit map, not a necessary-only congruence filter.

For any prime p in the candidate set, `0<J(s,C)-s<=2*p`. If either C−1 or C+1 is composite, its least proper prime factor q satisfies `q<=isqrt(C+1)`; therefore

`J(s,C)-s <=2*q<=2*isqrt(C+1).`                           (2)

Conversely, when **both C−1 and C+1 are prime**, and `s<=C`, the first possible even hit is at `2*(C-1)`, while the first possible odd hit is at `C+3`. For even C>=6, `C+3<2*(C-1)`, so

`boxed: J(s,C)=C+3,  d(C+3)=C+1.`                           (3)

At that event, the horizon updates to `2*C`; writing `M'=C+1`, the resulting state is **again canonical-shaped**:

`(s',D(s'))=(M'+2,2*M'-2).`                                  (4)

This renewal algebra holds for any synthetic or actual local state at which (3) applies; it does not prove that the original recurrence reaches a twin state.

## 2. Exact cutoff dichotomy at an ACTUALLY attained record

Assume `M>=968` is a genuinely attained canonical record, let

`s0=M+2, K=floor((7*M-1)/4), C=D(K), t=isqrt(C+1).`

Existing Lean bounds give `2*M-2<=C<=2*K`, and elementary arithmetic gives

`K+2*t<=2*M`, `K+2*t<=C` (for M>=968).

For instance `C-K>=2*M-2-K >= (M-7)/4`, while
`2*t<=2*sqrt(2*K+1)<=sqrt(14*M+2)`; the first lower bound exceeds the final upper bound for M>=238.

Let `J` denote the **next nonunit event strictly after K**. Apply (1) to `(K,C)`.

- **GOOD / canonical-return branch.** If C−1,C+1 are prime, then
  `J=C+3>=2*M+1`, `d(J)=C+1>M`,
  and the post-event state is `(C+3,2*C)`.
- **BAD / short-crossing branch.** If either neighbor is composite, then
  `boxed: K<J<=K+2*t<=C`, hence `J<=2*M`.             (5)

Moreover the short-crossing event necessarily has `d(J)<=M`. Proof: at even J, the increment is odd, divides the even J and cannot equal J, so `d(J)<=J/2<=M`. At odd J, let e=d(J). If e>M, then `e|J-2<2*M<=2*e` implies `e=J-2`. Since C+1 is an odd multiple of e strictly larger than e, `C+1>=3*(J-2)>2*K+1>=C+1` (J>K, K>4), contradiction. Thus

`boxed: J<=2*M and d(J)<=M` on the short-crossing branch.   (6)

So the next event is **either** a small, old-record-bounded event within O(sqrt M) after K **or** the canonical next record at C+3. There is no possible next nonunit hit in the wide gap `(K+2*t,C+2]`.

This is an exact reformulation of a critical first-hit obstruction. The existing Lean theorem `CapWeight.Sample.cap_iff_twins_at_cutoff` identifies the GOOD branch with Cap B for genuinely attained M>=968. **The BAD branch has NOT been ruled out for unbounded attained M.**

## 3. Factor-window refinement: what a last event near K would force

Let S<=K be the last nonunit event and C=D(S)=D(K), with L=K-S. Suppose a horizon neighbor is composite and let q be its least proper prime divisor. Then the exact map from S gives

`L < J-S <=2*q<=2*t`.

Thus, writing `delta=J-K>0`,

`boxed: L+delta<=2*q<=2*t,  L/2<q<=t.`             (7)

This gives a quantitative **cutoff-straddling factor certificate**: if the last event was already close to the slow threshold `L≈2*t`, then the next event must lie very soon after K, and q must lie close to sqrt(C+1). It also explains the eight-index boundary in the previous slow-envelope analysis.

An additional exact refinement substitutes `P(t)`, the greatest odd prime <=t (when t>=3), in place of t in (2), (5), and (7). It can improve the forced-hit window if t lies in a prime-free gap. It does **not** establish a uniform absence of short crossings.

## 4. Fully reproducible finite scan, and its logical scope

[terminal_cutoff_factor_audit.cpp](terminal_cutoff_factor_audit.cpp) implements (1) by complete exact integer prime factorization, and checks 1,098 independent **direct per-index gcd** trajectories for odd artificial starts M=7,...,2201. The factorized and direct traces agree in all events, last hit, and terminal horizon.

Then it exhaustively scans **all 499,997 odd integers M from 7 through 1,000,000**, each with the **artificial initial assignment** `(s,C)=(M+2,2*M-2)`, replays its exact local first hits through K, and checks (1)-(3) and the terminal F-envelope. Results:

- 38 synthetic windows fail the slow condition; the largest such M is 365.
- Exactly 9 synthetic windows have a terminal non-twin pair `C-1,C+1`: M=11,13,23,25,39,41,43,45,305. The largest failure is M=305.
- Thus **every synthetic odd start M in [307,1,000,000] yields twin primes at its cutoff in this FINITE scan.** This is **NOT** a theorem for all M, nor a claim that those M are attained A166944 records.

The distinctions matter. At synthetic M=365, terminal C=1020 gives genuine twin primes 1019,1021 while **no slow interval** exists: last event S=570, K=638, L=68, t=31, and 4L=272<280=32+8t. Thus the slow-interval sufficient test misses some true terminal twin pairs.

At actually attained small record M=43, K=75, C=132, and the next event is J=79 with increment 7, since 7 divides C+1=133. This is a real short-crossing example (but M<968).

**Self-renewing prime generator, CONDITIONAL:** If the apparent synthetic terminal-primality property could be proved for **every** odd M>=307, then choosing any such M and iterating the exact renewal map `M'=D(K)+1` would generate a strictly increasing infinite sequence of twin primes (M'−2,M'); (4) returns to a canonical-shaped state, and `M'>M`. This would prove twin-prime infinitude. The finite scan supplies NO proof of that universal property.

## 5. What is still mathematically missing

The next-hit map and the dichotomy eliminate ambiguous postcutoff behavior, but do NOT eliminate the **short-crossing branch**. The situation is sharper than merely a long or short terminal unit suffix:

`boxed: (Cap B fails at attained M>=968) iff the next event after K occurs within 2*isqrt(D(K)+1) indices, with increment <=M.`

The right-to-left implication invokes the previously verified Lean `cap_iff_twins_at_cutoff` and (1)-(3); it is not a stand-alone elementary implication for arbitrary artificial starts.

Hence the missing global input is an asymptotic theorem excluding this precise **near-cutoff small-increment crossing** on sufficiently many genuinely attained canonical records, or a direct proof of the terminal twin pair. The early real M=43 crossing and arbitrarily constructed local endpoint states demonstrate that immediate first-hit divisibility is compatible with the bad branch. The exhaustive synthetic finite success up to 1,000,000 is powerful experimental guidance but not a proof of the asymptotic exclusion.

**Reproduction:** `c++ -O3 -std=c++17 research/terminal_cutoff_factor_audit.cpp -o /tmp/terminal-audit && /tmp/terminal-audit 1000000`. The program ran successfully in the local container (~6 seconds), with direct-gcd cross-check and stated totals. The note and C++ code were persisted and read back from GitHub. No new Lean kernel build and no proof of twin primes.
