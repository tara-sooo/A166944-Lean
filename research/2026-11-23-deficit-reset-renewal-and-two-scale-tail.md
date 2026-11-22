# A166944: deficit reset and two-scale high-event renewal strategy

Date: 2026-11-23 JST. Research Issue [#4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [#1](https://github.com/tara-sooo/A166944-Lean/issues/1); branch `research/issue-4-terminal-survivor-positive-budget`. Continues [the high-prime restart CRT study](2026-11-23-high-prime-restart-crt-and-refractory-spectrum.md). All new identities and conditional implications below are PAPER arguments; reset-manifold maxima and trajectory counts are exhaustive finite computational evidence, NOT Lean-kernel theorems. Neither twin-prime infinitude nor the stronger A166944 conjecture is proved.

## 1. Exact deficit-residue reset dichotomy (PAPER)

At the plateau of the original **parity-specific squarefree clipped** GCD recurrence, let the last event origin be t, frozen even state C, and z=2t-C>=0. At its next nonunit event n=t+delta with squarefree odd d>=3, write C'=C+d-1 and z'=2n-C'=z+2delta-d+1. In the even-time case d|n and d|C-1, so d|(z+2delta+1) and therefore **z'≡0 (mod d)**. In the odd-time case d|(n-2) and d|(C+1), so d|(z+2delta-5) and therefore **z'≡6 (mod d)**. The canonical horizon invariant gives z'>=0.

For every high event (d containing a prime >=13, thus d>=13), we have the exact dichotomy:
- RESET: even-time z'=0, or odd-time z'=6.
- CHARGED: even-time z'>=d, or odd-time z'>=d+6.

The dichotomy is mutually exclusive. At reset, **C'=2n or C'=2n-6**, irrespective of the earlier high-prime history. This is *state-space renewal*, not independence of n from previous M; arithmetic correlations in the distribution of reset origins n remain the major obstacle.

At a high event when the previous z<=146 and the increment contains a prime p>=59, the already proved pair-deficit obstruction implies d=p exactly, and the reset/nonreset alternative is the simple carry of (z+2delta+epsilon)/p. This reduces the local state after that high event to a bounded number of deficit layers j*p+epsilon (j<=5 with epsilon=0 or 6).

## 2. MUCH smaller verified finite state space after resetting

Restrict future events to primes {3,5,7,11}, whose squarefree product P=1155. If the initial plateau is a reset (t,C=2t-z) with z in {0,6}, the restricted path is determined by t mod 2310 and z. Only 4620 states need checking, as opposed to 2,668,050 arbitrary (t mod 2310,C even mod2310) states. Exhaustive enumeration gives:

| reset z | origins checked | maximum low-only events | maximum cumulative low growth | maximum encountered deficit z | maximum clock span |
|---:|---:|---:|---:|---:|---:|
| 0 | 2310 | 19 | 100 | 146 | 105 |
| 6 | 2310 | 18 | 100 | 146 | 114 |

The previous ALL-STATE low-wheel bound for cumulative growth was 1156. The new <=100 bound holds only for the restricted path **starting from an actual reset plateau** and every initial prefix of that path. The maxima in a row need not be attained by the same state. The companion standalone Python enumerator checks all 4620 residue-lifts; an independent locally compiled C++17 checker produced the same maxima with strict `-Wall -Wextra -Werror` and also checked translation by period 2310.

**Consequence (PAPER conditional on exhaustive finite certificate):** The next high event after a reset and any number of intervening low-only events satisfies z<=146. Hence it contains exactly ONE high factor p>=13; for p>=59 its *entire* increment d=p. Furthermore, if the preceding high event left a reset, the SAME high prime q cannot fire again at the next high event unless q<=101. Proof: any q>=13 that has just fired is absent from both neighbors. The total intervening low-only growth e is <=100; to regain C±1 divisibility by the same odd q, the required positive even displacement is at least q-1. Thus q-1<=e<=100.

These are **not** statements that a q can never fire again after an intervening OTHER high event.

## 3. Two-scale tail lemma: a structured alternative to full adaptive CRT

For each canonical start M and its high (factor >=13) event sequence, classify each high event as RESET or CHARGED by section 1. Define R(M)=number of RESET high events, and L(M)=maximum consecutive run length of CHARGED high events between resets, including before the first and after the last reset (0 if none). The total high-event count T(M) satisfies the deterministic bound

    T(M) <= R(M) + (R(M)+1)*L(M).                     (NR1)

For fixed alpha,beta>0 with alpha+beta<1, the following TWO estimates are sufficient but BOTH OPEN:

    #{odd M in [X,2X): R(M)>B^alpha}=o(X),
    #{odd M in [X,2X): L(M)>B^beta}=o(X).             (NR2, OPEN)

Indeed outside their union T(M)=O(B^(alpha+beta))=o(B). The older finite-11-wheel interruption lemma E_B(M)<=22+23*T(M) and growth lemma G_B(M)<=6+4B*E_B(M) yield G_B(M)=o(B^2)=o(X) uniformly over the good starts; each bad start costs G_B(M)<=3X, and o(X) such starts contribute o(X^2). Consequently W_X=o(X^2), hence infinitely many twin prime pairs by the existing squarefree-wheel terminal certificate. One possible choice is alpha=beta=0.45.

The split offers two distinct mathematical targets: bound numbers of reset epochs by the distribution of **reset origins**, and bound charged-run lengths via the **deficit carry/layer evolution**. Neither can be replaced by an assumption of uniform phase at arbitrary adaptive plateaus; earlier audits already falsified that assumption.

## 4. Finite canonical high-event reset experiment

Independent full original parity-specific squarefree-wheel event scans over EVERY odd M in each window (not sampling), comparing historical high-event totals, yield:

| X | high events T_X | RESET high events | fraction reset | RESET among FIRST high events | largest R(M) | largest L(M) |
|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 7675 | 2865 | 0.3733 | 1004 | 7 | 17 |
| 16384 | 45343 | 14422 | 0.3181 | 4260 | 12 | 35 |
| 65536 | 224221 | 73941 | 0.3298 | 17729 | 18 | 35 |

The X65536 scan contained 92,893 high events preceded by a reset-origin low-only epoch (not necessarily immediately after the reset). For every such event, z<=146, the high prime was unique, and all events with p>=59 had d=p. First high events were treated as following the initial canonical reset z=6.

This is neither a positive-density asymptotic reset theorem nor a uniform tail bound. In fact, not all high events reset; the CHARGED excursions remain serious.

## 5. More promising analytic target: distribution of reset origins, not the product of historical CRT moduli

When z in {0,6} after a high event at time t, every intervening small-wheel plateau is an affine function of t on a fixed class t mod 2310:

    C_j(t) = 2t-z + h_j(t mod 2310,z),  j<=19.

For an as-yet inactive high prime q>=13 to be active at one of these plateaus it must satisfy one of TWO linear residue conditions

    q | 2t-z+h_j(r,z)-1  or  q | 2t-z+h_j(r,z)+1.

The equations depend on the current reset origin t and low-state residue r alone, **not explicitly on the product of primes from past high events**. This suggests replacing the multiplicative-history CRT proof (which fails from the third high wave) by an arithmetic DISPERSION estimate for the actual reset-origin multiset. One must also control charged excursions separately, e.g. NR2. Merely writing the congruence does NOT establish equidistribution: t is dynamically and arithmetically selected, often divisible by the last firing prime.

A potentially useful test: partition genuine reset origins by z=0 or6, residue t mod2310, restart depth, and large-prime dyadic band. Measure weighted discrepancy of their residues mod NEW q, removing the previously fired q and the <=101 immediate-refire possibilities. Seek average large-sieve cancellation for these dynamically selected origins, or a weaker tail inequality sufficient for NR2.

Standard purely combinatorial sieve cannot simply be expected to settle twins because of Selberg's parity obstruction; the Polymath8b paper [Variants of the Selberg sieve](https://arxiv.org/abs/1407.4897) explicitly discusses its limitations. The state-dependent time-order/deficit-carry correlations would need to supply genuinely additional information, not just a conventional upper-bound sieve.

## Status and reproduction

- **Paper-level proved:** post-event deficit congruence and dichotomy; consequent reset/charged run decomposition; conditional NR2 implication and q<=101 post-reset refractory bound, using the finite reset-manifold certificate.
- **Finite exhaustive:** 2310 residues for each reset z, independent original-GCD scans X4096,16384,65536; not a Lean kernel check.
- **OPEN:** two NR2 tail bounds, arithmetic dispersion of adaptively generated reset origins, high-deficit charged-run drift, original twin-prime and stronger A166944 conjectures.

To reproduce finite reset-manifold calculation: `python3 research/reset_manifold_audit.py`. A separate C++17 original-GCD scan was used for the canonical high-event percentages and new per-event assertions. Prior full-wheel verifier: [restart_epoch_audit.cpp](restart_epoch_audit.cpp). The X65536 high-event count 224221 matches the prior pinned regression. No merge to main.
