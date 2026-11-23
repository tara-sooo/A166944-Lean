# A166944: exact double-quantized deficit carry, three-seed reset normal form, and a prime-only return barrier

Date: 2026-11-23 JST. Research branch `research/issue-4-terminal-survivor-positive-budget`, Issue #4 (parent #1). Extends the actual parity-specific squarefree clipped-GCD recurrence work, most recently `2026-11-23-distinct-prime-shift-orthogonality-and-large-sieve-gap.md` and the previously verified arbitrary 11-low-wheel growth bound 1156.

**Scope:** the algebra below is proved on paper; the finite maxima are 2310-residue exhaustive computations with the committed independent actual-step-GCD checker `research/three_seed_reset_audit.py`. No new Lean-kernel proof; twin primes and the stronger A166944 record theorem remain open.

## 1. Stronger carry identity (paper)

At a plateau origin (t,C), write z=2t-C (even, nonnegative). Let the next nonunit event be at n=t+delta, with odd squarefree clipped increment d>=3, state C'=C+d-1 and z'=2n-C'=z+2delta-d+1, also even. The ORIGINAL even clock has d|gcd(n,C-1), hence d|(z+2delta+1) and d|z'. The ORIGINAL odd clock has d|gcd(n-2,C+1), hence d|(z+2delta-5) and d|(z'-6).

Because d is ODD and z',z'-6 are EVEN, the quotient in either divisibility is EVEN. For an event with d>=13, z+2delta-5>=-3 so it cannot be a negative nonzero multiple of d. Thus with integer k>=0:

    BOXED: even event z'=2*k*d; odd event z'=6+2*k*d.     (CARRY)

Therefore any nonreset event with d>=13 leaves z'>=2d (even) or z'>=2d+6 (odd), rather than the previously recorded weaker d/d+6. For low event d=3 at odd n the exceptional k=-1 can occur and is NOT included in the high-event statement.

## 2. Normalize EVERY high reset to THREE odd-time seed deficits (paper)

High RESET means z'=0 at even event time or z'=6 at odd event time. Let that event time be t.

- ODD reset: C=2t-6; this is EXACTLY canonical initialization at s=t=M'+2 for the new odd parameter M'=t-2, C=2M'-2. The original trajectory is a prefix of this new canonical trajectory, truncated at its OLD K(M), because K(M')>=K(M).

- EVEN reset: C=2t and t even. Direct inspection of the next THREE original parity-specific GCD steps (t+1 odd, t+2 even, t+3 odd) uses only primes 3 and 5 (no high prime can fire). The only possible triples of increments are

      (d_(t+1),d_(t+2),d_(t+3)) -> deficit at t+3
      (1,1,1) -> z=6
      (3,3,1) -> z=2
      (1,5,1) -> z=2
      (1,5,3) -> z=0.

  Proof: at t+1 g=gcd(t-1,2t+1)=gcd(t-1,3). With e1=d_(t+1)-1 in {0,2}, at t+2 g=gcd(t+2,2t+e1-1)=gcd(t+2,e1-5). At t+3, with e2 cumulative growth in {0,4}, g=gcd(t+1,2t+e2+1)=gcd(t+1,e2-1). Check the displayed cases. The resulting state at s'=t+3 (odd) is C=2s'-z, z in {0,2,6}. For the seed parameter M'=t+1 (odd) this is C=2M'-2+(6-z), with only THREE additive seed offsets {0,4,6}. If the original cutoff occurs before t+3, the remaining trajectory is already a <=3-step low-only suffix.

These are strict equalities, not probabilistic restart approximations. The odd reset is a genuine canonical restart; the even reset embeds after three elementary steps into a three-type odd-time seed family, although types z=0 or2 are not canonical initializations.

## 3. Exhaustive low-wheel check of all THREE seed types (finite, not Lean)

Restrict continuation to S={3,5,7,11}, product P=1155. An odd-time seed of deficit z in {0,2,6} is determined by time modulo 2310. The committed Python checker tests every 1155 ODD time residue for each type and independently checks each next clock against the literal parity-specific GCD. Results:

| odd-time deficit z | number of time residues | max nonunit low-only events | max low-only total growth | max deficit encountered |
|---:|---:|---:|---:|---:|
| 0 | 1155 | 17 | 100 | 146 |
| 2 | 1155 | 19 | 98 | 146 |
| 6 | 1155 | 18 | 98 | 146 |

The maximum deficit 146 remains valid for all prefixes. The three-step normalization at even t was checked for all 15 even classes modulo 30 (multiplicities 8,5,1,1 respectively). The earlier all-state restricted low-wheel growth bound 1156 remains available OUTSIDE the reset seeds.

## 4. BINARY first large-prime transition from any reset (paper plus finite certificate)

Starting after an odd reset or from the three-step-normalized even reset, suppose only low primes act until the next high event, whose prime factor p satisfies p>=149. At its pre-event plateau z<=146 by section 3. The earlier proved two-factor deficit obstruction gives that d=p exactly for p>=59 (no simultaneous low factor).

Write delta=n-t0 for this first high p clock; necessarily 1<=delta<=2p.

EVEN: since p divides z+2delta+1, write (2k+1)p=z+2delta+1 <=146+4p+1 <5p for p>=149.
ODD: similarly (2k+1)p=z+2delta-5 <=146+4p-5 <5p. The odd integer multiple must be positive for high p.

Hence k in {0,1}. So the FIRST p>=149 high event after ANY reset has exactly one of four post-deficit values:

    BOXED: z'=0 (even reset), 6 (odd reset), 2p (even charged), 2p+6 (odd charged).   (BINARY)

The p<149 sector contains only FINITELY MANY possible small high prime labels, but this alone does not make their unbounded repetitions finite.

## 5. A prime-only immediate return must almost DOUBLE the charged prime (paper)

Assume the first high event after reset has p>=149, increment d=p, and is CHARGED: post-deficit z1 is 2p or 2p+6. Suppose the NEXT high event has only intervening low-only events, total low growth e (possibly zero), and ITSELF is a RESET with prime-only increment d=q<=B.

The arbitrary-start low-wheel finite certificate gives e<=1156. The deficit just before the next high event is zpre=z1+2*(elapsed low time)-e >=2p-1156. At that next RESET event with waiting delta>=1:
- even reset d=zpre+2delta+1 >=2p-1153;
- odd reset d=zpre+2delta-5 >=2p-1159.

Thus

    BOXED: q>=2p-1159.                                         (RETURN)

In particular if p>(B+1159)/2, the next high event CANNOT be a prime-only reset (q<=B). It would need a composite increment, or must remain charged; the path could also terminate. This statement does NOT ban a later reset after another high event of another type. The additive constant 1159 comes from the sharp universal all-state bound e<=1156.

The 1156 low-only extreme cannot be excluded uniformly using just the shape z=2p: the legitimate ABSTRACT low-wheel plateau t=10394, p=2887 prime, z=2p has two low-only events and total growth exactly 1156. It is NOT claimed to be realized by an actual canonical high-charge history. Better constants require average or reachability information, not merely the congruence class of C.

## 6. Proof strategy: direct three-type renewal before more mixed-prime correlations

The older signed reset-load condition S_X=o(XB), the collision moment K_X=O(XB), and the nonjoining mixed-prime Fejer correlation are partial arithmetic estimates. **Even their complete proofs do not alone bound high-event depth or charged excursions.**

A more direct sufficient condition is the ONE averaged event depth target, for X/B definitions above:

    BOXED: sum_(odd M in [X,2X)) T_B(M) = o(XB),              (OPEN)

where T_B counts events with a prime factor >=13. This suffices for twins via the already established low-wheel block bound E_B(M)<=22+23*T_B(M), clock bound W_X<=3X+4B*sum_M E_B(M), and B^2=Theta(X). A stronger polylog mean sum_M T_B(M)=O(X(log B)^A) would suffice.

The three-seed normal form suggests a **first-return/transfer operator** whose boundary types are z=0,2,6 and whose high transitions have either RESET or CHARGED z≈2p. The section 5 barrier suggests sorting charged excursions by prime size: a large charged p cannot be followed immediately by a small *prime-only* reset, so either the next charged event propagates, a composite event occurs, or the orbit dies. A potentially useful quantitative target is a mean upper bound on paths with long sequences of high charged events **plus** large composite resets, not unconditional per-cell equidistribution of all reset origins.

To obtain the single global mean-depth bound, one still needs genuinely new arithmetic/transport input, such as decay in the occupancy of repeated *nonterminal* high-step histories across uniform canonical M. The elementary reset normal form and first-two-wave CRT do not provide that decay by themselves. A proof forcing many orbits to have no further events may run into the ordinary sieve parity obstruction; the time-order/deficit data must supply extra information.

## Reproduce

    python3 research/three_seed_reset_audit.py

This checker is the actual original parity-GCD for the low-only wheel, the exact three even-reset steps, and an explicit charged-low extreme. Previously committed files handle the full B-wheel and all-state 11-low graph. Research note and source are intended for Issue #4; no Lean kernel proof or main merge.
