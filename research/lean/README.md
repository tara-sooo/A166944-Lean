# Negative MIN formal research — issue #10

Base: sixth research branch `research/min-local-crossing-support` at
`26ad4eab14f0ab0862c9d0313a26a625488a4f44`.
Independent branch: `research/min-negative-lean-live-survival`. No canonical modules or sibling
research branches changed.

## Verified checkpoint

`NegativeMINCore.lean`, exact commit
[a9f0cc2](https://github.com/tara-sooo/A166944-Lean/commit/a9f0cc2e1dcaaad4a6f7495e40464bc03a702d7a),
blob `ebd6e41a70a5a803b2ac55ee487b9e628a842242`.
[Green pinned Lean run 46010915076](https://github.com/tara-sooo/A166944-Lean/actions/runs/46010915076).
54 theorem declarations, including conditional implications and a finite
counterexample. The checked file uses Lean v4.33.1 and core Omega.
The printed theorem dependencies are contained in
`propext, Classical.choice, Quot.sound`. No admitted proof or additional axiom.

- The state is (natural nonnegative center, signed integer clock). Canonical
  births are A divisible by 6 at clock 3-A/2. Each tick chooses the least
  eligible odd prime of either neighbor, with the appropriate clock
  congruence; a quiet tick leaves the center unchanged. No artificial prime
  cutoff or artificially absorbing twin rule.
- `winner_minimal`, `firstEvent_minimum_tick`,
  `firstEvent_minimum_label`, `calendarWait_pin`,
  `firstEvent_wait_le_factor`, `firstEvent_wait_le_three_gain`:
  actual first hit and tie-break, waits <=2q and <=3(p-1).
- `height_gain_identity`, `tick_height_pin`, `tick_height_nonneg`,
  `canonical_gain_bound`: preserve evenness, nonnegative doubled height,
  and total gain <=2 age+6.
- `coalescence`: equality of both center and clock implies common future.
  `center_only_coalescence_false`: same actual root A=6 has x=6 at
  ages 1 and 6, but x=6 and x=2 at the following ages. Position-only
  equality is not sufficient for future equality.
- `observeAge_le_half`, `observed_center_lower`,
  `liveAbove_of_slab`, `observedTwin_stays`: synchronized windows,
  slab displacement and genuine twin stability until retirement, when
  R>6T+14.
- `FullCapped`, `life_integral`: irreversible death ages, physical
  (window, center, clock) cap including pre-observation births, exact
  observation tick sum. `narrowCount`, `mediumCharge` count completed
  events through deletion/retirement, including the event on which the
  root is deleted. Roughness d=3/5 is the exact integer comparison
  p^3 <= (2q)^5.
- CONDITIONAL kernel theorems `scaled_twin_count_lower` and
  `unbounded_of_scaled_live_family`: under the explicit finite weighted
  estimate, strict positive surplus forces actual twin centers in the
  slab, and such certificates beyond arbitrary thresholds force
  unbounded twin centers. The estimate itself is NOT verified.

The proof loop actually inspected failure logs and repaired failed goals.
Runs 46009104198, 46009400888, 46009547955 and 46009940351 recorded
failed splitting/decidability, integer cast names, distributivity and
evolve rewriting, and final lifetime/geometry proof goals. Earlier
green core: 9f6e128, run 46009719094. In particular the height proof
requires parity: the bare lower bound H>=3-p and congruence H=6 mod p
allow H=-1 at p=7. The actual invariant H even excludes that arithmetic
countermodel. Do not mistake it for an actual canonical orbit.

## Finite experiments (not asymptotic proofs)

`negative_min_core_comparator.mjs`, commit 443fe9539ea2799daa86337173574b3e5131fbab:
independent tick implementation vs event-driven calendar,
A=6,12,...,1200, 120 ticks each, 24000 checks, 1346 events, 48 tie events.
Executed and reexecuted after remote readback. Includes actual
same-center/different-clock and tie fixtures; selected examples are
also kernel-reduced in the core via `decide`.

## Exact remaining target and Mathlib handoff

`NegativeMINWeightedCriterion.lean` at 01fc7e9eb1479c4a4524b20e7405c01ec31e11c9
is **an uncompiled candidate**, isolated from the verified core.
It records the exact additive weighted criterion from 5a22180 §§4–7,
used in 2fdbf53 and 26ad4ea, with beta=2.1, sigma=.25, alpha=.60,
gamma0=.45, gamma1=.85, epsilon1=.10, delta0=.50, and d=.60.
The real weights, shortened observation horizon, growing relay
budget, normalization over ALL roots, and unbounded-slab quantifiers
are explicit. Integer ceilings for Y0/Y1 encode the real threshold
inequalities. The separate Mathlib adapter uses the pinned
`Nat.prime_def_lt'` and `Nat.Prime.mod_two_eq_one_iff_ne_two`.
The conventional conclusion is arbitrarily large p with
`p.Prime ∧ (p-2).Prime`. The core's executable primality and least
factor bridge to Mathlib is not yet kernel-checked in that environment.

Open proof obligations (no axioms or admitted lemma bodies):
1. Check adapter in pinned Mathlib; prove leastOddFactor agrees with
   Nat.minFac for odd n>=3, and prove ScaleGeometry and the exact
   conditional real-scale extraction (no extra geometric hypothesis
   in the final ExactWeightedCriterion).
2. Verify the double-counted phase capacity (including truncated
   death intervals), low-label run and disjoint relay ledgers, then
   the uniform sieve and error estimates of (14)-(15), exactly
   `WeightedEstimate`. Earlier paper arguments are not Lean proof.
3. Prove `CheapSurvival`: actual capped histories with
   eta >= c (log R)^(-1/4) and prefixMean=o((log R)^(-1/4))
   on arbitrarily large slabs. The selected seed/prefix theorem at
   the base only reaches subpolynomial ages; it does not meet this
   requirement. Study collision losses in medium-label and repeated
   return intervals, with priority to actual time rather than event
   count. The conditional implication is not a solution to this goal.
4. Preserve the quantitative count conclusion R/(log R)^2.35,
   not just infinitude; prove elementary scale/cardinality comparisons
   and the corresponding real bound. Formalize the diversity-cost
   variant (17)-(18) separately, without silently equating it with
   the additive cost.

## Lightweight commands and environment

Core only:
```sh
lean research/lean/NegativeMINCore.lean
```
The branch-only GitHub workflow uses sparse checkout and a cached
pinned Lean toolchain; no lake update, Mathlib package acquisition,
or whole-repository build. The local chat execution environment
has no accessible Lean/Mathlib installation. The first hosted
toolchain setup was followed by cache restore in the verified run.

For the candidate Mathlib adapter, ONLY in an already prepared
checkout with the pinned dependencies and oleans available:
```sh
lake env lean -o research/lean/NegativeMINCore.olean research/lean/NegativeMINCore.lean
lake env sh -c 'LEAN_PATH="research/lean:$LEAN_PATH" lean research/lean/NegativeMINWeightedCriterion.lean'
```
Keep the generated olean untracked. These two Mathlib-environment
commands have not been executed in this session. Do not run a new
dependency fetch or the canonical full verification workflow merely
to test the adapter. No claim of a twin-prime proof.
