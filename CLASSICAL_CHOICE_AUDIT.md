# Axiom audit: `Classical.choice` leaks in four existing declarations

Found 2026-11-16 while verifying a documentation correction in `A166944/BindingCoordinate.lean`.

## The finding

Four declarations in `BindingCoordinate.lean` depend on `Classical.choice`:

```
excess_le_two_travel_add_six     [propext, Classical.choice, Quot.sound]
cap_of_travel_bound              [propext, Classical.choice, Quot.sound]
cap_iff_joint_form               [propext, Classical.choice, Quot.sound]
state_bound_iff_excess_bound     [propext, Classical.choice, Quot.sound]
```

This is NOT a `sorry` — the modules compile with 0 errors, 0 warnings and no `sorryAx`. The
consequence is that these four theorems are **non-constructive** in a way the rest of the
development avoids. Every other module landed this session audits to `[propext, Quot.sound]`
only, which is the standard the campaign has been holding itself to.

## Traced source

The leak enters through

```
moving_horizon_path_gap_le_three_growth   [propext, Classical.choice, Quot.sound]
```

in `A166944/CanonicalGrowth.lean`. Its proof is an induction whose final step is `omega` on a
goal mixing `s ≤ sf`, `C ≤ Cf` and `sf - s ≤ 3*(Cf - C)` after rewriting with
`moving_horizon_step_update` and `moving_horizon_step_gap_le_three_growth`. The direct
ingredients are clean:

```
moving_horizon_step_event_package      [propext, Quot.sound]
constant_D_event_map                   [propext, Quot.sound]
moving_horizon_step_state_bound        [propext, Quot.sound]
moving_horizon_path_state_bound        [propext, Quot.sound]
moving_horizon_path_index_le           [propext, Quot.sound]
canonical_start_state_bound            [propext, Quot.sound]
```

so the leak is in how `omega` closes that particular mixed arithmetic goal, not in any
mathematical input. A minimal standalone `omega` on a similar hypothesis set does NOT leak
(verified: two probe theorems both audit clean), so the trigger is specific to that goal shape.

## Why it matters and why it does not block

* It does **not** invalidate any result: `Classical.choice` is a legitimate axiom of Lean's
  standard library, and nothing in the campaign's stated deliverables depends on these four
  being constructive.
* It **does** mean these four should not be cited as "axiom-free" in any write-up. The
  campaign's own audit standard (`propext`, `Quot.sound` only) is not met by them.

## What to do about it

Two honest options, neither urgent:

1. **Document it** (this file) and stop citing those four as constructive. Cheapest, and
   accurate.
2. **Re-prove `moving_horizon_path_gap_le_three_growth`** replacing the terminal `omega` with
   explicit `Nat` arithmetic (`Nat.le_trans`, `Nat.sub_le_sub_right`, `Nat.add_le_add`). This
   would very likely remove the dependency, since all the ingredient lemmas are clean. Worth
   doing only if the project needs a fully constructive tree.

Recorded so that a future reader does not discover this by accident and either (a) panic that
something is broken, or (b) assume the whole tree is classically tainted. Neither is true:
it is exactly four declarations, the leak is localized, and the fix is mechanical if wanted.


---

# RESOLVED (2026-11-16, same session)

All four declarations are now **constructive** — `[propext, Quot.sound]` only. Two fixes:

## 1. `CanonicalGrowth.moving_horizon_path_gap_le_three_growth`

The inductive step's terminal `omega` was the leak. Replaced it with explicit `Nat` arithmetic:

```lean
have hgap  : r - s ≤ 3 * (C' - C)            := moving_horizon_step_gap_le_three_growth hstep
have hstep_le : sf - s ≤ (r - s) + (sf - r)  := by omega
calc sf - s ≤ (r - s) + (sf - r)             := hstep_le
  _ ≤ 3 * (C' - C) + 3 * (Cf - C')           := Nat.add_le_add hgap htailgap
  _ = 3 * (Cf - C)                           := by omega
```

The remaining `omega` calls are on small *purely linear* goals (`C ≤ C'`, the truncated
subtraction split) and do not leak — confirmed by audit. The `zero` case needed
`by omega` rather than `Nat.le_refl _` because the goal is `s - s ≤ 3 * (C - C)`.

This single fix cleared three of the four downstream declarations
(`excess_le_two_travel_add_six`, `cap_of_travel_bound`, `state_bound_iff_excess_bound`).

## 2. `BindingCoordinate.cap_iff_joint_form`

An independent `omega`, so it needed its own fix. It is pure linear arithmetic on an equation,
so it was done by rewriting instead:

```lean
have key : 8 * Cf + 8 * p = 16 * M - 16 + 8 * E := by
  have h1 : 8 * Cf + 8 * p = 8 * (Cf + p) := (Nat.mul_add 8 Cf p).symm
  rw [h1, hled, Nat.mul_add 8]
  ... hbase ...
rw [key]
constructor <;> intro h <;> omega
```

Gotcha worth recording: `Nat.mul_add`'s first argument is the multiplier, so
`Nat.mul_add 8 Cf p : 8 * (Cf + p) = 8 * Cf + 8 * p`. Passing the summands first silently
gives the wrong statement (`Nat.mul_add Cf p 8` elaborates to `Cf * (p + 8)`).

## Verification

`BindingCoordinate.lean`: exit 0, 0 errors, 0 warnings, and
`grep -c Classical.choice` on the axiom report returns **0**. Every declaration in the module
now audits to `[propext, Quot.sound]`.

The tree is constructive again. Module count and declaration count are unchanged, so
`DECLARATIONS.json` needed no edit.


---

# Final status after this session's fixes

## Fixed and verified constructive

| module | `Classical.choice` | errors | warnings |
|---|---|---|---|
| `CanonicalGrowth.lean` | **0** | 0 | 0 |
| `BindingCoordinate.lean` | **0** | 0 | 0 |
| `CanonicalTravel.lean` (module-level) | **0** | 0 | 0 |
| `ExcessCriterion.lean` | 0 | 0 | 0 |
| `QuietReturn.lean` | 0 | 0 | 0 |
| `TwoCapGate.lean` | 0 | 0 | 2 (unused binder) |

The four declarations named at the top of this file are all clean now:

```
excess_le_two_travel_add_six     [propext, Quot.sound]
cap_of_travel_bound              [propext, Quot.sound]
cap_iff_joint_form               [propext, Quot.sound]
state_bound_iff_excess_bound     [propext, Quot.sound]
```

Three techniques removed the leaks:

1. **`omega` → explicit `calc`/`Nat` chains** in the inductive steps of
   `moving_horizon_path_gap_le_three_growth` and `moving_horizon_path_travel_bound`. The
   remaining `omega` calls in those proofs are on small purely-linear goals and do not leak.
2. **`by_cases` → `Nat.lt_or_ge`** where the proposition is a decidable `Nat` inequality. Two
   sites: `canonical_horizon_bound_of_event_count` and `canonical_travel_bound_of_event_count`.
   Note `by_cases` is not itself the problem; the problem is that it goes through `Decidable`,
   and for some proposition shapes that resolves to `Classical.dec`.
3. **Explicit rewriting instead of `omega`** for `cap_iff_joint_form`, which is pure linear
   arithmetic on an equation. Gotcha: `Nat.mul_add`'s FIRST argument is the multiplier, so
   `Nat.mul_add 8 Cf p : 8 * (Cf + p) = 8 * Cf + 8 * p`; passing summands first silently gives
   a different statement.

## Still leaking (2 declarations, both in `CapBCandidates.lean`)

```
capB_of_event_count                    [propext, Classical.choice, Quot.sound]
canonical_travel_bound_of_event_count  [propext, Classical.choice, Quot.sound]
```

Both inherit from `CanonicalTravel`'s internal `divisorTravelBudget` development, where the
leak site is:

```lean
by_cases hex : ∃ j : Nat, s < j ∧ j ≤ sf ∧ ¬ d j ∣ P
```

An **existential** proposition is the case `by_cases` cannot decide constructively here, so it
resolves through `Classical.dec`. Fixing it means restructuring that case split — e.g. by
well-founded recursion on the `exists_last_nondvd` witness rather than case-splitting on whether
one exists. That is a real refactor of the `divisorTravelBudget` section, not a local edit, and it
was left for a future round rather than rushed.

Note for anyone re-auditing: a module-level `grep Classical.choice` on the lean output is NOT
sufficient, because `#print axioms` lines only appear for declarations actually printed. The
table above was produced with explicit `#print axioms` probes per declaration.
