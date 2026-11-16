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
