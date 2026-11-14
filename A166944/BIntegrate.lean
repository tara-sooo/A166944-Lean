import A166944.BStepLaw

/-!
# Integrating the reservoir step law without the E/T ledger

`B_step_law` (`BStepLaw`) is the per-step identity

    B r + (r - s) + 1 = B s + d r.

Summing it over a path gives the reservoir at the endpoint. There are two ways to
write the sum, and they are not equally convenient:

  * through `moving_horizon_path_ledger`, which produces `E = sum d r` and
    `T = sum (r - s)` as existential witnesses. `BLedger` records that route as a
    target, because matching the two sums needs the gap sum carried alongside and
    `omega` will not invert the truncated subtraction involved.

  * **directly**, carrying `sum (d r - 1)` and the total displacement. This file
    takes the second route. The statement is

        B sf + (sf - s) = B s + S

    where `S` is the accumulated `sum (d r - 1)`. Both sides are pure additions,
    so every step of the induction is a rearrangement and no subtraction is ever
    inverted -- which is exactly what the ledger route could not avoid.

At a canonical start `B s = M - 2` and `sf - s` is the travel, so this reads

    B sf = (M - 2) + S - travel,

i.e. the reservoir at the exit is the start minus the travel plus the accumulated
excess. That is the same content as the ledger identity, in a form the induction
can actually reach.
-/

namespace A166944Research

/-- **The integrated step law.**  Along a path, the endpoint reservoir plus the
total displacement equals the start reservoir plus the accumulated excess
`sum (d r - 1)` over the events. -/
theorem B_path_integrated {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ S : Nat, B sf + (sf - s) = B s + S := by
  induction q generalizing s C with
  | zero =>
      obtain ⟨rfl, _, _⟩ := hpath
      exact ⟨0, by simp⟩
  | succ q ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hS'⟩ := ih htail
      have hlaw := B_step_law hstep
      have hd1 : 1 < d r := hstep.2.2.2.1
      have hd : 1 ≤ d r := by omega
      refine ⟨S' + (d r - 1), ?_⟩
      -- Bounds for the subtraction split, named so omega does not have to find them.
      have hs2 : 2 ≤ s := hstep.1.1
      have hsr : s < r := hstep.2.1
      have hle : r ≤ sf := moving_horizon_path_index_le htail
      -- `B r + (r - s) + 1 = B s + d r`, i.e. `B r + (r - s) = B s + (d r - 1)`.
      have hstep' : B r + (r - s) = B s + (d r - 1) := by omega
      have hsrle : s ≤ r := by omega
      -- Split the displacement using Nat.add_sub_assoc in the right direction.
      have hsplit : sf - s = (sf - r) + (r - s) := by omega
      -- Additive rearrangement only: no subtraction is inverted.
      calc B sf + (sf - s)
          = B sf + ((sf - r) + (r - s)) := by rw [hsplit]
        _ = (B sf + (sf - r)) + (r - s) := by omega
        _ = (B r + S') + (r - s) := by rw [hS']
        _ = (B r + (r - s)) + S' := by omega
        _ = (B s + (d r - 1)) + S' := by rw [hstep']
        _ = B s + (S' + (d r - 1)) := by omega

end A166944Research
