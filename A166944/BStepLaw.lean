import A166944.BCoordinates
import A166944.CountFromIndex

/-!
# The reservoir step law and the path ledger

`BCoordinates` proves two things about the reservoir `B n = a n - (2n - 2)`:

  * along a unit tail, `B` drops by exactly one per step
    (`moving_horizon_B_pred`: `B (r - 1) + (r - 1 - s) = B s`);
  * at an event, `excess_succ_add_two` (`Lemmas.lean:1241`) raises it by `d r - 2`
    (`B (k + 1) + 2 = B k + d (k + 1)`).

Combining them gives the **step law**, which is what a path-level ledger needs:

    B r + (r - s) + 1 = B s + d r.

Both halves are already proved; this file is the composition. It is the missing
piece that `BLedger` recorded as a target, and it closes the arithmetic that
`omega` could not do there.

Summing the step law over a path then gives

    B sf + T + q = B s + E

with `T` the gap sum and `E` the event sum from `moving_horizon_path_ledger`.
At a canonical start `B (M + 2) = M - 2`, so the reservoir at the exit is
`B sf = (M - 2) + E - T - q`: the reservoir is pinned, not free.
-/

namespace A166944Research

/-- **The reservoir step law.**  Between consecutive events, the unit tail drops
`B` by one per index; the event itself raises it by `d r - 2`.  Net, over the gap
`r - s`:

    B r + (r - s) + 1 = B s + d r. -/
theorem B_step_law {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    B r + (r - s) + 1 = B s + d r := by
  have hs : 2 ≤ s := hstep.1.1
  have hsr : s < r := hstep.2.1
  -- the unit tail from s to r - 1
  have htail : ∀ j : Nat, s < j → j ≤ r - 1 → d j = 1 := by
    intro j hj1 hj2
    exact hstep.2.2.2.2.1 j hj1 (by omega)
  have hpred : B (r - 1) + (r - 1 - s) = B s :=
    B_add_index_sub_eq_of_unit_tail hs (by omega) htail
  -- the event step at r
  have hstep2 : B (r - 1 + 1) + 2 = B (r - 1) + d (r - 1 + 1) :=
    excess_succ_add_two (by omega : 2 ≤ r - 1)
  have hidx : r - 1 + 1 = r := by omega
  rw [hidx] at hstep2
  omega

end A166944Research
