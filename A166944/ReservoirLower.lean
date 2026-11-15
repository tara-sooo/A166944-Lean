import A166944.RoomLedger
import A166944.ExitBand

/-!
# What a reservoir lower bound does and does not give

This file began as an attempt to show that the excess term in the scaled form

    2 * S + M <= 2 * B sf + 4

is free -- that a lower bound on the reservoir would suffice with no hypothesis on
`S` at all. **That attempt failed, and the failure is the content of this file.**

The arithmetic is immediate once written out. A lower bound `B sf >= (M + 4) / 2`
makes the right side at least `M + 8`, so the inequality would require `2 * S <= 8`,
that is `S <= 4`. Far from being free, `S` must be small. This is exactly what
`RoomLedger.canonical_room_le_M_of_excess_le_four` already recorded -- the excess
has to be at most 4 for the room route to close -- so the "new" observation was a
rediscovery of an existing conclusion, and the claim attached to it was false.

Recorded rather than deleted because the mistake is a natural one: the scaled form
has `S` on the left and `B sf` on the right, which invites the reading that the two
are traded off against each other. They are not. `S` appears with a positive
coefficient on one side and not at all on the other, so a lower bound on `B sf`
cannot absorb it.

The true statement of the separation is therefore the opposite one, and it is what
`RoomLedger` proves: `Cf - sf <= (M - 4) + S` together with `S <= 4` gives
`Cf - sf <= M`, and dropping `S` entirely is *not* available.
-/

namespace A166944Research

/-- **The attempt, refuted.**  If the excess term could be discarded then
`2 * S + M <= 2 * B sf + 4` would follow from `M + 4 <= 2 * B sf` for every `S`.
It does not: at `S = 5` and `B sf = (M + 4) / 2` the inequality fails. -/
theorem reservoir_lower_does_not_absorb_excess :
    ¬ (∀ M S Bsf : Nat, M + 4 ≤ 2 * Bsf → 2 * S + M ≤ 2 * Bsf + 4) := by
  intro h
  -- M = 0, S = 5, Bsf = 2: M + 4 = 4 <= 4 = 2 * 2, but 2 * 5 + 0 = 10 > 8.
  have := h 0 5 2 (by decide)
  omega

/-- **What a reservoir lower bound does give**, matching the existing
`RoomLedger.canonical_room_le_M_of_excess_le_four`: the excess has to be bounded as
well, and with `S <= 4` the two together close the bound. -/
theorem room_bound_of_reservoir_lower_and_small_excess {M S Bsf : Nat}
    (hB : M + 4 ≤ 2 * Bsf) (hS : S ≤ 4) :
    M ≤ 2 * Bsf + 4 - 2 * S := by omega

end A166944Research
