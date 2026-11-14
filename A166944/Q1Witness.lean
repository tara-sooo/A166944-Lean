import A166944.AbsoluteIndex

namespace A166944Research

set_option maxRecDepth 100000

/-! The `q = 1` far-even witness is consistent locally but not a real state.

The local data

    delta = 15,  M = 11,  t = 16,  e = 13,  c = 4

satisfies every summary constraint of the `q = 1` far-even branch:

    2 * delta = t + 1 + e      (30 = 30)
    M < e < delta              (11 < 13 < 15)
    delta + 6 <= 2 * M         (21 <= 22)
    e + 2 < t                  (15 < 16)

but it is not realised by the recurrence. The branch would place the state at
`s = delta * c = 60` with horizon `C = delta * (c + 2) = 90`, and the real
`D 60` is 100, not 90. So the separation is the *absolute* value of `D`, not
any summary inequality -- the same mechanism that refutes the scalar survivors
in `AbsoluteIndex.lean`.

Recorded because the tempting converse ("`q = 1` forces `e <= M`, so the
far-even branch cannot be intermediate") is FALSE, and this witness is the
counterexample.
-/

theorem q1_local_data_satisfies_summary :
    2 * 15 = 16 + 1 + 13 ∧ 11 < 13 ∧ 13 < 15 ∧ 15 + 6 ≤ 2 * 11 ∧ 13 + 2 < 16 := by
  decide

theorem D_sixty_is_hundred : D 60 = 100 := by decide

theorem not_state_sixty_ninety : ¬ IsMovingHorizonState 60 90 := by
  intro h
  have hD : D 60 = 90 := h.2.1
  rw [D_sixty_is_hundred] at hD
  omega

/-- The tempting converse is refuted: `q = 1` far-even data can be intermediate. -/
theorem q1_far_even_can_be_intermediate :
    ∃ delta M t e : Nat,
      2 * delta = t + 1 + e ∧ M < e ∧ e < delta ∧ delta + 6 ≤ 2 * M ∧ e + 2 < t :=
  ⟨15, 11, 16, 13, by decide, by decide, by decide, by decide, by decide⟩

end A166944Research
