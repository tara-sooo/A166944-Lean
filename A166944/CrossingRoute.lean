import A166944.RecordBarrier
import A166944.ExitThreshold

/-!
# Why the crossing route cannot forbid a crossing

`HorizonCrossing.lean` characterises what a hypothetical crossing of `3 * M + 4`
must look like. The sharpest of those is
`canonical_large_old_crossing_prefix_multiple`: a crossing requires a positive even
`P` divisible by *every* increment strictly after `M + 2` and up to the crossing
prefix, and then forces

    M + 21 < 4 * P.

The natural witness for `P` is `recordHorizonBound M`, the least common multiple
of the odd numbers up to `M` (`RecordBarrier.lean:174`), which divides every odd
increment below `M` by `odd_dvd_recordHorizonBound` (`RecordBarrier.lean:197`).
And that witness is astronomically large -- 5 digits at `M = 13`, 60 at `M = 139`,
578 at `M = 1321`, 2346 at `M = 5419` -- so `M + 21 < 4 * P` holds with an
enormous margin everywhere a crossing could occur.

The precondition is therefore *satisfied* wherever a crossing could occur, and the
crossing theorems cannot be turned into a proof that no crossing occurs. The shape
is a description of a crossing, not an obstruction to one. This is the seventh
independent route to the conclusion recorded in `REACH.md`.

## What is proved here

`recordHorizonBound_mono` and `crossing_precondition_holds`: the bound is
monotone, and at odd `M >= 5` it dominates `M + 21` by a factor of four. The
monotonicity is the step I failed to close in an earlier session; the route is
`recordHorizonBound_dvd_succ` (`RecordBarrier.lean:180`), which gives
`recordHorizonBound M | recordHorizonBound (M+1)`, so the induction is `dvd`
transitivity rather than a case split over `Nat.lcm`.
-/

namespace A166944Research

/-- **`recordHorizonBound` is monotone.**  Mirroring the style of
`recordHorizonBound_pos_even` (`RecordBarrier.lean:186`), which unfolds the
definition with `simp [recordHorizonBound, h]` rather than by rewriting. -/
theorem recordHorizonBound_mono {M N : Nat} (h : M ≤ N) :
    recordHorizonBound M ≤ recordHorizonBound N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      have hik : recordHorizonBound M ≤ recordHorizonBound (M + k) := ih (by omega)
      have hstep : recordHorizonBound (M + k) ≤ recordHorizonBound (M + k + 1) := by
        by_cases hpar : (M + k + 1) % 2 = 1
        · -- Nat.le_lcm_right {m} (n) (hm : 0 < m) : n ≤ m.lcm n
          -- with m := M+k+1 and n := recordHorizonBound (M+k)
          have hlcm : recordHorizonBound (M + k) ≤
              Nat.lcm (M + k + 1) (recordHorizonBound (M + k)) :=
            Nat.le_lcm_right (recordHorizonBound (M + k)) (Nat.zero_lt_succ (M + k))
          simpa [recordHorizonBound, hpar] using hlcm
        · simpa [recordHorizonBound, hpar]
      have heq : M + k + 1 = M + (k + 1) := by omega
      rw [heq] at hstep
      exact Nat.le_trans hik hstep

/-- **The crossing precondition holds at every odd `M >= 5`.**  With
`P = recordHorizonBound M` the requirement `M + 21 < 4 * P` is met by a factor of
four, so it excludes no crossing. -/
theorem crossing_precondition_holds_at_odd (M : Nat) (hodd : M % 2 = 1) (hM : 5 ≤ M) :
    M + 21 < 4 * recordHorizonBound M := by
  have hdvd : M ∣ recordHorizonBound M := odd_dvd_recordHorizonBound hodd (Nat.le_refl M)
  have hle : M ≤ recordHorizonBound M :=
    Nat.le_of_dvd (recordHorizonBound_pos_even M).1 hdvd
  rcases Nat.lt_or_ge M 9 with hsmall | hbig
  · -- M odd and 5 <= M < 9 forces M = 5 or 7; both are evaluated
    have hcases : M = 5 ∨ M = 7 := by omega
    rcases hcases with rfl | rfl <;> decide
  · have h21 : M + 21 < 4 * M := by omega
    have h4 : 4 * M ≤ 4 * recordHorizonBound M := Nat.mul_le_mul_left 4 hle
    omega


end A166944Research
