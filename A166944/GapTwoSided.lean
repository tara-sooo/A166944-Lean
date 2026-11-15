import A166944.ResearchDefs
import A166944.RecordIndex
import A166944.FirstHitArithmetic
import A166944.HalfWindow

namespace A166944Research

/-- **The lead's claim 1, discharged as a specialisation.**
`lpf` is not needed as a function: any divisor `q` of `C - 1` with `1 < q` gives
`r - s ≤ 2 * q`, and the least prime factor is such a `q`.  So `gap ≤ 2*lpf(C-1)`
is `moving_horizon_gap_le_twice_even_factor` at `v := lpf(C-1)`. -/
theorem gap_le_twice_even_divisor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C - 1) :
    r - s ≤ 2 * v :=
  moving_horizon_gap_le_twice_even_factor hstep hv hdiv

theorem gap_le_twice_odd_divisor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C + 1) :
    r - s ≤ 2 * v :=
  moving_horizon_gap_le_twice_odd_factor hstep hv hdiv

/-- **The two-sided form is available with no parity hypothesis on `r`**: the even
and odd factor lemmas are both unconditional in `r`, so the gap is bounded by
twice the smaller of *any* divisor of `C - 1` and *any* divisor of `C + 1`. -/
theorem gap_le_twice_min_of_both_sides {s C r C' u v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hu : 1 < u) (hdivu : u ∣ C - 1)
    (hv : 1 < v) (hdivv : v ∣ C + 1) :
    r - s ≤ 2 * min u v := by
  have hu' := gap_le_twice_even_divisor hstep hu hdivu
  have hv' := gap_le_twice_odd_divisor hstep hv hdivv
  rcases Nat.le_total u v with h | h
  · rw [Nat.min_eq_left h]; exact hu'
  · rw [Nat.min_eq_right h]; exact hv'

#print axioms gap_le_twice_even_divisor
#print axioms gap_le_twice_odd_divisor
#print axioms gap_le_twice_min_of_both_sides

end A166944Research
