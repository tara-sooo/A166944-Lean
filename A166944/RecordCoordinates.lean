import A166944.CanonicalRecord

/-!
# A record at `n = R + 2`, in `D` and `B` coordinates

`canonical_increment_coordinates` (`CanonicalRecord.lean:171`) already gives,
for `d (R + 2) = R`:

    a (R + 1) = 2 * R,   D (R + 2) = 2 * R - 2,   B (R - 1) = 2.

This file records the *neighbouring* coordinates one index earlier, which are
what a first-hit argument needs.

  * `odd_record_horizon_pred_eq_value_sub_one`   `D (R + 1) = R - 1`
  * `odd_record_B_pred_eq_zero`                  `B (R + 1) = 0`

Both are immediate from `a (R + 1) = 2 * R`, which is why they belong beside
`canonical_increment_coordinates`.

Together with the existing lemmas they say: a record at `R + 2` is the
basic-point event. The value is `n - 2 = R`; the reservoir is emptied just before
it (`B (R + 1) = 0`); the horizon there is `R - 1`; and the horizon at the record
is `2 * R - 2`, which is exactly the canonical start shape `2 * M - 2` with
`M = R`. So the record state is itself the canonical start for the next replay.
That is the regeneration mechanism, and it is the shape Shevelev's
`q = spf (C + 1)` minimality argument has to attach to.

What is *not* proved here, and remains the open problem: that every record
satisfies `n = R + 2`, i.e. that `c = 1` in `record_odd_occurrence_structure`.
-/

namespace A166944Research

/-- **The horizon one step before a record at `R + 2` is `R - 1`.** -/
theorem odd_record_horizon_pred_eq_value_sub_one {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) : D (R + 1) = R - 1 := by
  have ha := (canonical_increment_coordinates hR hd).1
  have hD : D (R + 1) = a (R + 1) - (R + 1) := rfl
  rw [hD, ha]
  omega

/-- **The reservoir is empty one step before a record at `R + 2`.** -/
theorem odd_record_B_pred_eq_zero {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) : B (R + 1) = 0 := by
  have ha := (canonical_increment_coordinates hR hd).1
  have hB : B (R + 1) = a (R + 1) - (2 * (R + 1) - 2) := rfl
  rw [hB, ha]
  omega

/-- **The value at the record is the index minus two.** -/
theorem odd_record_value_eq_index_sub_two {R : Nat} (hd : d (R + 2) = R) :
    d (R + 2) = (R + 2) - 2 := by
  rw [hd]
  omega

/-- **The record state is a canonical start.**  Its horizon is `2 * R - 2`, the
shape `2 * M - 2` at `M = R`, so the next replay starts exactly here. -/
theorem odd_record_horizon_eq_canonical_start {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) : D (R + 2) = 2 * R - 2 :=
  (canonical_increment_coordinates hR hd).2.1

end A166944Research
