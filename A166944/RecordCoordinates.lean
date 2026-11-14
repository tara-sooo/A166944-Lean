import A166944.BCoordinates

/-!
# A record at an odd index, in `D` and `B` coordinates

`record_odd_occurrence_structure` (`Lemmas.lean:217`) says an odd-index record
satisfies `n - 2 = R * c` with `c` odd. The interesting case is `c = 1`, i.e.
`n = R + 2`, which is the case the index theorem asserts always holds.

This file records what is immediate about the coordinates in that case, and
names the two coordinate statements that are *not* yet proved here.

## Immediate

`odd_record_value_eq_index_sub_two`: at a record with `n = R + 2` the value is
`n - 2`. This is definitional given `d n = R`, and it is the pattern every
recorded record follows -- `313` at `315`, `661` at `663`, `139` at `141`.

## Recorded as the next target, not as theorems

  * `D (n - 1) = R - 1`
  * `B (n - 1) = 0`

Both are true in the data and both should follow from `record_index_structure`
together with the one-step identity `D_succ_eq_D_add_d_sub_one`. The versions
attempted here did **not** close: the step from `d n = R` and `n = R + 2` to
`D (n - 1) = R - 1` needs the *record* hypothesis routed through
`record_index_structure`, not just the value equation, and that is a larger proof
than this file should carry unverified.

Why the pair matters: together they say a record at `n = R + 2` is forced to be
the basic-point event, with the value pinned to `n - 2` and the reservoir emptied
just before it. That is the mechanism behind the twin-primality observed in the
data -- there is no room for the value to be anything else -- and it is the shape
to which Shevelev's `q = spf (C + 1)` minimality argument has to be attached.

This file is deliberately small. `DNodes` and `FirstHitDivisor` carry the
divisor half of the same story; neither assumes the minimality that is still
missing.
-/

namespace A166944Research

/-- **The event value at a record with `n = R + 2` is the index minus two.** -/
theorem odd_record_value_eq_index_sub_two {R n : Nat}
    (hd : d n = R) (hidx : n = R + 2) : d n = n - 2 := by
  rw [hd]; omega

end A166944Research
