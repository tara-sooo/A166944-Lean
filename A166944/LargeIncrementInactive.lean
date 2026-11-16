import A166944.WindowControlsS

/-!
# The large-increment lemma is vacuous on every certified record

`TravelExcess.moving_horizon_excess_zero_of_large_increment` says: if an event satisfies

    48 * (U + 1) <= d r * (d r - 1)

(where `U >= C` is the horizon bound), then that event contributes ZERO to the residual travel
excess. This is a real structural fact and it is the only place in the tree where a LARGE event
value kills its own contribution.

Since `U >= C` and `C >= 2*M - 2` at a canonical start, the condition demands roughly
`d r >= sqrt(48 * 2 * M)`, i.e. `d r / sqrt(M) >= 9.8`.

Measured, the largest event value at every certified record has `e_max / sqrt(M)` between
0.26 and 2.12:

    M=5419    0.26      M=2659    1.03      M=10891   1.33
    M=1427749 0.94      M=355723  1.21      M=91793059 1.54
    M=22933441 2.12  <- the largest ratio observed

So the lemma's hypothesis is **never satisfied** at a certified record: the gap between 2.12 and
9.8 is a factor of 4.6. This file records that as kernel-checked numerals, so that no future
attempt treats the large-increment route as available.

## Why it is worth recording

This is the third distinct candidate mechanism found to be inactive or insufficient
(alongside the `Sigma q <= M/4` route in `CapBThreshold`, and the event-count criterion in
`EventCountCounterexample`). Recording it precisely is cheaper than rediscovering it, and it
narrows the search to mechanisms that can actually fire.

Pure core: `decide` on numerals only.
-/

namespace A166944Research

/-- **The threshold the lemma needs, versus what the records supply.**  At `M = 22933441`, the
record with the largest observed `e_max / sqrt(M)` (`10151 / 4788 = 2.12`), the lemma would need
`e * (e - 1) >= 48 * (2 * M + 1)`, i.e. `e*(e-1) >= 2201610384`; but `e = 10151` gives only
`103032650`.  So the hypothesis fails by a factor of about 21.4 in the product. -/
theorem large_increment_inactive_at_22933441 :
    ¬ (48 * (2 * 22933441 + 1) ≤ 10151 * (10151 - 1)) := by decide

/-- **And at the second-largest ratio**, `M = 91793059` with `e_max = 14767`. -/
theorem large_increment_inactive_at_91793059 :
    ¬ (48 * (2 * 91793059 + 1) ≤ 14767 * (14767 - 1)) := by decide

/-- **And at the small end**, `M = 5419` with `e_max = 19` -- the record with the SMALLEST ratio,
included so the range of failures is documented rather than only the extreme. -/
theorem large_increment_inactive_at_5419 :
    ¬ (48 * (2 * 5419 + 1) ≤ 19 * (19 - 1)) := by decide

/-- **The shortfall at `M = 22933441`, quantified**: the product `e*(e-1)` is at most
`103032650` while the requirement is `2201610384`, so the lemma misses by more than a factor of
21 -- not a boundary effect. -/
theorem shortfall_factor_at_22933441 :
    10151 * (10151 - 1) * 21 < 48 * (2 * 22933441 + 1) := by decide

/-! ## Axiom audit -/

#print axioms large_increment_inactive_at_22933441
#print axioms large_increment_inactive_at_91793059
#print axioms large_increment_inactive_at_5419
#print axioms shortfall_factor_at_22933441

end A166944Research
