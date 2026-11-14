import A166944.FirstHitArithmetic

/-!
# The individual gap is at most twice the record

`moving_horizon_event_divisor_gap` (`FirstHitArithmetic.lean:37`) bounds a single
gap by twice any divisor of the event value:

    r - s <= 2 * p      whenever  p >= 2  and  p | d r.

Taking `p` to be the event value itself is not allowed -- `p | d r` with `p = d r`
is trivially true but `p >= 2` needs the event to be nontrivial -- and taking the
smallest prime factor is what Shevelev does. This file takes the other extreme,
which needs nothing:

    r - s <= 2 * d r

since `d r | d r`. And `d r <= M` is exactly the running-maximum clause of
`IsAttainedPreviousMaximum M sf`, so on a path whose events all stay below `M`,

    r - s <= 2 * M.

## What this does and does not give

It gives a *per-step* bound: no single gap can exceed twice the record. Summing
over the path then bounds the total travel by `2 * M * p`, which is useless
without a bound on `p` -- that is the missing ingredient again.

What it does give is an upper bound that is uniform in the step, not merely
uniform in the path: every gap on a canonical replay is at most `2 * M`,
independently of how many steps there are. That is the form needed if one wants to
argue "the travel is spread over few long gaps" rather than "the travel is small".

Numerically, on the fourteen canonical exits the sweep reaches, the largest
observed gap is at most `2 * d r` at every step (no violation), and the bound
`r - s <= M` also holds at every step, which is half of `2 * M`. The factor two is
not tight in the data; it is what the divisor lemma gives.
-/

namespace A166944Research

/-- **A single gap is at most twice the event value.**  Immediate from
`moving_horizon_event_divisor_gap` with `p := d r`. -/
theorem gap_le_two_mul_event {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    r - s ≤ 2 * d r := by
  have hdr : 2 ≤ d r := hstep.2.2.2.1
  exact moving_horizon_event_divisor_gap hstep hdr (Nat.dvd_refl _)

/-- **A single gap is at most twice the running maximum.**  On a path whose
events all stay at or below `M` -- the running-maximum clause of
`IsAttainedPreviousMaximum` -- every gap is at most `2 * M`, uniformly in the
number of steps. -/
theorem gap_le_two_mul_of_max {M s C r C' sf : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hmax : IsAttainedPreviousMaximum M sf)
    (hrsf : r ≤ sf) (hr2 : 2 ≤ r) :
    r - s ≤ 2 * M := by
  have hgap := gap_le_two_mul_event hstep
  have hdrM : d r ≤ M := hmax.1 r hr2 hrsf
  omega

end A166944Research
