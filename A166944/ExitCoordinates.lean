import A166944.ExitBand

/-!
# Coordinate relations at a canonical exit

The endpoint of a canonical replay carries three numbers: the index `sf`, the
horizon `Cf = D sf`, and the sequence value `a sf`. They are not independent --
two identities tie them together, and both are immediate from the definitions:

    a sf = D sf + sf = Cf + sf

and the reservoir dictionary

    B sf + sf = Cf + 2.

Everything proved here is bookkeeping on those two, but the bookkeeping is the
useful part: it converts `a_le_three_mul` (`CanonicalRecord.lean:15`) into a
two-sided statement about the exit, and it shows that the upper side is tight.

## What is tight and what is not

`a n <= 3 * n` is *tight* at these exits: numerically `a sf / sf` tends to `3.0`
and `a sf / M` tends to `3.0` as `M` grows, while `Cf / M` tends to `2.0` and
`sf / M` tends to `1.0`. So the bound

    Cf + sf = a sf <= 3 * sf,   i.e.   Cf <= 2 * sf

is the state bound in coordinate form, and it cannot be improved from above.

The lower side is where a sharper statement lives. From `Cf - sf <= 2*M - 4`
(`ExitBand`, under `sf <= 2*M - 4`) one gets `Cf <= sf + 2*M - 4` and hence

    a sf = Cf + sf <= 2 * sf + 2 * M - 4,

i.e. an upper bound on `a sf` that is *better* than `3 * sf` whenever
`sf > 2 * M - 4`. That is not automatic; it is exactly the index bound again.

## Why record this

Because the direction that matters is the one `a_le_three_mul` does not give. To
bound `sf` from `a` one needs a *lower* bound on `a sf`, and `a sf = Cf + sf`
with `Cf` large is the only source of one. The numerical convergence
`a sf / sf -> 3` says that source is already exhausted at the exits, which is why
no route through `a` alone can bound `sf`.
-/

namespace A166944Research

/-- **The sequence value at a state is the horizon plus the index.**  Direct from
`D n = a n - n`. -/
theorem a_eq_D_add_index {n : Nat} (hn : n ≤ a n) : a n = D n + n := by
  unfold D
  omega

/-- **The exit value in terms of the horizon and the index.** -/
theorem a_at_state {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    a sf = Cf + sf := by
  obtain ⟨hs2, hD, _⟩ := hstate
  have hle : sf ≤ a sf := by
    have := index_le_a sf
    omega
  have h := a_eq_D_add_index hle
  omega

/-- **`a_le_three_mul` at a state is the state bound.**  `Cf <= 2 * sf`. -/
theorem state_bound_of_a_le_three_mul {sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) : Cf ≤ 2 * sf := by
  have ha := a_at_state hstate
  have h3 := a_le_three_mul sf
  omega

/-- **The sharper upper bound on the exit value**, on the index hypothesis that
`ExitBand` isolates.  `a sf <= 2 * sf + 2 * M - 4`, which beats `3 * sf` exactly
when `sf > 2 * M - 4`. -/
theorem a_at_exit_le {M sf Cf : Nat}
    (hM : 5 < M) (hsf : sf ≤ 2 * M - 4) (hstate : IsMovingHorizonState sf Cf) :
    a sf ≤ 2 * sf + 2 * M - 4 := by
  have ha := a_at_state hstate
  have hslack := canonical_exit_slack_le_two_mul_sub_four hM hsf hstate
  omega

/-- **The index is the value minus the horizon.**  `sf = a sf - Cf` at any state,
directly from `a sf = Cf + sf`. -/
theorem sf_eq_a_sub_horizon {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    sf = a sf - Cf := by
  have ha := a_at_state hstate
  omega

/-- **The index is the reservoir minus two, plus the horizon gap.**  Combining
`B sf + sf = Cf + 2` with `sf = a sf - Cf` shows the three coordinates carry no
independent information: any two determine the third. -/
theorem coordinates_determined {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    a sf = B sf + 2 * sf - 2 := by
  have ha := a_at_state hstate
  have hB := moving_horizon_state_B_add_index hstate
  omega

end A166944Research

