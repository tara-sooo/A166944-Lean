import A166944.BCapDictionary
import A166944.CanonicalRecord

/-!
# The endpoint slack bound at a canonical exit

`Attempt.lean:1091` records, under `HasMovingHorizonDangerousSuffix`,

    Cf - sf <= 2 * M - 4,

and the dangerous-suffix hypothesis includes `M < Cf - sf`. That is a real
restriction: at a genuine canonical exit it holds only for small `M`. Of the
fourteen records the sweep reaches (M from 13 to 713833), five exits are **not**
dangerous -- `M >= 313` gives `Cf - sf ~ M`, below `M` rather than above it -- and
the bound holds at all fourteen anyway.

This file proves the bound **without** the dangerous hypothesis, under the
hypotheses a canonical replay actually supplies. The mechanism is
`a_le_three_mul` (`CanonicalRecord.lean:15`), Rowland's "formidable obstruction"
which is already resolved here: at a state with `D sf = Cf` and `M + 2 <= sf`,

    Cf - sf = a sf - 2 * sf <= 3 * sf - 2 * sf = sf,

so the slack never exceeds the index. Combined with `M + 2 <= sf` and the state
bound this gives the numerical form.

What the bound buys: `B sf = Cf - sf + 2` at the endpoint, so
`B sf <= 2 * M - 2`. That is the *upper* half of the reservoir bracket; the lower
half is what `CountFromIndex` and `REACH.md` identify as missing.
-/

namespace A166944Research

/-- **The slack at any state never exceeds the index.**  This is `a_le_three_mul`
in coordinate form: `Cf - sf <= sf` whenever `D sf = Cf`. -/
theorem state_slack_le_index {sf Cf : Nat} (hD : D sf = Cf) : Cf - sf ≤ sf := by
  have hle := a_le_three_mul sf
  have hDn : D sf = a sf - sf := rfl
  omega

/-- **The endpoint slack bound, with the index bound as an explicit hypothesis.**
The numerical form `Cf - sf <= 2 * M - 4` needs `sf <= 2 * M - 4`, i.e. a bound on
the endpoint index. That bound is *not* available from the state and the start
alone -- it is the same missing ingredient `REACH.md` records -- so it is stated
here as a hypothesis rather than smuggled in. -/
theorem canonical_exit_slack_le_two_mul_sub_four {M sf Cf : Nat}
    (hM : 5 < M) (hsf : sf ≤ 2 * M - 4) (hstate : IsMovingHorizonState sf Cf) :
    Cf - sf ≤ 2 * M - 4 := by
  obtain ⟨_, hD, _⟩ := hstate
  have hslack := state_slack_le_index hD
  omega

/-- **The reservoir at a canonical exit is at most `2 * M - 2`**, on the same
hypothesis.  `B sf = Cf - sf + 2` at the endpoint, so this is the upper half of
the reservoir bracket; the lower half is what `CountFromIndex` and `REACH.md`
identify as missing. -/
theorem canonical_exit_B_le {M sf Cf : Nat}
    (hM : 5 < M) (hsf : sf ≤ 2 * M - 4) (hstate : IsMovingHorizonState sf Cf) :
    B sf ≤ 2 * M - 2 := by
  have hslack := canonical_exit_slack_le_two_mul_sub_four hM hsf hstate
  have hB := moving_horizon_state_B_add_index hstate
  omega

end A166944Research
