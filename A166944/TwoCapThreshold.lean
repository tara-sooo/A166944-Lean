import A166944.TwoCapTarget
import A166944.VerifiedTravelExtension

/-!
# The two-cap target at the threshold the platform states

`TwoCapTarget` carries the decomposition of the travel bound to the top of the
development, at the threshold `22933441` where the verified extension begins. The
platform statement of the same reduction uses `45895573`, the point at which the
finite replay certificates stop. This module bridges the two.

The bridge is the one the travel-bound route already uses
(`TravelTarget.record_index_and_twin_prime_of_twin_travel_bound_from_45895573`):
below `45895573` the explicit replay certificate discharges the bound, and above it
the supplied hypothesis takes over. Here the certificate has to discharge the
*stronger* travel bound, from which both caps follow -- so the bridge is if
anything easier than the one it replaces.
-/

namespace A166944Research

/-- **The caps hold below the platform threshold.**  Between `22933441` and
`45895573` the explicit replay certificate gives the travel bound, and each cap is
a consequence of it. -/
theorem two_cap_below_platform_threshold {M sf Cf p : Nat}
    (hM : 22933441 ≤ M) (hupper : M < 45895573) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) :
    Cf ≤ 3 * M + 4 ∧ 4 * sf ≤ 7 * M - 1 := by
  have hshort := canonical_travel_bound_on_verified_extension hM hupper hcanon hpath hmax
  have hsf : M + 2 ≤ sf := by
    have := moving_horizon_path_index_le hpath
    omega
  constructor
  · exact canonical_horizon_bound_of_short_travel hpath hshort
  · omega

/-- **The platform threshold version.**  Caps stated at `45895573` give the target;
below that threshold the certificate supplies them, above it the hypotheses do. -/
theorem a166944_target_of_two_caps_at_platform_threshold
    (hA : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  -- Assemble the threshold-22933441 pair the induction consumes.
  have hcaps : TwinPrimeTwoCapBoundFrom 22933441 := by
    constructor
    · intro M sf Cf p hM htwin hcanon hpath hmax
      by_cases h : M < 45895573
      · exact (two_cap_below_platform_threshold (by omega) h hcanon hpath hmax).1
      · exact hA (by omega) htwin hcanon hpath hmax
    · intro M sf Cf p hM htwin hcanon hpath hmax
      by_cases h : M < 45895573
      · exact (two_cap_below_platform_threshold (by omega) h hcanon hpath hmax).2
      · exact hB (by omega) htwin hcanon hpath hmax
  intro R hR hrecord
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  exact (record_index_and_twin_prime_of_two_caps_from_22933441
    hcaps hR hn hd hprior).2

end A166944Research
