import A166944.TwoCapGate
import A166944.TravelTarget
import A166944.TravelExcess
import A166944.VerifiedTwinPrimePrefix
import A166944.VerifiedTravelExtension
import A166944.VerifiedRecordPrefix

/-!
# The index theorem from the two weaker gates

`TwoCapGate` proved that the consumer of the travel bound needs strictly less:
a horizon cap `Cf <= 3*M + 4` and an index cap `4*sf <= 7*M - 1`, the latter
relaxed by a factor of `7/6` against what travel gives. This module carries that
relaxation up to the top of the development, so that the obstruction is stated at
the weaker strength everywhere above the consumer.

The induction below is `TravelTarget.record_index_and_twin_prime_of_twin_travel_bound_from_22933441`
with exactly one thing changed: the single call to
`canonical_next_record_factors_of_short_travel` becomes a call to
`canonical_next_record_factors_of_two_caps_tight`, and the travel hypothesis it
consumed becomes the pair of caps. Everything else -- the truncation at the
verified prefix, the strong recursion, the extraction of the previous maximum
`M` and its canonical index -- is the same argument.

## What is gained

The hypothesis is strictly weaker, so the statement is strictly easier. It is not
yet proved: `4*sf <= 7*M - 1` is still a uniform statement about the terminal
index, and `REACH.md`'s diagnosis is unchanged. What has changed is which
inequality is the target, and a target with 45.9 million more slack at the
threshold is a better target than the one before it.

## Why this is not circular

The temptation is to derive the travel bound from the caps and then reuse the
existing theorem. That is exactly what is impossible: `TwoCapGate.separation_at_real_threshold`
exhibits an index/horizon pair satisfying both caps while violating the travel
bound. The caps do not imply travel, so the argument has to go through the consumer
directly, which is what this file does.
-/

namespace A166944Research

/-- The two caps, bundled so the induction can carry one hypothesis. -/
def TwinPrimeTwoCapBoundFrom (lower : Nat) : Prop :=
  (∀ {M sf Cf p : Nat}, lower ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4) ∧
  (∀ {M sf Cf p : Nat}, lower ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1)

/-- **Travel gives both caps**, so the pair is implied by the existing hypothesis
and any proof of the pair replaces it. -/
theorem two_cap_of_travel (htravel : TwinPrimeTravelBoundFrom 22933441) :
    TwinPrimeTwoCapBoundFrom 22933441 := by
  constructor
  · intro M sf Cf p hM htwin hcanon hpath hmax
    exact canonical_horizon_bound_of_short_travel hpath (htravel hM htwin hcanon hpath hmax)
  · intro M sf Cf p hM htwin hcanon hpath hmax
    have hshort := htravel hM htwin hcanon hpath hmax
    have hsf : M + 2 ≤ sf := by
      have := moving_horizon_path_index_le hpath
      omega
    omega

/-- **The index theorem from the two caps.**  The same induction as the
travel-bound version, with the consumer replaced by its decomposed form. -/
theorem record_index_and_twin_prime_of_two_caps_from_22933441
    (hcaps : TwinPrimeTwoCapBoundFrom 22933441) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  intro R n
  induction n using Nat.strongRecOn generalizing R with
  | ind n ih =>
    intro hR hn hd hprior
    by_cases h : R ≤ 22933441
    · exact ⟨(record_index_and_factors_of_le_22933441 hR h hn hd hprior).1,
        target_for_records_le_22933441 hR h ⟨n, hn, hd, hprior⟩⟩
    · have hnLarge : 22933443 < n := by
        by_cases hle : n ≤ 22933443
        · have hcap := last_verified_prefix_maximum.1 n hn hle
          omega
        · omega
      obtain ⟨M, hmax⟩ := attained_previous_maximum_exists (n - 1) (by omega)
      have hM : 22933441 ≤ M := by
        have hcap := hmax.1 22933443 (by decide) (by omega)
        simpa only [last_verified_record_value] using hcap
      obtain ⟨m, hm, hmn, hdm, hMprior⟩ := attained_previous_maximum_first_occurrence hmax
      obtain ⟨hmi, hMtwin⟩ := ih m (by omega) (by omega : 5 < M) hm hdm hMprior
      have hMcanon : d (M + 2) = M := by rwa [← hmi]
      have hstartMax : IsAttainedPreviousMaximum M (M + 2) :=
        ⟨fun j hj hjM => hmax.1 j hj (by omega), ⟨M + 2, by omega, Nat.le_refl _, hMcanon⟩⟩
      have hMlt : M < R := by simpa only [hdm] using hprior m hm (by omega)
      obtain ⟨C, hnew, hpre, hdnew, hminus, hplus⟩ :=
        canonical_next_record_factors_of_two_caps_tight (by omega) hMcanon hstartMax
          (fun hpath hp => hcaps.1 (by omega) hMtwin hMcanon hpath hp)
          (fun hpath hp => hcaps.2 (by omega) hMtwin hMcanon hpath hp)
      have heq : n = C + 3 := by
        rcases Nat.lt_trichotomy n (C + 3) with hlt | heq | hgt
        · have hcap := hpre.1 n hn (by omega)
          omega
        · exact heq
        · have hcap := hmax.1 (C + 3) (by omega) (by omega)
          omega
      have hR' : R = C + 1 := by rw [heq, hdnew] at hd; omega
      refine ⟨by omega, ?_⟩
      change R.Prime ∧ (R - 2).Prime
      rw [hR', show C + 1 - 2 = C - 1 by omega]
      exact ⟨prime_of_no_proper_factor (by omega) hplus, prime_of_no_proper_factor (by omega) hminus⟩

end A166944Research
