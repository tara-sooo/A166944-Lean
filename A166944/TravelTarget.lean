import A166944.QuietReturn
import A166944.TravelExcess
import A166944.VerifiedTwinPrimePrefix
import A166944.VerifiedTravelExtension

/-!
# A common travel hypothesis for the full index and primality targets

The verified prefix discharges all earlier records. A short actual
capped replay forces the next canonical record to have twin-prime
value, so a joint induction needs the travel hypothesis only after
a canonical record already known to be a greater twin prime.
-/

namespace A166944Research

theorem record_index_of_travel_bound_from_22933441
    (htravel : CanonicalTravelBoundFrom 22933441) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 := by
  apply record_index_of_horizon_bound_from_22933441
  intro M sf Cf p hM hcanon hpath hmax
  exact canonical_horizon_bound_of_short_travel hpath (htravel hM hcanon hpath hmax)

/-- The travel hypothesis restricted to canonical previous records whose
twin-primality has already been proved. -/
def TwinPrimeTravelBoundFrom (lower : Nat) : Prop :=
  ∀ {M sf Cf p : Nat}, lower ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M

/-- Proving travel only after canonical greater twin primes suffices for
both the unrestricted index theorem and the twin-primality target. -/
theorem record_index_and_twin_prime_of_twin_travel_bound_from_22933441
    (htravel : TwinPrimeTravelBoundFrom 22933441) :
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
        canonical_next_record_factors_of_short_travel (by omega) hMcanon hstartMax
          (fun hpath hp => htravel hM hMtwin hMcanon hpath hp)
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

theorem target_of_twin_prime_travel_bound_from_22933441
    (htravel : TwinPrimeTravelBoundFrom 22933441) : Target := by
  intro R hR hrecord
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  exact (record_index_and_twin_prime_of_twin_travel_bound_from_22933441
    htravel hR hn hd hprior).2

theorem target_of_travel_bound_from_22933441
    (htravel : CanonicalTravelBoundFrom 22933441) : Target := by
  apply target_of_twin_prime_travel_bound_from_22933441
  intro M sf Cf p hM _ hcanon hpath hmax
  exact htravel hM hcanon hpath hmax

theorem target_of_event_count_bound_from_22933441
    (hcount : ∀ {M sf Cf p : Nat}, 22933441 ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 48 * (p * p) + 1 < M) : Target := by
  apply target_of_travel_bound_from_22933441
  intro M sf Cf p hM hcanon hpath hmax
  exact canonical_travel_bound_of_event_count (by omega) hcanon hpath hmax
    (hcount hM hcanon hpath hmax)

theorem target_for_records_le_45895573 {R : Nat}
    (hR : 5 < R) (hbound : R ≤ 45895573) (hrecord : IsDifferenceRecord R) :
    IsGreaterTwinPrime R := by
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  obtain ⟨_, hminus, hplus⟩ := record_index_and_factors_of_le_45895573 hR hbound hn hd hprior
  exact ⟨prime_of_no_proper_factor (by omega) hplus, prime_of_no_proper_factor (by omega) hminus⟩

/-- The first interval of the travel hypothesis is discharged by the
verified extension. Only previous records from `45895573` remain. -/
theorem record_index_and_twin_prime_of_twin_travel_bound_from_45895573
    (htravel : TwinPrimeTravelBoundFrom 45895573) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  apply record_index_and_twin_prime_of_twin_travel_bound_from_22933441
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_cases h : M < 45895573
  · exact canonical_travel_bound_on_verified_extension hM h hcanon hpath hmax
  · exact htravel (by omega) htwin hcanon hpath hmax

/-- A bound on the number of starts at horizons divisible by six can
replace a uniform bound on the total event count. -/
theorem record_index_and_twin_prime_of_six_cover_from_45895573
    (hcover : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf →
      ∃ cover : List Nat,
        (∀ j : Nat, IsReplayEventStart (M + 2) sf j → 6 ∣ D j → j ∈ cover) ∧
        2 * (6 * p + cover.length * (Nat.sqrt (4 * (3 * M + 4)) - 6)) ≤ M) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  apply record_index_and_twin_prime_of_twin_travel_bound_from_45895573
  intro M sf Cf p hM htwin hcanon hpath hmax
  obtain ⟨cover, hlist, hbudget⟩ := hcover hM htwin hcanon hpath hmax
  exact canonical_travel_bound_of_six_cover (by omega) hcanon hpath cover hlist hbudget

/-- It suffices to bound the short gaps and the long prime gaps on
prefixes that have not yet crossed the short-travel cutoff. -/
theorem record_index_and_twin_prime_of_residual_travel_from_45895573
    (hbudget : ∀ {M s C p total : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonResidualTravel (M + 2) (2 * M - 2) s C p total →
      IsAttainedPreviousMaximum M s → 2 * (s - (M + 2)) ≤ M →
      6 * (total + Nat.sqrt (4 * (3 * M + 4))) + 10 ≤ M) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  apply record_index_and_twin_prime_of_twin_travel_bound_from_45895573
  intro M sf Cf q hM htwin hcanon hpath hmax
  by_cases h : 2 * (sf - (M + 2)) ≤ M
  · exact h
  · obtain ⟨s, C, r, C', p, total, hcost, hstep, hr, _, hshort, _, _, hcross⟩ :=
      canonical_first_travel_crossing_residual hcanon hpath (by omega)
    have hstart := (moving_horizon_residual_travel_bound hcost).1
    have hsr := hstep.2.1
    have hmax' : IsAttainedPreviousMaximum M s :=
      ⟨fun j hj hjs => hmax.1 j hj (by omega), ⟨M + 2, by omega, hstart, hcanon⟩⟩
    have hle := hbudget hM htwin hcanon hcost hmax' hshort
    omega

/-- The finite first-use and excess budget suffices at every short
capped prefix. This route has no asymptotic threshold. -/
theorem record_index_and_twin_prime_of_excess_budget_from_45895573
    (hbudget : ∀ {M s C p first remaining excess : Nat},
      45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) s C [] p first →
      HasMovingHorizonTravelExcess (M + 2) (2 * M - 2) s C [] p remaining excess →
      IsAttainedPreviousMaximum M s → 2 * (s - (M + 2)) ≤ M →
      24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 9 * (C - (2 * M - 2)) + excess ≤ 12 * M) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  apply record_index_and_twin_prime_of_twin_travel_bound_from_45895573
  intro M sf Cf q hM htwin hcanon hpath hmax
  by_cases h : 2 * (sf - (M + 2)) ≤ M
  · exact h
  · obtain ⟨s, C, r, C', p, total, first, excess, hledger, _, hfirst, hstep, hr, _,
      hshort, _, _, hgap, hcross⟩ := canonical_first_travel_crossing_excess hcanon hpath (by omega)
    have hstart := (moving_horizon_travel_excess_bounds hledger).1
    have hsr := hstep.2.1
    have hmax' : IsAttainedPreviousMaximum M s :=
      ⟨fun j hj hjs => hmax.1 j hj (by omega), ⟨M + 2, by omega, hstart, hcanon⟩⟩
    have hle := hbudget hM htwin hcanon hfirst hledger hmax' hshort
    omega

end A166944Research
