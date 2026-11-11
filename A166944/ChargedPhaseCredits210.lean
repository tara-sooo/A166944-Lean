import A166944.TravelCharged210

/-!
# Short travel from the improved credit balances

The new balances charge four times separator growth. Their first-phase
gap mass is unchanged, so the existing first-phase sublinearity theorem
still applies. Allocation existence remains an explicit hypothesis.
-/

open Finset

namespace A166944Research

private theorem charged_crossing_gap_bound {M : Nat} (hM : 147456 ≤ M) :
    96 * Nat.sqrt (4 * (3 * M + 4)) ≤ M := by
  let Q := Nat.sqrt (4 * (3 * M + 4))
  change 96 * Q ≤ M
  apply Nat.mul_self_le_mul_self_iff.mp
  have hQ : Q * Q ≤ 4 * (3 * M + 4) := Nat.sqrt_le _
  calc
    (96 * Q) * (96 * Q) = (96 * 96) * (Q * Q) := by ac_rfl
    _ ≤ (96 * 96) * (16 * M) := Nat.mul_le_mul_left _ (by omega)
    _ = 147456 * M := by omega
    _ ≤ M * M := Nat.mul_le_mul_right _ hM

set_option maxRecDepth 4096 in
/-- The former funded certificate applies to the improved balances too.
In particular the zero-funding case needs only ordinary negative supply. -/
theorem canonical_travel_of_charged_prefix_allocations210 (slots multiplier : Nat) :
    ∃ threshold : Nat, ∀ {M sf Cf q : Nat} (phase : Nat → Nat → Fin slots),
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q →
      IsAttainedPreviousMaximum M sf →
      (∀ {s C p first : Nat} {balance : Int},
        HasMovingHorizonChargedPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance →
        2 * (s - (M + 2)) ≤ M →
        IsAttainedPreviousMaximum M s →
        ∃ (n m : Nat) (cost : Fin n → Int) (key : Fin n → Fin (631 * 420))
          (eligible : Fin n → Fin m → Prop),
          (∑ i, cost i) = balance ∧
            Nonempty (FundedPhaseCreditAllocation210 cost key eligible first multiplier)) →
      2 * (sf - (M + 2)) ≤ M := by
  obtain ⟨firstThreshold, hfirst⟩ :=
    canonical_first_prime_phase_travel_sublinear slots (4 * (24 + multiplier)) (by omega)
  refine ⟨max firstThreshold (max 147456 (4 * (smallPhaseStartupBound210 + 1315))), ?_⟩
  intro M sf Cf q phase hM hcanon hpath hmax hallocate
  have hMF : firstThreshold ≤ M := le_trans (le_max_left _ _) hM
  have hMLarge : 147456 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMStartup : 4 * (smallPhaseStartupBound210 + 1315) ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, balance, hledger, hstep, hr, _, hs, _, hgap, hcross⟩ :=
      canonical_first_crossing_requires_charged_phase_balances210 phase hcanon hpath (by omega)
    obtain ⟨original, horiginal⟩ := charged_phase_balances210_original hledger
    have hstart := moving_horizon_path_index_le (moving_horizon_phase_balances210_path horiginal)
    have hsr := hstep.2.1
    have hs_sf : s ≤ sf := (Nat.le_of_lt hsr).trans hr
    have hmax' : IsAttainedPreviousMaximum M s :=
      ⟨fun j hj hjs => hmax.1 j hj (hjs.trans hs_sf),
        ⟨M + 2, Nat.le_add_left 2 M, hstart, hcanon⟩⟩
    obtain ⟨n, m, cost, key, eligible, hsum, ⟨certificate⟩⟩ := hallocate hledger hs hmax'
    have hF := hfirst hMF hcanon horiginal hs
    have hbound := funded_phase_credit_allocation_bound210 certificate
    rw [hsum] at hbound
    have hQ := charged_crossing_gap_bound hMLarge
    have hg := (Nat.mul_le_mul_left 96 hgap).trans hQ
    have hF' : 4 * (24 * first + multiplier * first) ≤ M := by
      simpa only [Nat.mul_assoc, Nat.add_mul] using hF
    omega

end A166944Research
