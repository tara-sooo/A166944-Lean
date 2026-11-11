import A166944.ResidualFirstPayment210
import A166944.VerifiedRecordExtension

/-! # Horizon growth and gap constraints at the first travel crossing -/

open Finset

namespace A166944Research

private def gapPotential6 (s C : Nat) : Nat :=
  if (C % 6 = 0 ∧ s % 6 = 2) ∨ (C % 6 = 2 ∧ s % 6 = 5) ∨
      (C % 6 = 4 ∧ s % 6 = 0) then 2 else 0

private theorem gapPotential6_le (s C : Nat) : gapPotential6 s C ≤ 2 := by
  unfold gapPotential6
  split <;> decide

private theorem moving_horizon_step_gap_potential6 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') :
    2 * (r - s) + gapPotential6 r C' ≤ 5 * (d r - 1) + gapPotential6 s C := by
  have hs2 := step.1.1
  have hsr := step.2.1
  have hCpos := step.1.2.2
  have hCe := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have hupdate := moving_horizon_step_update step
  have hgap := moving_horizon_step_gap_le_twice_increment step
  have hcap := gapPotential6_le r C'
  by_cases hthree : d r = 3
  · have hshape : (C % 6 = 4 ∧ r % 6 = 0 ∧ C' % 6 = 0) ∨
        (C % 6 = 2 ∧ r % 6 = 5 ∧ C' % 6 = 4) := by
      rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
      · obtain ⟨hdivr, hdivC⟩ := moving_horizon_event_divisibility_even step hthree heven
        have hr3 := Nat.mod_eq_zero_of_dvd hdivr
        have hC3 := Nat.mod_eq_zero_of_dvd hdivC
        exact Or.inl ⟨by omega, by omega, by omega⟩
      · obtain ⟨hdivr, hdivC⟩ := moving_horizon_event_divisibility_odd step hthree hodd
        have hr3 := Nat.mod_eq_zero_of_dvd hdivr
        have hC3 := Nat.mod_eq_zero_of_dvd hdivC
        exact Or.inr ⟨by omega, by omega, by omega⟩
    have hafter : gapPotential6 r C' = 0 := by
      rcases hshape with ⟨_, hr, hC'⟩ | ⟨_, hr, hC'⟩ <;> simp [gapPotential6, hr, hC']
    by_cases hlong : r - s = 6
    · have hbefore : gapPotential6 s C = 2 := by
        rcases hshape with ⟨hC, hr, _⟩ | ⟨hC, hr, _⟩
        · simp [gapPotential6, hC, show s % 6 = 0 by omega]
        · simp [gapPotential6, hC, show s % 6 = 5 by omega]
      omega
    · omega
  by_cases hfive : d r = 5
  · by_cases hlong : r - s = 10
    · have hdiv : 6 ∣ C := by
        by_contra h
        have := moving_horizon_gap_le_six_of_six_not_dvd step h
        omega
      have hC0 := Nat.mod_eq_zero_of_dvd hdiv
      have hC'4 : C' % 6 = 4 := by omega
      have hparity : r % 6 = 0 ↔ s % 6 = 2 := by omega
      have hpot : gapPotential6 r C' = gapPotential6 s C := by
        simp [gapPotential6, hC0, hC'4, hparity]
      omega
    · omega
  have he3 := moving_horizon_step_event_ge_three step
  have hodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ r)
  omega

namespace ResidualPhaseEvent210

def growthWithLargeGap (event : ResidualPhaseEvent210) : Nat :=
  if d event.hit - 1 < 3 * (event.hit - event.start + 1) then d event.hit - 1 else 0

/-- A large gap relative to its horizon growth is either short with
increment at most 33, or ends at a prime with a bounded cofactor product. -/
theorem large_relative_gap_cases (event : ResidualPhaseEvent210)
    (large : d event.hit - 1 < 3 * (event.hit - event.start + 1)) :
    (event.hit - event.start ≤ 10 ∧ d event.hit ≤ 33) ∨
      (10 < event.hit - event.start ∧ NoProperFactor (d event.hit) ∧
        (d event.hit - 4) * d event.hit < 6 * (event.horizon + 1)) := by
  by_cases hshort : event.hit - event.start ≤ 10
  · exact Or.inl ⟨hshort, by omega⟩
  have hlong : 10 < event.hit - event.start := by omega
  have hprime : NoProperFactor (d event.hit) := by
    by_contra hcomp
    have hgap := moving_horizon_long_composite_seven_growth event.step hlong hcomp
    have hupdate := moving_horizon_step_update event.step
    omega
  have hprod := moving_horizon_step_gap_mul_increment_le_twice_horizon event.step
  have hpositive : 0 < d event.hit := by have := event.step.2.2.2.1; omega
  have hlt := Nat.mul_lt_mul_of_pos_right
    (show d event.hit - 4 < 3 * (event.hit - event.start) by omega) hpositive
  rw [Nat.mul_assoc] at hlt
  exact Or.inr ⟨hlong, hprime, by omega⟩

private def gapGrowthPathValue (x : Nat) : Int :=
  6 * (x : Int) + 3 * (gapPotential6 x (D x) : Int) - 2 * (D x : Int)

private theorem gap_growth_path_value_step (event : ResidualPhaseEvent210) :
    gapGrowthPathValue event.hit - gapGrowthPathValue event.start ≤
      13 * (event.growthWithLargeGap : Int) := by
  have hsr := event.step.2.1
  have hupdate := moving_horizon_step_update event.step
  have hstart := event.step.1.2.1
  have hhit := event.step.2.2.2.2.2.2.2.2.2.1
  unfold gapGrowthPathValue growthWithLargeGap
  rw [hstart, hhit]
  split
  · have hgap := moving_horizon_step_gap_potential6 event.step
    omega
  · have hpot := gapPotential6_le event.hit event.nextHorizon
    omega

end ResidualPhaseEvent210

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- Growth on events whose gap plus one exceeds a third of their own growth. -/
def growthAtLargeGaps : Nat := ∑ i, (trace.event i).growthWithLargeGap

theorem growth_at_large_gaps_le
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    trace.growthAtLargeGaps ≤ D sf - D s := by
  rw [← trace.sum_horizon_growth_of_delta210 delta]
  apply Finset.sum_le_sum
  intro i _
  unfold ResidualPhaseEvent210.growthWithLargeGap
  split <;> omega

theorem growth_at_large_gaps_le_count {U cutoff : Nat}
    (horizon : ∀ i, (trace.event i).horizon ≤ U)
    (hcutoff : 33 < cutoff) (product : 6 * (U + 1) ≤ (cutoff - 4) * cutoff) :
    trace.growthAtLargeGaps ≤ (cutoff - 2) *
      (Finset.univ.filter fun i =>
        d (trace.event i).hit - 1 < 3 * ((trace.event i).hit - (trace.event i).start + 1)).card := by
  unfold growthAtLargeGaps ResidualPhaseEvent210.growthWithLargeGap
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i =>
          d (trace.event i).hit - 1 < 3 * ((trace.event i).hit - (trace.event i).start + 1)),
          (cutoff - 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hgap := (Finset.mem_filter.mp hi).2
      have hsmall : d (trace.event i).hit < cutoff := by
        rcases (trace.event i).large_relative_gap_cases hgap with hshort | hlong
        · omega
        · by_contra hlarge
          have hmul := Nat.mul_le_mul (show cutoff - 4 ≤ d (trace.event i).hit - 4 by omega)
            (show cutoff ≤ d (trace.event i).hit by omega)
          have hbound := horizon i
          omega
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem travel_le_growth_and_large_gaps {C Cf : Nat}
    (path : HasMovingHorizonPathTo s C sf Cf n)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    6 * (sf - s) ≤ 2 * (Cf - C) + 13 * trace.growthAtLargeGaps + 6 := by
  have hstart : D s = C := by
    cases n with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have ⟨hsf, hCf, _⟩ := moving_horizon_path_gap_le_three_growth path
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (trace.event i).gap_growth_path_value_step)
  rw [delta ResidualPhaseEvent210.gapGrowthPathValue, ← Finset.mul_sum, ← Nat.cast_sum] at hsum
  change ResidualPhaseEvent210.gapGrowthPathValue sf - ResidualPhaseEvent210.gapGrowthPathValue s ≤
    13 * (trace.growthAtLargeGaps : Int) at hsum
  unfold ResidualPhaseEvent210.gapGrowthPathValue at hsum
  rw [hstart, hend] at hsum
  have hcap := gapPotential6_le s C
  omega

end ResidualPhaseTrace210

/-- A first crossing needs growth, growth at large relative gaps, and
signed cost simultaneously. The signed lower bound keeps the actual
horizon and both endpoint potentials. -/
theorem rebalanced_first_crossing_growth_constraints210 {M s C r C' p first : Nat} {balance : Int}
    (hM : 5 < M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (step : IsMovingHorizonStep s C r C')
    (short : 2 * (s - (M + 2)) ≤ M) (cross : M < 2 * (r - (M + 2)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) :
    M < 5 * (C - (2 * M - 2)) + 2 * (r - s) + 2 ∧
      M < 13 * trace.growthAtLargeGaps + 6 * (r - s) + 16 ∧
      ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) ≤
        (∑ i, (trace.event i).rebalancedNetCost) +
          (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hs := moving_horizon_path_index_le path
  have hr := step.2.1
  have hbound := canonical_horizon_bound_of_short_travel path short
  have hCe := hend ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have hModd : M % 2 = 1 := canonical ▸ d_mod_two_eq_one_of_three_le (by omega)
  have htravel := trace.travel_le_growth_and_large_gaps path delta
  have hlarge := trace.growth_at_large_gaps_le delta
  rw [hstart, hend] at hlarge
  have hcost := trace.potential_travel_budget moving_horizon_rebalanced_supported210 path delta
  change ((24 * (s - (M + 2)) : Nat) : Int) + (rebalancedPotential210 s C : Int) ≤
    ((11 * (C - (2 * M - 2)) : Nat) : Int) + (rebalancedPotential210 (M + 2) (2 * M - 2) : Int) +
      ∑ i, (trace.event i).rebalancedNetCost at hcost
  exact ⟨by omega, by omega, by omega⟩

theorem crossing_growth_ratios_of_gap_bound210 {M G H g : Nat}
    (hM : 50000000 ≤ M) (gap : g ≤ Nat.sqrt (4 * (3 * M + 4)))
    (growth : M < 5 * G + 2 * g + 2) (largeGapGrowth : M < 13 * H + 6 * g + 16) :
    100 * M < 501 * G ∧ M < 14 * H := by
  have hgap := (Nat.mul_le_mul_left 1536 gap).trans (fifty_million_sqrt_budget hM)
  exact ⟨by omega, by omega⟩

/-- The signed upper bound on the remaining actual crossings after the
finite certificates and the two growth constraints are applied. -/
def RebalancedRemainingCrossingCondition210 : Prop :=
  ∀ {M s C r C' p first : Nat} {balance : Int},
    367232911 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance →
    IsMovingHorizonStep s C r C' → 2 * (s - (M + 2)) ≤ M → M < 2 * (r - (M + 2)) →
    r - s ≤ Nat.sqrt (4 * (3 * M + 4)) → IsAttainedPreviousMaximum M r →
    ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
      (∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) →
      M < 5 * (C - (2 * M - 2)) + 2 * (r - s) + 2 →
      M < 13 * trace.growthAtLargeGaps + 6 * (r - s) + 16 →
      (∑ i, (trace.event i).rebalancedNetCost) +
        (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
          ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int)

theorem twin_travel_of_rebalanced_remaining_crossings210
    (bound : RebalancedRemainingCrossingCondition210) : TwinPrimeTravelBoundFrom 367232911 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_contra hnot
  obtain ⟨s, C, r, C', q, first, balance, hledger, hstep, hr, _, hshort, hcross, hgap, _⟩ :=
    canonical_first_crossing_requires_residual_phase_balances210
      residualHorizonPhase210 hcanon hpath (Nat.lt_of_not_ge hnot)
  obtain ⟨trace, hdelta⟩ := residual_phase_trace_with_delta210 hledger
  have hstart := moving_horizon_path_index_le (residual_phase_balances210_path hledger)
  have hsr := hstep.2.1
  have hrMax : IsAttainedPreviousMaximum M r :=
    ⟨fun j hj hjr => hmax.1 j hj (hjr.trans hr), ⟨M + 2, by omega, by omega, hcanon⟩⟩
  obtain ⟨hgrowth, hlarge, hlower⟩ :=
    rebalanced_first_crossing_growth_constraints210 (by omega) hcanon hledger hstep hshort hcross trace hdelta
  exact (not_lt_of_ge hlower)
    (bound hM htwin hcanon hledger hstep hshort hcross hgap hrMax trace hdelta hgrowth hlarge)

theorem target_of_rebalanced_remaining_crossings210
    (bound : RebalancedRemainingCrossingCondition210) : Target :=
  target_of_twin_travel_from_fifty_million
    (twin_travel_from_367232911 (twin_travel_of_rebalanced_remaining_crossings210 bound))

end A166944Research
