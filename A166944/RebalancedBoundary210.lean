import A166944.RebalancedPeriodLoad210
import A166944.VerifiedBoundaryRecordExtension

/-! # A boundary for capped canonical replays

Use the linear combination `C + 216*(2*s-C)` of the horizon and the
index, with the same residue potential as the signed cost ledger.
The cofactor of a new record bounds how early it can occur inside
the horizon. At a quiet exit the boundary also leaves enough room to
certify primality of both horizon terms.
-/

open Finset

namespace A166944Research

def rebalancedBoundaryValue210 (s C : Nat) : Int :=
  432 * (s : Int) - 215 * (C : Int) + 18 * (rebalancedPotential210 s C : Int)

def rebalancedBoundaryLimit210 (M : Nat) : Int := 219 * (M : Int) - 2400

theorem moving_horizon_state_horizon_le_twice_index {s C : Nat} (state : IsMovingHorizonState s C) :
    C ≤ 2 * s := by
  have ha := a_le_three_mul s
  have hD := state.2.1
  have hsum : D s + s = a s := Nat.sub_add_cancel (index_le_a s)
  omega

theorem horizon_le_rebalanced_boundary_value210 {s C : Nat} (state : IsMovingHorizonState s C) :
    (C : Int) ≤ rebalancedBoundaryValue210 s C := by
  have := moving_horizon_state_horizon_le_twice_index state
  unfold rebalancedBoundaryValue210
  omega

/-- The offset at the hit is a positive multiple of the increment,
up to the parity-dependent constants in the gcd map. -/
theorem moving_horizon_index_offset_of_large_increment {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (large : 5 < d r) : C + d r ≤ 2 * r + 1 := by
  have hC := moving_horizon_state_horizon_le_twice_index step.1
  have hsr := step.2.1
  have hCe := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · obtain ⟨hr, hCdiv⟩ := moving_horizon_event_divisibility_even step rfl heven
    have hdiv := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hr 2) hCdiv
    have hsize := Nat.le_of_dvd (by omega : 0 < 2 * r - (C - 1)) hdiv
    omega
  · obtain ⟨hr, hCdiv⟩ := moving_horizon_event_divisibility_odd step rfl hodd
    have h2r := Nat.dvd_mul_left_of_dvd hr 2
    have hpos : C + 1 < 2 * (r - 2) := by
      by_cases h : C + 1 < 2 * (r - 2)
      · exact h
      · have hsize := Nat.le_of_dvd (by omega : 0 < C + 1 - 2 * (r - 2)) (Nat.dvd_sub hCdiv h2r)
        omega
    have hsize := Nat.le_of_dvd (by omega : 0 < 2 * (r - 2) - (C + 1)) (Nat.dvd_sub h2r hCdiv)
    omega

/-- A cofactor of at least three is available at every inside hit.
For a large increment its contribution to the horizon outweighs
the index gap that the same cofactor allows. -/
theorem rebalanced_boundary_value_ge_of_large_increment210 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (large : 864 ≤ d r) :
    219 * (d r : Int) - 2809 ≤ rebalancedBoundaryValue210 s C := by
  have hoffset := moving_horizon_index_offset_of_large_increment step (by omega)
  obtain ⟨v, hv, hC, _, hgap⟩ := moving_horizon_step_exact_cofactor_gap step
  have hsr := step.2.1
  have hlo := Nat.mul_le_mul_left (d r - 864) hv
  have hsplit : (d r - 864) * v + 864 * v = d r * v := by
    rw [← Nat.add_mul, Nat.sub_add_cancel large]
  unfold rebalancedBoundaryValue210
  omega

theorem moving_horizon_no_new_record_below_rebalanced_boundary210 {M s C r C' : Nat}
    (hM : 863 ≤ M) (odd : M % 2 = 1) (step : IsMovingHorizonStep s C r C')
    (below : rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M) : d r ≤ M := by
  by_cases hnew : d r ≤ M
  · exact hnew
  · have he := d_mod_two_eq_one_of_three_le (by have := step.1.1; have := step.2.1; omega : 3 ≤ r)
    have hlower := rebalanced_boundary_value_ge_of_large_increment210 step (by omega)
    unfold rebalancedBoundaryLimit210 at below
    omega

theorem rebalanced_boundary_step_increase_le210 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') :
    rebalancedBoundaryValue210 r C' - rebalancedBoundaryValue210 s C ≤
      (325 * (r - s) + 18863 : Nat) := by
  have hsr := step.2.1
  have hup := moving_horizon_step_update step
  have hgap := moving_horizon_step_gap_le_twice_increment step
  have state : IsMovingHorizonState r C' := step.2.2.2.2.2.2.2.2
  have hCe := state.2.1 ▸ D_mod_two_eq_zero_of_two_le state.1
  have hV := rebalanced_potential210_le r C' hCe
  unfold rebalancedBoundaryValue210
  omega

namespace ResidualPhaseEvent210

theorem rebalanced_boundary_increase_le_net_cost210 (event : ResidualPhaseEvent210) :
    rebalancedBoundaryValue210 event.hit event.nextHorizon -
      rebalancedBoundaryValue210 event.start event.horizon ≤
      18 * event.rebalancedNetCost - 17 * ((d event.hit - 1 : Nat) : Int) := by
  have hup := moving_horizon_step_update event.step
  have hsr := event.step.2.1
  unfold rebalancedBoundaryValue210 rebalancedNetCost potentialNetCost
  split
  · rename_i hd
    have h := moving_horizon_rebalanced_supported210 event.step hd
    omega
  · omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem rebalanced_boundary_long_composite_checked210 :
    ∀ (e : Fin 210) (f : Fin 15), e.val % 2 = 1 → ¬ 3 ∣ e.val → ¬ 5 ∣ e.val →
      5 < f.val → f.val ∣ e.val → f.val * f.val ≤ e.val → 215 * (e.val - 1) < 864 * f.val + 18648 →
      e.val = 49 ∨ e.val = 77 ∨ e.val = 91 ∨ e.val = 121 := by
  decide +kernel

/-- A step crossing the adjusted boundary has positive net cost.
A short gap allows increments through 107. A long gap allows
only three composite values. -/
theorem rebalanced_boundary_increasing_step_cases210 (event : ResidualPhaseEvent210)
    (increase : rebalancedBoundaryValue210 event.start event.horizon <
      rebalancedBoundaryValue210 event.hit event.nextHorizon) :
    ¬ d event.hit ∣ 210 ∧
      ((event.hit - event.start ≤ 10 ∧ d event.hit ≤ 107) ∨
        (10 < event.hit - event.start ∧
          (d event.hit = 49 ∨ d event.hit = 77 ∨ d event.hit = 121 ∨ NoProperFactor (d event.hit)))) := by
  have hnet := event.rebalanced_boundary_increase_le_net_cost210
  have hu : ¬ d event.hit ∣ 210 := by
    intro hd
    simp [potentialNetCost, hd] at hnet
    omega
  have hcost := event.rebalanced_net_cost_le_of_unsupported hu
  refine ⟨hu, ?_⟩
  by_cases hgap : event.hit - event.start ≤ 10
  · exact Or.inl ⟨hgap, by omega⟩
  refine Or.inr ⟨by omega, ?_⟩
  by_cases hp : NoProperFactor (d event.hit)
  · exact Or.inr (Or.inr (Or.inr hp))
  have hcomp := moving_horizon_long_composite_seven_growth event.step (by omega) hp
  have hup := moving_horizon_step_update event.step
  have he := d_mod_two_eq_one_of_three_le (by have := event.step.1.1; have := event.step.2.1; omega : 3 ≤ event.hit)
  have hsmall : d event.hit < 210 := by omega
  have h3 : ¬ 3 ∣ d event.hit := by
    intro h
    have := moving_horizon_step_gap_le_twice_increment_factor event.step (by decide : 1 < 3) h
    omega
  have h5 : ¬ 5 ∣ d event.hit := by
    intro h
    have := moving_horizon_step_gap_le_twice_increment_factor event.step (by decide : 1 < 5) h
    omega
  obtain ⟨f, hf, hdiv, hsq⟩ := exists_small_factor_of_composite hp
  have hfactorGap := moving_horizon_step_gap_le_twice_increment_factor event.step hf hdiv
  have hfgt : 5 < f := by omega
  have hf15 : f < 15 := by
    by_cases h : f < 15
    · exact h
    · have := Nat.mul_le_mul (show 15 ≤ f by omega) (show 15 ≤ f by omega)
      omega
  have hfactorBudget : 215 * (d event.hit - 1) < 864 * f + 18648 := by
    have hr := event.step.2.1
    have state : IsMovingHorizonState event.hit event.nextHorizon := event.step.2.2.2.2.2.2.2.2
    have hCe := state.2.1 ▸ D_mod_two_eq_zero_of_two_le state.1
    have hV := rebalanced_potential210_le event.hit event.nextHorizon hCe
    unfold rebalancedBoundaryValue210 at increase
    omega
  rcases rebalanced_boundary_long_composite_checked210 ⟨d event.hit, hsmall⟩ ⟨f, hf15⟩
      he h3 h5 hfgt hdiv hsq hfactorBudget with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · change d event.hit = 91 at h
    have hclip : 1 < Nat.gcd (d event.hit) 210 := by rw [h]; decide
    have entry : (d event.hit, 0) ∈ rebalancedClippedCostCaps210 (Nat.gcd (d event.hit) 210) := by
      rw [h]
      decide
    have hcap := moving_horizon_rebalanced_clipped_cost_cap210 event.step hclip entry
    have hr := event.step.2.1
    unfold rebalancedBoundaryValue210 at increase
    omega
  · exact Or.inr (Or.inr (Or.inl h))

end ResidualPhaseEvent210

private theorem rebalanced_boundary_sqrt_le210 {M C : Nat}
    (hM : 11751795061 ≤ M) (hC : C ≤ 219 * M) :
    3600 * Nat.sqrt (4 * (C + 1)) ≤ M := by
  let q := Nat.sqrt (4 * (C + 1))
  change 3600 * q ≤ M
  have hq : q * q ≤ 877 * M := Nat.le_trans (Nat.sqrt_le (4 * (C + 1))) (by omega)
  apply Nat.mul_self_le_mul_self_iff.mp
  calc
    (3600 * q) * (3600 * q) = (3600 * 3600) * (q * q) := by ac_rfl
    _ ≤ (3600 * 3600) * (877 * M) := Nat.mul_le_mul_left _ hq
    _ = 11365920000 * M := by rw [← Nat.mul_assoc]
    _ ≤ M * M := Nat.mul_le_mul_right _ (by omega)

theorem rebalanced_boundary_crossing_gap210 {M s C r C' : Nat}
    (hM : 11751795061 ≤ M) (step : IsMovingHorizonStep s C r C')
    (below : rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M) :
    3600 * (r - s) ≤ M := by
  have hC := horizon_le_rebalanced_boundary_value210 step.1
  unfold rebalancedBoundaryLimit210 at below
  exact Nat.le_trans (Nat.mul_le_mul_left _ (moving_horizon_step_gap_le_sqrt step (Nat.le_refl C)))
    (rebalanced_boundary_sqrt_le210 hM (by omega))

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

noncomputable def rebalancedBoundaryBudget210 : Int :=
  180 * (trace.totalCappedFirstPayment : Int) + 60 * trace.rebalancedCreditDebt -
    50 * ((D sf - D s : Nat) : Int)

theorem rebalanced_boundary_budget_le_periods210 (cover : trace.RebalancedAnchorComponents)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    trace.rebalancedBoundaryBudget210 ≤
      (180 * trace.totalCappedFirstPayment + ∑ w ∈ cover.windows, trace.rebalancedPeriodExcess w : Nat) -
        170 * (cover.unusedGrowth : Int) - 180 * ((∑ i, trace.rebalancedNegativeCost i : Nat) : Int) := by
  have h := trace.rebalanced_credit_debt_scaled_le_horizon_and_period_excess210 cover delta
  unfold rebalancedBoundaryBudget210
  omega

end ResidualPhaseTrace210

theorem rebalanced_boundary_increase_le_budget210 {M s C p first : Nat} {balance : Int}
    (hM : 5 < M) (canonical : d (M + 2) = M)
    (path : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) :
    10 * (rebalancedBoundaryValue210 s C - rebalancedBoundaryValue210 (M + 2) (2 * M - 2)) ≤
      trace.rebalancedBoundaryBudget210 + 729812160 := by
  have hstart := (canonical_increment_coordinates hM canonical).2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have ⟨hindex, hhorizon, _⟩ := moving_horizon_path_gap_le_three_growth path
  have htravel := trace.potential_travel_budget moving_horizon_rebalanced_supported210 path delta
  change ((24 * (s - (M + 2)) : Nat) : Int) + (rebalancedPotential210 s C : Int) ≤
    ((11 * (C - (2 * M - 2)) : Nat) : Int) + (rebalancedPotential210 (M + 2) (2 * M - 2) : Int) +
      ∑ i, (trace.event i).rebalancedNetCost at htravel
  have hnet := trace.rebalanced_net_cost_eq_credit_debt210
  have hstartup := trace.rebalanced_startup_cost_le
  unfold ResidualPhaseTrace210.rebalancedBoundaryBudget210 rebalancedBoundaryValue210
  rw [hstart, hend] at hnet ⊢
  omega

/-- The prefix before an upward crossing has already accumulated more
than `M/4` horizon growth from large relative gaps. -/
theorem rebalanced_boundary_crossing_large_gap_growth210 {M s C r C' p first : Nat} {balance : Int}
    (hM : 11751795061 ≤ M) (canonical : d (M + 2) = M)
    (path : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (step : IsMovingHorizonStep s C r C')
    (below : rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M)
    (cross : rebalancedBoundaryLimit210 M < rebalancedBoundaryValue210 r C')
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) :
    M < 4 * trace.growthAtLargeGaps := by
  have hstart := (canonical_increment_coordinates (by omega) canonical).2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have ⟨hindex, hhorizon, _⟩ := moving_horizon_path_gap_le_three_growth path
  have htravel := trace.travel_le_growth_and_large_gaps path delta
  have hgrowth := trace.growth_at_large_gaps_le delta
  rw [hstart, hend] at hgrowth
  have hCe := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have hV := rebalanced_potential210_le s C hCe
  have hgap := rebalanced_boundary_crossing_gap210 hM step below
  have hincrease := rebalanced_boundary_step_increase_le210 step
  have hpre : rebalancedBoundaryValue210 s C ≤ 2 * (M : Int) + 865 * (trace.growthAtLargeGaps : Int) + 20374 := by
    unfold rebalancedBoundaryValue210
    omega
  unfold rebalancedBoundaryLimit210 at cross
  omega

theorem rebalanced_boundary_excludes_crossing_of_budget210 {M s C r C' p first : Nat} {balance : Int}
    (hM : 11751795061 ≤ M) (canonical : d (M + 2) = M)
    (path : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (step : IsMovingHorizonStep s C r C')
    (below : rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (budget : trace.rebalancedBoundaryBudget210 ≤ (2169 * M : Nat)) :
    rebalancedBoundaryValue210 r C' ≤ rebalancedBoundaryLimit210 M := by
  have hgap := rebalanced_boundary_crossing_gap210 hM step below
  have hincrease := rebalanced_boundary_step_increase_le210 step
  have hcost := rebalanced_boundary_increase_le_budget210 (by omega) canonical path trace delta
  have hV := rebalanced_potential210_le (M + 2) (2 * M - 2) (by omega)
  have horigin : rebalancedBoundaryValue210 (M + 2) (2 * M - 2) ≤ 2 * (M : Int) + 19942 := by
    unfold rebalancedBoundaryValue210
    omega
  unfold rebalancedBoundaryLimit210
  omega

/-- It suffices to pay the boundary budget on capped prefixes just before
an upward crossing, with the necessary large-gap growth already present. -/
def RebalancedBoundaryCondition210 : Prop :=
  ∀ {M s C r C' p first : Nat} {balance : Int},
    11751795061 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p →
    IsMovingHorizonStep s C r C' → IsAttainedPreviousMaximum M r →
    rebalancedBoundaryValue210 s C ≤ rebalancedBoundaryLimit210 M →
    rebalancedBoundaryLimit210 M < rebalancedBoundaryValue210 r C' →
    ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
      (∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) →
      M < 4 * trace.growthAtLargeGaps →
      trace.rebalancedBoundaryBudget210 ≤ (2169 * M : Nat)

private theorem exists_rebalanced_boundary_crossing210 {s C sf Cf n : Nat} {limit : Int}
    (path : HasMovingHorizonPathTo s C sf Cf n)
    (start : rebalancedBoundaryValue210 s C ≤ limit) (finish : limit < rebalancedBoundaryValue210 sf Cf) :
    ∃ t H r H' p : Nat, HasMovingHorizonPathTo s C t H p ∧ IsMovingHorizonStep t H r H' ∧
      r ≤ sf ∧ rebalancedBoundaryValue210 t H ≤ limit ∧ limit < rebalancedBoundaryValue210 r H' := by
  induction n generalizing s C with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := path
    omega
  | succ n ih =>
    obtain ⟨state, u, U, step, tail⟩ := path
    by_cases h : rebalancedBoundaryValue210 u U ≤ limit
    · obtain ⟨t, H, r, H', p, hprefix, next, hr, hb, hc⟩ := ih tail h
      exact ⟨t, H, r, H', p + 1, ⟨state, u, U, step, hprefix⟩, next, hr, hb, hc⟩
    · exact ⟨s, C, u, U, 0, ⟨rfl, rfl, state⟩, step, moving_horizon_path_index_le tail, start, by omega⟩

theorem canonical_rebalanced_boundary_of_condition210 (bound : RebalancedBoundaryCondition210)
    {M sf Cf n : Nat} (hM : 11751795061 ≤ M) (twin : IsGreaterTwinPrime M)
    (canonical : d (M + 2) = M)
    (path : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf n)
    (cap : IsAttainedPreviousMaximum M sf) : rebalancedBoundaryValue210 sf Cf ≤ rebalancedBoundaryLimit210 M := by
  by_contra h
  have hV := rebalanced_potential210_le (M + 2) (2 * M - 2) (by omega)
  have hstart : rebalancedBoundaryValue210 (M + 2) (2 * M - 2) ≤ rebalancedBoundaryLimit210 M := by
    unfold rebalancedBoundaryValue210 rebalancedBoundaryLimit210
    omega
  obtain ⟨s, C, r, C', p, hprefix, step, hr, below, cross⟩ :=
    exists_rebalanced_boundary_crossing210 path hstart (by omega)
  have hr0 := moving_horizon_path_index_le hprefix
  have hsr := step.2.1
  have hrCap : IsAttainedPreviousMaximum M r :=
    ⟨fun j hj hjr => cap.1 j hj (hjr.trans hr), ⟨M + 2, by omega, by omega, canonical⟩⟩
  obtain ⟨first, balance, ledger⟩ := moving_horizon_residual_phase_balances210 residualHorizonPhase210 [] hprefix
  obtain ⟨trace, delta⟩ := residual_phase_trace_with_delta210 ledger
  have hlarge := rebalanced_boundary_crossing_large_gap_growth210 hM canonical hprefix step below cross trace delta
  have hbudget := bound hM twin canonical hprefix step hrCap below cross trace delta hlarge
  exact (not_lt_of_ge (rebalanced_boundary_excludes_crossing_of_budget210 hM canonical hprefix step below
    trace delta hbudget)) cross

theorem canonical_next_record_factors_of_rebalanced_boundary210 (bound : RebalancedBoundaryCondition210)
    {M : Nat} (hM : 11751795061 ≤ M) (twin : IsGreaterTwinPrime M) (canonical : d (M + 2) = M)
    (cap : IsAttainedPreviousMaximum M (M + 2)) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have hD := (canonical_increment_coordinates (by omega) canonical).2.1
  have state : IsMovingHorizonState (M + 2) (2 * M - 2) := ⟨by omega, hD, by omega⟩
  obtain ⟨s, C, n, path, hcap, hexit⟩ := capped_moving_horizon_eventual_exit state cap
  have below := canonical_rebalanced_boundary_of_condition210 bound hM twin canonical path hcap
  have hstate := moving_horizon_path_endpoint path
  have hClo := (moving_horizon_path_gap_le_three_growth path).2.1
  rcases hexit with ⟨_, quiet⟩ | ⟨r, C', step, newRecord⟩
  · have hCvalue := horizon_le_rebalanced_boundary_value210 hstate
    have hbound := below
    unfold rebalancedBoundaryLimit210 at hbound
    have hC : C ≤ 219 * M := by omega
    have hsqrt := rebalanced_boundary_sqrt_le210 hM hC
    have hsmall := Nat.sqrt_le_sqrt (by omega : C + 1 ≤ 4 * (C + 1))
    have hlong : 2 * Nat.sqrt (C + 1) < C - s := by
      unfold rebalancedBoundaryValue210 at hbound
      omega
    obtain ⟨hnew, hpre, hd, _⟩ := canonical_quiet_return_next_record (by omega) hClo hstate hcap quiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate quiet hlong
    exact ⟨C, hnew, hpre, hd, hminus, hplus⟩
  · have hodd := attained_previous_maximum_value_mod_two_eq_one hcap (by omega : 5 < M)
    exact False.elim (not_lt_of_ge (moving_horizon_no_new_record_below_rebalanced_boundary210
      (by omega) hodd step below) newRecord)

theorem record_index_and_twin_prime_of_rebalanced_boundary210 (bound : RebalancedBoundaryCondition210)
    {R n : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) : n = R + 2 ∧ IsGreaterTwinPrime R := by
  revert hR hn hd hprior
  induction n using Nat.strongRecOn generalizing R with
  | ind n ih =>
    intro hR hn hd hprior
    by_cases h : R ≤ 11751795061
    · exact record_index_and_twin_prime_of_le_11751795061 hR h hn hd hprior
    obtain ⟨hverified, hmaxVerified, _⟩ := verified_prefix_through_11751795063
    have hnLarge : 11751795063 < n := by
      by_contra hle
      have hcap := hmaxVerified.1 n hn (by omega)
      omega
    obtain ⟨M, hmax⟩ := attained_previous_maximum_exists (n - 1) (by omega)
    have hM : 11751795061 ≤ M := by
      have hcap := hmax.1 11751795063 (by decide) (by omega)
      omega
    obtain ⟨m, hm, hmn, hdm, hMprior⟩ := attained_previous_maximum_first_occurrence hmax
    obtain ⟨hmi, htwin⟩ := ih m (by omega) (by omega : 5 < M) hm hdm hMprior
    have canonical : d (M + 2) = M := by rwa [← hmi]
    have hstartMax : IsAttainedPreviousMaximum M (M + 2) :=
      ⟨fun j hj hjM => hmax.1 j hj (by omega), ⟨M + 2, by omega, le_rfl, canonical⟩⟩
    have hMlt : M < R := by simpa only [hdm] using hprior m hm (by omega)
    obtain ⟨C, hnew, hpre, hdnew, hminus, hplus⟩ :=
      canonical_next_record_factors_of_rebalanced_boundary210 bound hM htwin canonical hstartMax
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

theorem target_of_rebalanced_boundary210 (bound : RebalancedBoundaryCondition210) : Target := by
  rintro R hR ⟨n, hn, hd, hprior⟩
  exact (record_index_and_twin_prime_of_rebalanced_boundary210 bound hR hn hd hprior).2

end A166944Research
