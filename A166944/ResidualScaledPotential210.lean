import A166944.ResidualGrowthAllocation210
import A166944.TwinCrossingBudget210

/-! # A smaller potential for the signed crossing budget -/

open Finset

namespace A166944Research

def IsTravelPotential210 (potential : Nat → Nat → Nat) : Prop :=
  ∀ {s C r C' : Nat}, IsMovingHorizonStep s C r C' → d r ∣ 210 →
    24 * (r - s) + potential r C' ≤ 11 * (d r - 1) + potential s C

def scaledPotential210 (s C : Nat) : Nat := 8 * supportedPotential210 s C / 9

theorem scaled_potential210_le (s C : Nat) (heven : C % 2 = 0) : scaledPotential210 s C ≤ 1120 := by
  have h := (supported_excess_and_potential210_bounds s C heven).2
  unfold scaledPotential210
  omega

theorem moving_horizon_supported210_scaled_potential {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (supported : d r ∣ 210) :
    24 * (r - s) + scaledPotential210 r C' ≤ 11 * (d r - 1) + scaledPotential210 s C := by
  have htable := moving_horizon_supported210_travel_potential step supported
  have hgap := moving_horizon_step_gap_le_twice_increment step
  have he := step.2.2.2.1
  have hodd := d_mod_two_eq_one_of_three_le (show 3 ≤ r by have := step.1.1; have := step.2.1; omega)
  unfold scaledPotential210
  omega

namespace ResidualPhaseEvent210

def potentialNetCost (event : ResidualPhaseEvent210) (potential : Nat → Nat → Nat) : Int :=
  if d event.hit ∣ 210 then 0 else
    (24 * (event.hit - event.start) : Nat) + (potential event.hit event.nextHorizon : Int) -
      (potential event.start event.horizon : Int) - 11 * ((d event.hit - 1 : Nat) : Int)

theorem potential_net_cost_le_of_unsupported (event : ResidualPhaseEvent210) {potential : Nat → Nat → Nat}
    {cap : Nat} (hcap : potential event.hit event.nextHorizon ≤ cap) (hu : ¬ d event.hit ∣ 210) :
    event.potentialNetCost potential ≤ ((24 * (event.hit - event.start) + cap : Nat) : Int) -
      11 * ((d event.hit - 1 : Nat) : Int) := by
  rw [potentialNetCost, if_neg hu]
  omega

/-- Supported events are covered by the scaled potential. For the other
events, keep the entire signed difference, including any first-use gap. -/
def scaledNetCost (event : ResidualPhaseEvent210) : Int :=
  if d event.hit ∣ 210 then 0 else
    (24 * (event.hit - event.start) : Nat) + (scaledPotential210 event.hit event.nextHorizon : Int) -
      (scaledPotential210 event.start event.horizon : Int) - 11 * ((d event.hit - 1 : Nat) : Int)

theorem scaled_net_cost_le_of_unsupported (event : ResidualPhaseEvent210) (hu : ¬ d event.hit ∣ 210) :
    event.scaledNetCost ≤ ((24 * (event.hit - event.start) + 1120 : Nat) : Int) -
      11 * ((d event.hit - 1 : Nat) : Int) := by
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := scaled_potential210_le event.hit event.nextHorizon heven
  exact event.potential_net_cost_le_of_unsupported hV hu

theorem scaled_net_cost_positive_part_le (event : ResidualPhaseEvent210) :
    event.scaledNetCost.toNat ≤ 37 * d event.hit + 1131 := by
  by_cases hd : d event.hit ∣ 210
  · simp [scaledNetCost, hd]
  · have hcost := event.scaled_net_cost_le_of_unsupported hd
    have hgap := moving_horizon_step_gap_le_twice_increment event.step
    omega

/-- A single such event supplies enough negative credit for the
worst-case positive shortfall of any two prime reuse costs. -/
theorem scaled_net_cost_le_neg1536 (event : ResidualPhaseEvent210)
    (large : (event.hit - event.start ≤ 10 ∧ 265 ≤ d event.hit) ∨
      (¬ NoProperFactor (d event.hit) ∧ 665 ≤ d event.hit)) :
    event.scaledNetCost ≤ -1536 := by
  have hu : ¬ d event.hit ∣ 210 := by
    intro hd
    have h := Nat.le_of_dvd (by decide : 0 < 210) hd
    rcases large with hs | hc <;> omega
  have hcost := event.scaled_net_cost_le_of_unsupported hu
  rcases large with hs | hc
  · omega
  · by_cases hgap : 10 < event.hit - event.start
    · have h := moving_horizon_long_composite_seven_growth event.step hgap hc.1
      have hup := moving_horizon_step_update event.step
      omega
    · omega

private def potentialPathValue (potential : Nat → Nat → Nat) (x : Nat) : Int :=
  24 * (x : Int) + (potential x (D x) : Int) - 11 * (D x : Int)

private theorem potential_path_value_step (event : ResidualPhaseEvent210) {potential : Nat → Nat → Nat}
    (supported : IsTravelPotential210 potential) :
    potentialPathValue potential event.hit - potentialPathValue potential event.start ≤
      event.potentialNetCost potential := by
  have hs := event.step.1.2.1
  have hr := event.step.2.2.2.2.2.2.2.2.2.1
  have hsr := event.step.2.1
  have hup := moving_horizon_step_update event.step
  unfold potentialPathValue potentialNetCost
  rw [hs, hr]
  split
  · rename_i hd
    have h := supported event.step hd
    omega
  · omega

end ResidualPhaseEvent210

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

theorem potential_travel_budget {C Cf : Nat} {potential : Nat → Nat → Nat}
    (supported : IsTravelPotential210 potential)
    (path : HasMovingHorizonPathTo s C sf Cf n)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    ((24 * (sf - s) : Nat) : Int) + (potential sf Cf : Int) ≤
      ((11 * (Cf - C) : Nat) : Int) + (potential s C : Int) +
        ∑ i, (trace.event i).potentialNetCost potential := by
  have hstart : D s = C := by
    cases n with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have ⟨hsf, hCf, _⟩ := moving_horizon_path_gap_le_three_growth path
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (trace.event i).potential_path_value_step supported)
  rw [delta (ResidualPhaseEvent210.potentialPathValue potential)] at hsum
  unfold ResidualPhaseEvent210.potentialPathValue at hsum
  rw [hstart, hend] at hsum
  omega

theorem scaled_travel_budget {C Cf : Nat}
    (path : HasMovingHorizonPathTo s C sf Cf n)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    ((24 * (sf - s) : Nat) : Int) + (scaledPotential210 sf Cf : Int) ≤
      ((11 * (Cf - C) : Nat) : Int) + (scaledPotential210 s C : Int) +
        ∑ i, (trace.event i).scaledNetCost :=
  trace.potential_travel_budget moving_horizon_supported210_scaled_potential path delta

theorem unsupported_prime_ge_eleven {i j : Fin n} (reuse : trace.PrimeReuse i j) :
    11 ≤ d (trace.event j).hit := by
  let e := d (trace.event j).hit
  have he : 1 < e := (trace.event j).step.2.2.2.1
  have hr : 3 ≤ (trace.event j).hit := by
    have := (trace.event j).step.1.1
    have := (trace.event j).step.2.1
    omega
  have hodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  by_contra h
  have hcases : e = 3 ∨ e = 5 ∨ e = 7 ∨ e = 9 := by omega
  have hu : ¬ e ∣ 210 := reuse.unsupported
  have hp : NoProperFactor e := reuse.prime
  rcases hcases with h₃ | h₅ | h₇ | h₉
  · apply hu; rw [h₃]; decide
  · apply hu; rw [h₅]; decide
  · apply hu; rw [h₇]; decide
  · rw [h₉] at hp
    exact hp ⟨3, by decide⟩ (by decide) (by decide)

/-- Even the shortest possible drift for increment 11 pays its entire
positive scaled cost using two thirds of the growth. -/
theorem prime_reuse_scaled_net_cost_two_thirds {i j : Fin n} (reuse : trace.PrimeReuse i j) :
    3 * (trace.event j).scaledNetCost.toNat ≤ 2 * (trace.growthWindow i j).card := by
  have hsize := trace.unsupported_prime_ge_eleven reuse
  have hwidth := (trace.prime_reuse_drift reuse).2
  have hcost := (trace.event j).scaled_net_cost_positive_part_le
  simp only [growthWindow, Nat.card_Ico]
  omega

/-- All repeated long occurrences of one key can use their latest-anchor
windows together. The union counts every unit of growth at most once. -/
theorem same_key_scaled_reuses_two_thirds (selected : Finset (Fin n)) (key : Nat × Fin 420)
    (repeated : ∀ i ∈ selected, (trace.event i).LongPrime ∧ (trace.event i).phaseKey ∈ (trace.event i).seen)
    (sameKey : ∀ i ∈ selected, (trace.event i).phaseKey = key)
    (unsupported : ¬ key.1 ∣ 210) :
    3 * (∑ i ∈ selected, (trace.event i).scaledNetCost.toNat) ≤
      2 * (selected.biUnion (fun i => trace.growthWindow (trace.anchor i) i)).card := by
  have hdisjoint : (selected : Set (Fin n)).PairwiseDisjoint
      (fun i => trace.growthWindow (trace.anchor i) i) := by
    intro i hi j hj hne
    have hkey := (sameKey i hi).trans (sameKey j hj).symm
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact trace.same_key_long_reuse_growth_disjoint hij (repeated i hi).1 (repeated j hj).1 hkey
    · exact (trace.same_key_long_reuse_growth_disjoint hji (repeated j hj).1 (repeated i hi).1 hkey.symm).symm
  rw [Finset.card_biUnion hdisjoint, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have ⟨hl, hs⟩ := repeated i hi
  have ⟨hanchor, hkey⟩ := trace.anchor_of_seen_long hl hs
  have hd := congrArg Prod.fst (sameKey i hi)
  change d (trace.event i).hit = key.1 at hd
  exact trace.prime_reuse_scaled_net_cost_two_thirds ⟨hanchor, hkey, hl.2, fun h => unsupported (hd ▸ h)⟩

theorem two_reuses_scaled_net_cost_two_thirds_of_large {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hlarge : 35 ≤ max (d (trace.event c).hit) (d (trace.event e).hit)) :
    3 * ((trace.event c).scaledNetCost.toNat + (trace.event e).scaledNetCost.toNat) ≤
      2 * (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  have hp := (trace.prime_reuse_drift p).2
  have hq := (trace.prime_reuse_drift q).2
  have hcost₁ := (trace.event c).scaled_net_cost_positive_part_le
  have hcost₂ := (trace.event e).scaled_net_cost_positive_part_le
  have hleft := Finset.card_le_card (Finset.subset_union_left (s₂ := trace.growthWindow b e)
    (s₁ := trace.growthWindow a c))
  have hright := Finset.card_le_card (Finset.subset_union_right (s₁ := trace.growthWindow a c)
    (s₂ := trace.growthWindow b e))
  simp only [growthWindow, Nat.card_Ico] at hleft hright
  unfold growthWindow
  rcases le_total (d (trace.event c).hit) (d (trace.event e).hit) with h | h
  · rw [max_eq_right h] at hlarge
    omega
  · rw [max_eq_left h] at hlarge
    omega

/-- The negative credit in a union of growth windows. A pre-event
horizon `H` contributes at `H - 1`, so adjacent windows share no credit. -/
def scaledGrowthCredit (growth : Finset Nat) : Nat :=
  ∑ i ∈ Finset.univ.filter (fun i => (trace.event i).horizon - 1 ∈ growth),
    (-(trace.event i).scaledNetCost).toNat

theorem scaled_growth_credit_ge_of_event {growth : Finset Nat} {i : Fin n}
    (inside : (trace.event i).horizon - 1 ∈ growth) :
    (-(trace.event i).scaledNetCost).toNat ≤ trace.scaledGrowthCredit growth := by
  unfold scaledGrowthCredit
  apply Finset.single_le_sum (f := fun j : Fin n => (-(trace.event j).scaledNetCost).toNat)
    (fun _ _ => Nat.zero_le _)
  exact Finset.mem_filter.mpr ⟨mem_univ i, inside⟩

/-- Pay any finite set of positive costs from a common growth region
and its negative credit. A largest-increment reuse supplies the
lower bound on the region's width. -/
theorem scaled_costs_two_thirds_of_peak_reuse {a peak : Fin n}
    (reuse : trace.PrimeReuse a peak) (selected : Finset (Fin n)) (growth : Finset Nat)
    (inside : trace.growthWindow a peak ⊆ growth)
    (largest : ∀ i ∈ selected, d (trace.event i).hit ≤ d (trace.event peak).hit)
    (fits : selected.card * (37 * d (trace.event peak).hit + 1131) ≤
      140 * d (trace.event peak).hit + trace.scaledGrowthCredit growth) :
    3 * (∑ i ∈ selected, (trace.event i).scaledNetCost.toNat) ≤
      2 * growth.card + 3 * trace.scaledGrowthCredit growth := by
  have hwidth := (trace.prime_reuse_drift reuse).2
  have hcard := Finset.card_le_card inside
  simp only [growthWindow, Nat.card_Ico] at hcard
  have hsum : (∑ i ∈ selected, (trace.event i).scaledNetCost.toNat) ≤
      selected.card * (37 * d (trace.event peak).hit + 1131) := by
    calc
      _ ≤ ∑ _i ∈ selected, (37 * d (trace.event peak).hit + 1131) := by
        apply Finset.sum_le_sum
        intro i hi
        have hcost := (trace.event i).scaled_net_cost_positive_part_le
        have hsize := largest i hi
        omega
      _ = _ := by simp
  omega

theorem two_scaled_costs_of_enclosed_credit {a peak creditEvent : Fin n}
    (reuse : trace.PrimeReuse a peak) (selected : Finset (Fin n)) (growth : Finset Nat)
    (inside : trace.growthWindow a peak ⊆ growth)
    (largest : ∀ i ∈ selected, d (trace.event i).hit ≤ d (trace.event peak).hit)
    (count : selected.card ≤ 2) (enclosed : (trace.event creditEvent).horizon - 1 ∈ growth)
    (credit : (trace.event creditEvent).scaledNetCost ≤ -1536) :
    3 * (∑ i ∈ selected, (trace.event i).scaledNetCost.toNat) ≤
      2 * growth.card + 3 * trace.scaledGrowthCredit growth := by
  apply trace.scaled_costs_two_thirds_of_peak_reuse reuse selected growth inside largest
  have hsize := trace.unsupported_prime_ge_eleven reuse
  have hcost := Nat.mul_le_mul_right (37 * d (trace.event peak).hit + 1131) count
  have hcredit := trace.scaled_growth_credit_ge_of_event enclosed
  omega

end ResidualPhaseTrace210

/-- A sufficient budget on an actual capped prefix at the first crossing. -/
def PotentialCrossingBudgetCondition210 (netCost : ResidualPhaseEvent210 → Int) (overhead : Nat) : Prop :=
  ∀ {M s C r C' p first : Nat} {balance : Int},
    50000000 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance →
    IsMovingHorizonStep s C r C' → 2 * (s - (M + 2)) ≤ M → M < 2 * (r - (M + 2)) →
    r - s ≤ Nat.sqrt (4 * (3 * M + 4)) → IsAttainedPreviousMaximum M r →
    ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
      (∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2)) →
      (∑ i, netCost (trace.event i)) + (24 * (r - s) + overhead : Nat) ≤ (M : Int)

/-- The crossing overhead is the starting potential cap plus 55 for
the maximum extra horizon growth beyond the previous record. -/
theorem twin_travel_of_potential_crossing_budget_condition210 {potential : Nat → Nat → Nat} {cap : Nat}
    (potentialBound : ∀ s C, C % 2 = 0 → potential s C ≤ cap)
    (supported : IsTravelPotential210 potential)
    (bound : PotentialCrossingBudgetCondition210 (fun event => event.potentialNetCost potential) (cap + 55)) :
    TwinPrimeTravelBoundFrom 50000000 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_contra hnot
  obtain ⟨s, C, r, C', q, first, balance, hledger, hstep, hr, _, hshort, hcross, hgap, _⟩ :=
    canonical_first_crossing_requires_residual_phase_balances210
      residualHorizonPhase210 hcanon hpath (Nat.lt_of_not_ge hnot)
  obtain ⟨trace, hdelta⟩ := residual_phase_trace_with_delta210 hledger
  have hprefix := residual_phase_balances210_path hledger
  have hstart := moving_horizon_path_index_le hprefix
  have hsr := hstep.2.1
  have hrMax : IsAttainedPreviousMaximum M r :=
    ⟨fun j hj hjr => hmax.1 j hj (hjr.trans hr), ⟨M + 2, by omega, by omega, hcanon⟩⟩
  have hnet := bound hM htwin hcanon hledger hstep hshort hcross hgap hrMax trace hdelta
  change (∑ i, (trace.event i).potentialNetCost potential) +
    ((24 * (r - s) + (cap + 55) : Nat) : Int) ≤ (M : Int) at hnet
  have htravel := trace.potential_travel_budget supported hprefix hdelta
  have hV := potentialBound (M + 2) (2 * M - 2) (by omega)
  have hC := canonical_horizon_bound_of_short_travel hprefix hshort
  have hstate := moving_horizon_path_endpoint hprefix
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hModd : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
  omega

abbrev ScaledCrossingBudgetCondition210 : Prop :=
  PotentialCrossingBudgetCondition210 ResidualPhaseEvent210.scaledNetCost 1175

theorem twin_travel_of_scaled_crossing_budget_condition210 (bound : ScaledCrossingBudgetCondition210) :
    TwinPrimeTravelBoundFrom 50000000 :=
  twin_travel_of_potential_crossing_budget_condition210 scaled_potential210_le
    moving_horizon_supported210_scaled_potential bound

theorem target_of_scaled_crossing_budget_condition210 (bound : ScaledCrossingBudgetCondition210) : Target :=
  target_of_twin_travel_from_fifty_million (twin_travel_of_scaled_crossing_budget_condition210 bound)

theorem unbounded_twin_primes_of_scaled_crossing_budget_condition210
    (bound : ScaledCrossingBudgetCondition210) (N : Nat) :
    ∃ R : Nat, N < R ∧ IsGreaterTwinPrime R :=
  unbounded_greater_twin_primes_of_target (target_of_scaled_crossing_budget_condition210 bound) N

end A166944Research
