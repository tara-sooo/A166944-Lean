import A166944.ResidualRebalancedCosts210

/-! # First-hit caps for pairs of rebalanced requests -/

open Finset

namespace A166944Research

def rebalancedCoarsePairCap210 (e : Nat) : Nat :=
  if e ∈ rebalancedExceptions210 then rebalancedAllowance210 e
  else if Nat.Prime e ∧ e ≤ 31 then 37 * e + 1047
  else startupWeightAtCap210 1036 e

private def coarsePairIncrements210 : Finset Nat :=
  {9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 33, 39, 45, 49, 51, 55, 57, 63, 65, 75, 77, 85, 91}

set_option maxRecDepth 16384 in
theorem nonlong_rebalanced_pair_cap210 : ∀ e : Fin 160,
    1 < e.val → e.val % 2 = 1 → ¬ e.val ∣ 210 → startupWeightAtCap210 1036 e.val ≤ 1166 := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem rebalanced_coarse_pair_cap_le210 : ∀ e : Fin 160,
    1 < e.val → e.val % 2 = 1 → ¬ e.val ∣ 210 → rebalancedCoarsePairCap210 e.val ≤ 2194 := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem coarse_pair_increments_checked210 : ∀ e : Fin 160,
    1 < e.val → e.val % 2 = 1 → ¬ e.val ∣ 210 → 0 < rebalancedCoarsePairCap210 e.val →
    2 * Nat.lcm 210 (2 * e.val) < 3 * (rebalancedCoarsePairCap210 e.val + 2194) →
    e.val ∈ coarsePairIncrements210 := by
  decide +kernel

private def candidatePairs210 (increments : Finset Nat) (cap : Nat → Nat) : Finset (Nat × Nat) :=
  (increments ×ˢ increments).filter fun (e, f) =>
    e ≤ f ∧ 0 < cap e ∧ 0 < cap f ∧
      2 * max (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f)) < 3 * (cap e + cap f)

def rebalancedCoarseDeficitPairs210 : Finset (Nat × Nat) :=
  candidatePairs210 coarsePairIncrements210 rebalancedCoarsePairCap210

def rebalancedPairIncrements210 : Finset Nat :=
  {9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 33, 39, 45, 49, 55, 63, 65, 75, 77, 91}

theorem mem_rebalanced_coarse_deficit_pairs210 {e f : Nat}
    (he : e < 160 ∧ 1 < e ∧ e % 2 = 1 ∧ ¬ e ∣ 210)
    (hf : f < 160 ∧ 1 < f ∧ f % 2 = 1 ∧ ¬ f ∣ 210) (ordered : e ≤ f)
    (positiveE : 0 < rebalancedCoarsePairCap210 e) (positiveF : 0 < rebalancedCoarsePairCap210 f)
    (deficit : 2 * max (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f)) <
      3 * (rebalancedCoarsePairCap210 e + rebalancedCoarsePairCap210 f)) :
    (e, f) ∈ rebalancedCoarseDeficitPairs210 := by
  have hE := rebalanced_coarse_pair_cap_le210 ⟨e, he.1⟩ he.2.1 he.2.2.1 he.2.2.2
  have hF := rebalanced_coarse_pair_cap_le210 ⟨f, hf.1⟩ hf.2.1 hf.2.2.1 hf.2.2.2
  change rebalancedCoarsePairCap210 e ≤ 2194 at hE
  change rebalancedCoarsePairCap210 f ≤ 2194 at hF
  have hle := le_max_left (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f))
  have hlf := le_max_right (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f))
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨coarse_pair_increments_checked210 ⟨e, he.1⟩ he.2.1 he.2.2.1 he.2.2.2 positiveE (by simpa using
        (show 2 * Nat.lcm 210 (2 * e) < 3 * (rebalancedCoarsePairCap210 e + 2194) by omega)),
      coarse_pair_increments_checked210 ⟨f, hf.1⟩ hf.2.1 hf.2.2.1 hf.2.2.2 positiveF (by simpa using
        (show 2 * Nat.lcm 210 (2 * f) < 3 * (rebalancedCoarsePairCap210 f + 2194) by omega))⟩,
    ordered, positiveE, positiveF, deficit⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rebalanced_coarse_deficit_pair_count210 : rebalancedCoarseDeficitPairs210.card = 72 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem rebalanced_coarse_pair_increments_checked210 : ∀ pair : rebalancedCoarseDeficitPairs210,
    pair.val.1 ∈ rebalancedPairIncrements210 ∧ pair.val.2 ∈ rebalancedPairIncrements210 := by
  decide +kernel

theorem rebalanced_coarse_pair_increments210 {e f : Nat} (member : (e, f) ∈ rebalancedCoarseDeficitPairs210) :
    e ∈ rebalancedPairIncrements210 ∧ f ∈ rebalancedPairIncrements210 :=
  rebalanced_coarse_pair_increments_checked210 ⟨_, member⟩

private def rebalancedLongPotentialCap210 : Nat → Nat
  | 11 => 1034
  | 13 => 984
  | 17 => 1010
  | 19 => 984
  | 23 => 803
  | 29 => 770
  | 31 => 768
  | _ => 1036

def rebalancedPairCostCap210 (e : Nat) : Nat :=
  if e ∈ smallReusePrimes210 then 37 * e + 11 + rebalancedLongPotentialCap210 e
  else ((rebalancedClippedCostCaps210 (Nat.gcd e 210)).lookup e).getD 0

def rebalancedDeficitPairs210 : Finset (Nat × Nat) :=
  candidatePairs210 rebalancedPairIncrements210 rebalancedPairCostCap210

theorem mem_rebalanced_deficit_pairs210 {e f : Nat}
    (he : e ∈ rebalancedPairIncrements210) (hf : f ∈ rebalancedPairIncrements210) (ordered : e ≤ f)
    (positiveE : 0 < rebalancedPairCostCap210 e) (positiveF : 0 < rebalancedPairCostCap210 f)
    (deficit : 2 * max (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f)) <
      3 * (rebalancedPairCostCap210 e + rebalancedPairCostCap210 f)) :
    (e, f) ∈ rebalancedDeficitPairs210 :=
  mem_filter.mpr ⟨mem_product.mpr ⟨he, hf⟩, ordered, positiveE, positiveF, deficit⟩

set_option maxRecDepth 16384 in
theorem rebalanced_deficit_pair_count210 : rebalancedDeficitPairs210.card = 35 := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem rebalanced_pair_width_and_credit_caps210 :
    ∀ pair : rebalancedDeficitPairs210,
      3 * (rebalancedPairCostCap210 pair.val.1 + rebalancedPairCostCap210 pair.val.2) ≤ 10188 ∧
      3 * (rebalancedPairCostCap210 pair.val.1 + rebalancedPairCostCap210 pair.val.2) ≤
        2 * max (Nat.lcm 210 (2 * pair.val.1)) (Nat.lcm 210 (2 * pair.val.2)) + 4092 := by
  decide +kernel

private def checkRebalancedLongPotential210 (p : Nat) : Bool :=
  longGapHorizons210.all fun c => (List.range 210).all fun r =>
    decide (rebalancedPotential210 r (c + p - 1) ≤ rebalancedLongPotentialCap210 p)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem rebalanced_long_potentials_checked210 (p : Nat) (hp : p ∈ smallReusePrimes210) :
    checkRebalancedLongPotential210 p = true := by
  simp only [smallReusePrimes210, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rebalanced_long_potential_le210 (r C p : Nat) (hp : p ∈ smallReusePrimes210)
    (hC : C % 210 ∈ longGapHorizons210) (hsize : 1 < p) :
    rebalancedPotential210 r (C + p - 1) ≤ rebalancedLongPotentialCap210 p := by
  have h := rebalanced_long_potentials_checked210 p hp
  have hc := List.all_eq_true.mp h (C % 210) hC
  have hr := List.all_eq_true.mp hc (r % 210) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hb := of_decide_eq_true hr
  change rebalancedPotential210 (r % 210) (C % 210 + p - 1) ≤ rebalancedLongPotentialCap210 p at hb
  unfold rebalancedPotential210 at hb ⊢
  rwa [Nat.mod_mod, show (C % 210 + p - 1) % 210 = (C + p - 1) % 210 by omega] at hb

private theorem rebalanced_short_prime_gap_cap210 :
    ∀ p : smallReusePrimes210, 336 + 1036 ≤ 48 * p.val + rebalancedLongPotentialCap210 p.val := by
  decide +kernel

private theorem rebalanced_pair_cap_clipped_entry210 :
    ∀ e : rebalancedPairIncrements210, e.val ∉ smallReusePrimes210 →
      1 < Nat.gcd e.val 210 ∧
        (e.val, rebalancedPairCostCap210 e.val) ∈ rebalancedClippedCostCaps210 (Nat.gcd e.val 210) := by
  decide +kernel

namespace ResidualPhaseEvent210

theorem rebalanced_cost_le_coarse_pair_cap210 (event : ResidualPhaseEvent210) (positive : 0 < event.rebalancedCost)
    (longBound : (event.LongPrime ∧ event.phaseKey ∈ event.seen) → d event.hit ≤ 31) :
    event.rebalancedCost.toNat ≤ rebalancedCoarsePairCap210 (d event.hit) := by
  have hraw := event.rebalanced_cost_le_net
  have he := event.step.2.2.2.1
  unfold rebalancedCoarsePairCap210
  split
  · rename_i hx
    have hc := event.rebalanced_net_cost_exception_le hx
    omega
  split
  · have hc := event.rebalanced_net_cost_positive_part_le
    omega
  · rename_i hp
    have hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen) :=
      fun h => hp ⟨prime_of_no_proper_factor he h.1.2, longBound h⟩
    exact (adjusted_phase_cost_weight_of_bound210 event (by decide : 1036 ≤ 1120)
      hnew positive (event.rebalanced_cost_le_of_positive positive)).2

theorem rebalanced_cost_le_pair_cap210 (event : ResidualPhaseEvent210) (positive : 0 < event.rebalancedCost)
    (candidate : d event.hit ∈ rebalancedPairIncrements210) :
    event.rebalancedCost.toNat ≤ rebalancedPairCostCap210 (d event.hit) := by
  have hraw := event.rebalanced_cost_le_net
  have hu := event.rebalanced_cost_positive_unsupported positive
  have hsize := event.step.2.2.2.1
  by_cases hp : d event.hit ∈ smallReusePrimes210
  · rw [rebalancedPairCostCap210, if_pos hp]
    by_cases hlong : 14 < event.hit - event.start
    · have hC := moving_horizon_long_gap_residue210 event.step hlong
      have hV := rebalanced_long_potential_le210 event.hit event.horizon (d event.hit) hp hC hsize
      have hupdate := moving_horizon_step_update event.step
      have hgap := moving_horizon_step_gap_le_twice_increment event.step
      rw [show event.horizon + d event.hit - 1 = event.nextHorizon by omega] at hV
      change event.rebalancedCost ≤ event.potentialNetCost rebalancedPotential210 at hraw
      rw [potentialNetCost, if_neg hu] at hraw
      omega
    · have hc := event.rebalanced_net_cost_le_of_unsupported hu
      have hs := rebalanced_short_prime_gap_cap210 ⟨_, hp⟩
      change 336 + 1036 ≤ 48 * d event.hit + rebalancedLongPotentialCap210 (d event.hit) at hs
      omega
  · have entry : 1 < Nat.gcd (d event.hit) 210 ∧
        (d event.hit, rebalancedPairCostCap210 (d event.hit)) ∈ rebalancedClippedCostCaps210 (Nat.gcd (d event.hit) 210) :=
      rebalanced_pair_cap_clipped_entry210 ⟨_, candidate⟩ hp
    obtain ⟨hc, hm⟩ := entry
    have h := moving_horizon_rebalanced_clipped_cost_cap210 event.step hc hm
    change event.rebalancedCost ≤ event.potentialNetCost rebalancedPotential210 at hraw
    rw [potentialNetCost, if_neg hu] at hraw
    omega

end ResidualPhaseEvent210

end A166944Research
