import A166944.ResidualRebalancedMixedOffsets210

/-! # Horizon offsets can exclude pairs that pass separate cost caps -/

open Finset

namespace A166944Research

private def twentyThreeCostCap210 : Nat → Nat
  | 0 => 1218
  | 12 => 1449
  | 18 => 1251
  | 30 => 1554
  | 42 => 1665
  | 60 => 1650
  | 72 => 1206
  | 102 => 1452
  | 108 => 1230
  | 138 => 1230
  | 150 => 1206
  | 168 => 984
  | 180 => 1206
  | 192 => 1206
  | 198 => 984
  | _ => 1665

private def checkTwentyThreeCostCaps210 : Bool :=
  longGapHorizons210.all fun c => (List.range 210).all fun r =>
    decide (862 + rebalancedPotential210 r (c + 22) ≤ twentyThreeCostCap210 c)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem twenty_three_cost_caps_checked210 : checkTwentyThreeCostCaps210 = true := by
  decide +kernel

private def twentyThreeEndpointOffset210 (c d : Nat) : Nat := 22 + (d + 398 - c) % 210

private theorem twenty_three_offset_caps_checked210 :
    (longGapHorizons210.all fun c => longGapHorizons210.all fun d =>
      decide (3 * (twentyThreeCostCap210 c + twentyThreeCostCap210 d) ≤
        2 * (4830 + twentyThreeEndpointOffset210 c d))) = true := by
  decide +kernel

private theorem twenty_three_long_cost_le_horizon_cap210 (event : ResidualPhaseEvent210)
    (increment : d event.hit = 23) (long : 14 < event.hit - event.start)
    (positive : 0 < event.rebalancedCost) :
    event.rebalancedCost.toNat ≤ twentyThreeCostCap210 (event.horizon % 210) := by
  have hC := moving_horizon_long_gap_residue210 event.step long
  have hrow := List.all_eq_true.mp twenty_three_cost_caps_checked210 _ hC
  have hr := List.all_eq_true.mp hrow (event.hit % 210) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hV := of_decide_eq_true hr
  change 862 + rebalancedPotential210 (event.hit % 210) (event.horizon % 210 + 22) ≤ _ at hV
  have hupdate := moving_horizon_step_update event.step
  have hmod : (event.horizon % 210 + 22) % 210 = event.nextHorizon % 210 := by omega
  unfold rebalancedPotential210 at hV
  rw [Nat.mod_mod, hmod] at hV
  change 862 + rebalancedPotential210 event.hit event.nextHorizon ≤ _ at hV
  have hgap := moving_horizon_step_gap_le_twice_increment event.step
  have hu := event.rebalanced_cost_positive_unsupported positive
  have hc := event.rebalanced_cost_le_net
  change event.rebalancedCost ≤ event.potentialNetCost rebalancedPotential210 at hc
  rw [ResidualPhaseEvent210.potentialNetCost, if_neg hu] at hc
  omega

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- Costs near the individual caps at increment 23 require horizon
residues whose separation makes the combined window wide enough. -/
theorem two_rebalanced_twenty_three_requests_pay210 {i j : Fin n} {a b : Nat} (order : i < j)
    (insideI : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (insideJ : j ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (hj : 0 < trace.costDemand trace.rebalancedCosts j)
    (incrementI : d (trace.event i).hit = 23) (incrementJ : d (trace.event j).hit = 23) :
    3 * (trace.costDemand trace.rebalancedCosts i + trace.costDemand trace.rebalancedCosts j) ≤ 2 * (b - a) := by
  let demand := trace.costDemand trace.rebalancedCosts
  let firstEvent := trace.event i
  let lastEvent := trace.event j
  change d firstEvent.hit = 23 at incrementI
  change d lastEvent.hit = 23 at incrementJ
  change 3 * (demand i + demand j) ≤ _
  have hwidth := trace.rebalanced_request_width_with_later210 order insideI insideJ hi hj
  have hoffset := trace.rebalanced_event_endpoint_growth210 order
  change Nat.lcm 210 (2 * d firstEvent.hit) + (lastEvent.horizon - firstEvent.horizon) ≤ b - a at hwidth
  change d firstEvent.hit - 1 ≤ lastEvent.horizon - firstEvent.horizon at hoffset
  rw [incrementI, show Nat.lcm 210 (2 * 23) = 4830 by decide] at hwidth
  rw [incrementI] at hoffset
  have costFacts {k : Fin n} (hk : 0 < demand k) :
      demand k = (trace.event k).rebalancedCost.toNat ∧ 0 < (trace.event k).rebalancedCost := by
    have h := trace.cost_demand_eq_cost hk
    change demand k = (trace.event k).rebalancedCost.toNat at h
    exact ⟨h, by omega⟩
  have hi' : demand i = firstEvent.rebalancedCost.toNat ∧ 0 < firstEvent.rebalancedCost := costFacts hi
  have hj' : demand j = lastEvent.rebalancedCost.toNat ∧ 0 < lastEvent.rebalancedCost := costFacts hj
  have globalCap (event : ResidualPhaseEvent210) (he : d event.hit = 23) (hp : 0 < event.rebalancedCost) :
      event.rebalancedCost.toNat ≤ 1665 := by
    have h := event.rebalanced_cost_le_pair_cap210 hp (by rw [he]; decide)
    rw [he, show rebalancedPairCostCap210 23 = 1665 by decide] at h
    exact h
  have shortCap (event : ResidualPhaseEvent210) (he : d event.hit = 23) (hp : 0 < event.rebalancedCost)
      (short : event.hit - event.start ≤ 14) : event.rebalancedCost.toNat ≤ 1130 := by
    have h := event.rebalanced_net_cost_le_of_unsupported (event.rebalanced_cost_positive_unsupported hp)
    have hle := event.rebalanced_cost_le_net
    omega
  by_cases longI : 14 < firstEvent.hit - firstEvent.start
  · by_cases longJ : 14 < lastEvent.hit - lastEvent.start
    · let c := firstEvent.horizon % 210
      let d := lastEvent.horizon % 210
      let offset := lastEvent.horizon - firstEvent.horizon
      have hc : c ∈ longGapHorizons210 := moving_horizon_long_gap_residue210 firstEvent.step longI
      have hd : d ∈ longGapHorizons210 := moving_horizon_long_gap_residue210 lastEvent.step longJ
      have htable := of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp twenty_three_offset_caps_checked210 c hc) d hd)
      change 3 * (twentyThreeCostCap210 c + twentyThreeCostCap210 d) ≤
        2 * (4830 + twentyThreeEndpointOffset210 c d) at htable
      have ho : 22 ≤ offset := hoffset
      have hmod : (offset - 22) % 210 = (d + 398 - c) % 210 := by
        dsimp only [offset, c, d] at ho ⊢
        omega
      have hmin : twentyThreeEndpointOffset210 c d ≤ offset := by
        unfold twentyThreeEndpointOffset210
        rw [← hmod]
        have := Nat.mod_le (offset - 22) 210
        omega
      have hcostI : demand i ≤ twentyThreeCostCap210 c :=
        hi'.1.trans_le (twenty_three_long_cost_le_horizon_cap210 firstEvent incrementI longI hi'.2)
      have hcostJ : demand j ≤ twentyThreeCostCap210 d :=
        hj'.1.trans_le (twenty_three_long_cost_le_horizon_cap210 lastEvent incrementJ longJ hj'.2)
      change 4830 + offset ≤ _ at hwidth
      omega
    · have hcostI := hi'.1.trans_le (globalCap firstEvent incrementI hi'.2)
      have hcostJ := hj'.1.trans_le (shortCap lastEvent incrementJ hj'.2 (by omega))
      omega
  · have hcostI := hi'.1.trans_le (shortCap firstEvent incrementI hi'.2 (by omega))
    have hcostJ := hj'.1.trans_le (globalCap lastEvent incrementJ hj'.2)
    omega

end ResidualPhaseTrace210

def rebalancedOffsetDeficitPairs210 : Finset (Nat × Nat) :=
  (rebalancedDeficitPairs210.erase (23, 23)).erase (9, 63)

theorem rebalanced_offset_deficit_pair_count210 : rebalancedOffsetDeficitPairs210.card = 33 := by
  decide +kernel

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

theorem classify_two_rebalanced_growth_requests_with_offsets210 {a b : Nat}
    (deficit : trace.GrowthDeficit (trace.costAnchor trace.rebalancedCosts) (trace.costDemand trace.rebalancedCosts)
      trace.rebalancedCosts a b)
    (count : ((trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b).filter
      (fun i => 0 < trace.costDemand trace.rebalancedCosts i)).card = 2) :
    ∃ i j : Fin n, i ≠ j ∧ (trace.event i).phaseKey ≠ (trace.event j).phaseKey ∧
      (d (trace.event i).hit, d (trace.event j).hit) ∈ rebalancedOffsetDeficitPairs210 ∧ b - a ≤ 5093 ∧
      (∑ k ∈ trace.eventsInGrowthBlock a b, (-trace.rebalancedCosts k).toNat) ≤ 1363 := by
  classical
  obtain ⟨i, j, hpair, hne, hkey, member, width, credit⟩ :=
    trace.classify_two_rebalanced_growth_requests210 deficit count
  refine ⟨i, j, hne, hkey, ?_, width, credit⟩
  let demand := trace.costDemand trace.rebalancedCosts
  let requests := trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b
  change requests.filter (fun k => 0 < demand k) = {i, j} at hpair
  have memI : i ∈ requests.filter (fun k => 0 < demand k) := by simp [hpair]
  have memJ : j ∈ requests.filter (fun k => 0 < demand k) := by simp [hpair]
  have hsum : (∑ k ∈ requests, demand k) = demand i + demand j := by
    rw [sum_positive_requests, hpair, sum_pair hne]
  have hbad : 2 * (b - a) < 3 * (demand i + demand j) := by
    have h : trace.growthWindowCredit trace.rebalancedCosts a b < 3 * (∑ k ∈ requests, demand k) := deficit
    rw [hsum] at h
    unfold growthWindowCredit at h
    omega
  obtain ⟨hinI, hip⟩ := mem_filter.mp memI
  obtain ⟨hinJ, hjp⟩ := mem_filter.mp memJ
  refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, member⟩⟩
  · intro mixed
    have hi := congrArg Prod.fst mixed
    have hj := congrArg Prod.snd mixed
    exact Nat.not_le_of_gt hbad (trace.two_rebalanced_nine_sixty_three_requests_pay210 hinI hinJ hip hjp hi hj)
  · intro both
    have hi := congrArg Prod.fst both
    have hj := congrArg Prod.snd both
    rcases lt_or_gt_of_ne hne with order | order
    · exact Nat.not_le_of_gt hbad (trace.two_rebalanced_twenty_three_requests_pay210 order hinI hinJ hip hjp hi hj)
    · rw [Nat.add_comm] at hbad
      exact Nat.not_le_of_gt hbad (trace.two_rebalanced_twenty_three_requests_pay210 order hinJ hinI hjp hip hj hi)

end ResidualPhaseTrace210

end A166944Research
