import A166944.ResidualRebalancedTwoRequests210

/-! # The short mixed pair at increments 9 and 63 -/

open Finset

namespace A166944Research

private def checkClippedCostRows210 (e cap : Nat) (rows : List Nat) : Bool :=
  rows.all fun c => (List.range 210).all fun s =>
    match firstClippedHit210 s c with
    | some (gap, clip) =>
      if clip = Nat.gcd e 210 then
        decide (24 * gap + rebalancedPotential210 (s + gap) (c + e - 1) ≤
          11 * (e - 1) + rebalancedPotential210 s c + cap)
      else true
    | none => true

private theorem clipped_cost_le_checked_rows210 (event : ResidualPhaseEvent210) {e cap : Nat} {rows : List Nat}
    (increment : d event.hit = e) (hclip : 1 < Nat.gcd e 210)
    (checked : checkClippedCostRows210 e cap rows = true) (hC : event.horizon % 210 ∈ rows)
    (positive : 0 < event.rebalancedCost) : event.rebalancedCost.toNat ≤ cap := by
  have hhit := first_clipped_hit210_of_nonunit event.step (show 1 < Nat.gcd (d event.hit) 210 by rwa [increment])
  rw [increment] at hhit
  have hrow := List.all_eq_true.mp checked _ hC
  have hcell := List.all_eq_true.mp hrow (event.start % 210) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [hhit] at hcell
  have h := of_decide_eq_true hcell
  have horder := event.step.2.1
  have hupdate := moving_horizon_step_update event.step
  have hs : (event.start % 210 + (event.hit - event.start)) % 210 = event.hit % 210 := by omega
  have hc : (event.horizon % 210 + e - 1) % 210 = event.nextHorizon % 210 := by
    have := event.step.2.2.2.1
    omega
  unfold rebalancedPotential210 at h
  rw [hs, hc] at h
  simp only [Nat.mod_mod] at h
  change 24 * (event.hit - event.start) + rebalancedPotential210 event.hit event.nextHorizon ≤
    11 * (e - 1) + rebalancedPotential210 event.start event.horizon + cap at h
  have hu := event.rebalanced_cost_positive_unsupported positive
  have hnet := event.rebalanced_cost_le_net
  change event.rebalancedCost ≤ event.potentialNetCost rebalancedPotential210 at hnet
  rw [ResidualPhaseEvent210.potentialNetCost, if_neg hu] at hnet
  omega

private def otherSixtyThreeHorizons210 : List Nat := [20, 62, 64, 104, 106, 146, 148, 188, 190]

private def precedingNineHorizons210 : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 198, 200, 202, 204, 206, 208]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem sixty_three_other_horizons_checked210 : checkClippedCostRows210 63 0 otherSixtyThreeHorizons210 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem preceding_nine_horizons_checked210 : checkClippedCostRows210 9 266 precedingNineHorizons210 = true := by
  decide +kernel

private theorem sixty_three_horizon_cases210 : ∀ c : Fin 210,
    (c.val % 42 = 20 ∨ c.val % 42 = 22) → c.val ≠ 22 → c.val ∈ otherSixtyThreeHorizons210 := by
  decide +kernel

private theorem preceding_nine_horizon_cases210 : ∀ offset : Fin 35,
    8 ≤ offset.val → offset.val % 2 = 0 → (232 - offset.val) % 210 ∈ precedingNineHorizons210 := by
  decide +kernel

private theorem sixty_three_positive_horizon210 (event : ResidualPhaseEvent210) (increment : d event.hit = 63)
    (positive : 0 < event.rebalancedCost) : event.horizon % 210 = 22 := by
  have hdiv : 21 ∣ d event.hit := by rw [increment]; decide
  have hcase : event.horizon % 42 = 20 ∨ event.horizon % 42 = 22 := by
    rcases moving_horizon_factor_event_residues event.step (by decide : 2 < 21) hdiv with h | h
    · exact Or.inr h.2.2
    · exact Or.inl h.2.2
  have hmod := Nat.mod_mod_of_dvd event.horizon (by decide : 42 ∣ 210)
  by_contra hnot
  have hrow := sixty_three_horizon_cases210 ⟨event.horizon % 210, Nat.mod_lt _ (by decide)⟩
    (by simpa only [hmod] using hcase) hnot
  have hcap := clipped_cost_le_checked_rows210 event increment (by decide) sixty_three_other_horizons_checked210 hrow positive
  omega

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- The only positive horizon residue at increment 63 precludes a
nearby preceding increment 9 from reaching its global cost cap. -/
theorem two_rebalanced_nine_sixty_three_requests_pay210 {i j : Fin n} {a b : Nat}
    (insideI : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (insideJ : j ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (hj : 0 < trace.costDemand trace.rebalancedCosts j)
    (incrementI : d (trace.event i).hit = 9) (incrementJ : d (trace.event j).hit = 63) :
    3 * (trace.costDemand trace.rebalancedCosts i + trace.costDemand trace.rebalancedCosts j) ≤ 2 * (b - a) := by
  let demand := trace.costDemand trace.rebalancedCosts
  let nine := trace.event i
  let sixtyThree := trace.event j
  change d nine.hit = 9 at incrementI
  change d sixtyThree.hit = 63 at incrementJ
  change 3 * (demand i + demand j) ≤ _
  have hn : demand i = nine.rebalancedCost.toNat := trace.cost_demand_eq_cost hi
  have hs : demand j = sixtyThree.rebalancedCost.toNat := trace.cost_demand_eq_cost hj
  change 0 < demand i at hi
  change 0 < demand j at hj
  have hposI : 0 < nine.rebalancedCost := by omega
  have hposJ : 0 < sixtyThree.rebalancedCost := by omega
  have hcI : demand i ≤ 315 := by
    have h := nine.rebalanced_cost_le_pair_cap210 hposI (by rw [incrementI]; decide)
    rw [incrementI, show rebalancedPairCostCap210 9 = 315 by decide] at h
    exact hn.trans_le h
  have hcJ : demand j ≤ 128 := by
    have h := sixtyThree.rebalanced_cost_le_pair_cap210 hposJ (by rw [incrementJ]; decide)
    rw [incrementJ, show rebalancedPairCostCap210 63 = 128 by decide] at h
    exact hs.trans_le h
  have hne : i ≠ j := by
    intro h
    subst j
    have : d (trace.event i).hit = 63 := incrementJ
    have : d (trace.event i).hit = 9 := incrementI
    omega
  rcases lt_or_gt_of_ne hne with order | order
  · let offset := sixtyThree.horizon - nine.horizon
    have hwidth := trace.rebalanced_request_width_with_later210 order insideI insideJ hi hj
    change Nat.lcm 210 (2 * d nine.hit) + offset ≤ b - a at hwidth
    rw [incrementI, show Nat.lcm 210 (2 * 9) = 630 by decide] at hwidth
    have hgrowth := trace.rebalanced_event_endpoint_growth210 order
    change d nine.hit - 1 ≤ offset at hgrowth
    rw [incrementI] at hgrowth
    by_contra hdef
    have hoffset : offset < 35 := by omega
    have hC := sixty_three_positive_horizon210 sixtyThree incrementJ hposJ
    have hevenI := nine.step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le nine.step.1.1
    have hevenJ := sixtyThree.step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le sixtyThree.step.1.1
    have horder := trace.horizon_strict_mono order
    change nine.horizon < sixtyThree.horizon at horder
    have hmod : nine.horizon % 210 = (232 - offset) % 210 := by
      dsimp only [offset] at *
      omega
    have hpar : offset % 2 = 0 := by unfold offset; omega
    have hrow := preceding_nine_horizon_cases210 ⟨offset, hoffset⟩ (by exact hgrowth) hpar
    change (232 - offset) % 210 ∈ precedingNineHorizons210 at hrow
    rw [← hmod] at hrow
    have hcap : demand i ≤ 266 := hn.trans_le
      (clipped_cost_le_checked_rows210 nine incrementI (by decide) preceding_nine_horizons_checked210 hrow hposI)
    omega
  · have hwidth := trace.rebalanced_request_width_with_later210 order insideJ insideI hj hi
    have hgrowth := trace.rebalanced_event_endpoint_growth210 order
    change Nat.lcm 210 (2 * d sixtyThree.hit) + (nine.horizon - sixtyThree.horizon) ≤ b - a at hwidth
    change d sixtyThree.hit - 1 ≤ nine.horizon - sixtyThree.horizon at hgrowth
    rw [incrementJ, show Nat.lcm 210 (2 * 63) = 630 by decide] at hwidth
    rw [incrementJ] at hgrowth
    omega

end ResidualPhaseTrace210

end A166944Research
