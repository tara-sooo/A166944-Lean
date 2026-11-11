import A166944.ResidualRebalancedPairCaps210

/-! # Small overlapping pairs in a rebalanced growth deficit -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

/-- For one phase key the last full period of each request lies inside
its own window, and these terminal periods are pairwise disjoint. -/
theorem same_key_rebalanced_requests_pay210 {a b : Nat} (selected : Finset (Fin n))
    (key : Nat × Fin 420)
    (inside : ∀ i ∈ selected, i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (positive : ∀ i ∈ selected, 0 < trace.costDemand trace.rebalancedCosts i)
    (sameKey : ∀ i ∈ selected, (trace.event i).phaseKey = key) :
    3 * (∑ i ∈ selected, trace.costDemand trace.rebalancedCosts i) ≤ 2 * (b - a) := by
  let period := Nat.lcm 210 (2 * key.1)
  let terminal (i : Fin n) := Ico ((trace.event i).horizon - period) (trace.event i).horizon
  have incr {i : Fin n} (hi : i ∈ selected) : d (trace.event i).hit = key.1 :=
    congrArg Prod.fst (sameKey i hi)
  have width {i : Fin n} (hi : i ∈ selected) :
      period ≤ (trace.event i).horizon - (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon := by
    have h := (trace.rebalanced_request_period210 (positive i hi)).2
    rwa [incr hi] at h
  have disjoint {i j : Fin n} (hi : i ∈ selected) (hj : j ∈ selected) (order : i < j) :
      Disjoint (terminal i) (terminal j) := by
    let interval := trace.samePhaseInterval order ((sameKey i hi).trans (sameKey j hj).symm)
    have h := (same_phase_credit_interval_constraints210 interval).2.2.1
    change Nat.lcm 210 (2 * d (trace.event i).hit) ≤ (trace.event j).horizon - (trace.event i).horizon at h
    rw [incr hi] at h
    have hlt := trace.horizon_strict_mono order
    change period ≤ _ at h
    change (trace.event i).horizon < (trace.event j).horizon at hlt
    rw [Finset.disjoint_left]
    intro x hx hy
    have hxi := (mem_Ico.mp hx).2
    have hyj := (mem_Ico.mp hy).1
    omega
  have hdisjoint : (selected : Set (Fin n)).PairwiseDisjoint terminal := by
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact disjoint hi hj hij
    · exact (disjoint hj hi hji).symm
  have hsub : selected.biUnion terminal ⊆ Ico a b := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    have ho := (trace.cost_demand_anchor (positive i hi)).1
    apply trace.growth_window_inside_of_request ho (inside i hi)
    have hw := width hi
    have ⟨hl, hr⟩ := mem_Ico.mp hxi
    exact mem_Ico.mpr ⟨by omega, hr⟩
  calc
    _ ≤ 2 * (selected.biUnion terminal).card := by
      rw [card_biUnion hdisjoint, Finset.mul_sum, Finset.mul_sum]
      apply sum_le_sum
      intro i hi
      have h := trace.rebalanced_request_pays_period210 (positive i hi)
      rw [incr hi] at h
      have hw := width hi
      have hcard : (terminal i).card = period := by
        change (Ico ((trace.event i).horizon - period) (trace.event i).horizon).card = period
        rw [Nat.card_Ico]
        omega
      rw [hcard]
      exact h
    _ ≤ _ := Nat.mul_le_mul_left _ (by simpa only [Nat.card_Ico] using card_le_card hsub)

private theorem rebalanced_demand_cost_positive {i : Fin n} (hi : 0 < trace.costDemand trace.rebalancedCosts i) :
    0 < (trace.event i).rebalancedCost := by
  have h := trace.cost_demand_eq_cost hi
  change _ = (trace.event i).rebalancedCost.toNat at h
  omega

private theorem rebalanced_request_endpoints {i : Fin n} {a b : Nat}
    (inside : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (positive : 0 < trace.costDemand trace.rebalancedCosts i) :
    a ≤ (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon ∧ (trace.event i).horizon ≤ b := by
  have ⟨hl, hr⟩ := (mem_filter.mp inside).2
  rw [trace.growth_request_left_of_order (trace.cost_demand_anchor positive).1] at hl
  change (trace.event i).horizon - 1 ≤ b - 1 at hr
  have hC := (trace.event i).step.1.2.2
  have hs := (trace.event i).step.1.1
  exact ⟨hl, by omega⟩

/-- The earlier request's period and the distance between the two
right endpoints must both fit in the containing window. -/
theorem rebalanced_request_width_with_later210 {i j : Fin n} {a b : Nat} (order : i < j)
    (insideI : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (insideJ : j ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (hj : 0 < trace.costDemand trace.rebalancedCosts j) :
    Nat.lcm 210 (2 * d (trace.event i).hit) + ((trace.event j).horizon - (trace.event i).horizon) ≤ b - a := by
  have hl := (trace.rebalanced_request_endpoints insideI hi).1
  have hr := (trace.rebalanced_request_endpoints insideJ hj).2
  have hperiod := (trace.rebalanced_request_period210 hi).2
  have hlt := trace.horizon_strict_mono order
  change (trace.event i).horizon < (trace.event j).horizon at hlt
  have ha := trace.horizon_strict_mono (trace.cost_demand_anchor hi).1
  change (trace.event (trace.costAnchor trace.rebalancedCosts i)).horizon < (trace.event i).horizon at ha
  omega

theorem rebalanced_event_endpoint_growth210 {i j : Fin n} (order : i < j) :
    d (trace.event i).hit - 1 ≤ (trace.event j).horizon - (trace.event i).horizon := by
  have h := D_le_of_le (trace.ordered order)
  rw [← (trace.event i).step.2.2.2.2.2.2.1, (trace.event j).step.1.2.1] at h
  have hup := moving_horizon_step_update (trace.event i).step
  omega

private theorem rebalanced_request_period_le_window {i : Fin n} {a b : Nat}
    (inside : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (positive : 0 < trace.costDemand trace.rebalancedCosts i) :
    Nat.lcm 210 (2 * d (trace.event i).hit) ≤ b - a := by
  have h := trace.rebalanced_request_period210 positive
  have horder := (trace.cost_demand_anchor positive).1
  have hwidth := card_le_card (trace.growth_window_inside_of_request horder inside)
  simp only [growthWindow, Nat.card_Ico] at hwidth
  exact h.2.trans hwidth

private theorem rebalanced_demand_linear_cap {i : Fin n} (hi : 0 < trace.costDemand trace.rebalancedCosts i) :
    trace.costDemand trace.rebalancedCosts i ≤ 37 * d (trace.event i).hit + 1047 := by
  have h := trace.cost_demand_eq_cost hi
  change _ = (trace.event i).rebalancedCost.toNat at h
  have hraw := (trace.event i).rebalanced_cost_le_net
  have hbound := (trace.event i).rebalanced_net_cost_positive_part_le
  omega

theorem rebalanced_demand_nonlong_bounds {i : Fin n}
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (short : ¬ trace.ReusedLong i) :
    d (trace.event i).hit ≤ 159 ∧ trace.costDemand trace.rebalancedCosts i ≤ 1166 := by
  let event := trace.event i
  have hp := trace.rebalanced_demand_cost_positive hi
  have ⟨hsize, hbound⟩ := adjusted_phase_cost_weight_of_bound210 event (by decide : 1036 ≤ 1120)
    short hp (event.rebalanced_cost_le_of_positive hp)
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have hc := nonlong_rebalanced_pair_cap210 ⟨d event.hit, by omega⟩ event.step.2.2.2.1
    (d_mod_two_eq_one_of_three_le hr) (event.rebalanced_cost_positive_unsupported hp)
  exact ⟨hsize, (trace.cost_demand_eq_cost hi).trans_le (hbound.trans hc)⟩

private theorem rebalanced_long_pair_increment_bound {a b : Nat} {i j : Fin n}
    (insideI : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (insideJ : j ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (hj : 0 < trace.costDemand trace.rebalancedCosts j)
    (deficit : 2 * (b - a) < 3 * (trace.costDemand trace.rebalancedCosts i + trace.costDemand trace.rebalancedCosts j))
    (longJ : trace.ReusedLong j) : d (trace.event j).hit ≤ 31 := by
  have period {k : Fin n} (inside : k ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
      (hk : 0 < trace.costDemand trace.rebalancedCosts k) (long : trace.ReusedLong k) :
      210 * d (trace.event k).hit ≤ b - a := by
    have ⟨horder, hkey⟩ := trace.cost_demand_anchor hk
    have reuse : trace.PrimeReuse (trace.costAnchor trace.rebalancedCosts k) k :=
      ⟨horder, hkey, long.1.2, (trace.event k).rebalanced_cost_positive_unsupported
        (trace.rebalanced_demand_cost_positive hk)⟩
    have hwidth := card_le_card (trace.growth_window_inside_of_request horder inside)
    simp only [growthWindow, Nat.card_Ico] at hwidth
    exact (trace.prime_reuse_drift reuse).2.trans hwidth
  have hcostI := trace.rebalanced_demand_linear_cap hi
  have hcostJ := trace.rebalanced_demand_linear_cap hj
  have hperiodJ := period insideJ hj longJ
  by_contra hlarge
  by_cases order : d (trace.event i).hit ≤ d (trace.event j).hit
  · omega
  by_cases longI : trace.ReusedLong i
  · have hperiodI := period insideI hi longI
    omega
  · have hshort := (trace.rebalanced_demand_nonlong_bounds hi longI).2
    omega

/-- If two requests exceed the credit of their containing window,
both increments and the maximum required credit are finite. -/
theorem two_rebalanced_request_deficit_bounds210 {a b : Nat} {i j : Fin n}
    (insideI : i ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (insideJ : j ∈ trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b)
    (hi : 0 < trace.costDemand trace.rebalancedCosts i) (hj : 0 < trace.costDemand trace.rebalancedCosts j)
    (ordered : d (trace.event i).hit ≤ d (trace.event j).hit)
    (deficit : trace.growthWindowCredit trace.rebalancedCosts a b <
      3 * (trace.costDemand trace.rebalancedCosts i + trace.costDemand trace.rebalancedCosts j)) :
    (d (trace.event i).hit, d (trace.event j).hit) ∈ rebalancedDeficitPairs210 ∧ b - a ≤ 5093 ∧
      (∑ k ∈ trace.eventsInGrowthBlock a b, (-trace.rebalancedCosts k).toNat) ≤ 1363 := by
  let e := d (trace.event i).hit
  let f := d (trace.event j).hit
  let demand := trace.costDemand trace.rebalancedCosts
  let credit := ∑ k ∈ trace.eventsInGrowthBlock a b, (-trace.rebalancedCosts k).toNat
  change 2 * (b - a) + 3 * credit < 3 * (demand i + demand j) at deficit
  change 0 < demand i at hi
  change 0 < demand j at hj
  have hlongI := trace.rebalanced_long_pair_increment_bound insideJ insideI hj hi (by
    change 2 * (b - a) < 3 * (demand j + demand i)
    omega)
  have hlongJ := trace.rebalanced_long_pair_increment_bound insideI insideJ hi hj (by
    change 2 * (b - a) < 3 * (demand i + demand j)
    omega)
  have hsize {k : Fin n} (hk : 0 < demand k) (bound : trace.ReusedLong k → d (trace.event k).hit ≤ 31) :
      d (trace.event k).hit < 160 := by
    by_cases hl : trace.ReusedLong k
    · have := bound hl
      omega
    · have := (trace.rebalanced_demand_nonlong_bounds hk hl).1
      omega
  have hperiod : max (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f)) ≤ b - a :=
    max_le (trace.rebalanced_request_period_le_window insideI hi)
      (trace.rebalanced_request_period_le_window insideJ hj)
  have hcost {k : Fin n} (hk : 0 < demand k) (bound : trace.ReusedLong k → d (trace.event k).hit ≤ 31) :
      demand k ≤ rebalancedCoarsePairCap210 (d (trace.event k).hit) := by
    have h := (trace.event k).rebalanced_cost_le_coarse_pair_cap210 (trace.rebalanced_demand_cost_positive hk) bound
    have heq := trace.cost_demand_eq_cost hk
    exact heq.trans_le h
  have hadmissible {k : Fin n} (hk : 0 < demand k) :
      1 < d (trace.event k).hit ∧ d (trace.event k).hit % 2 = 1 ∧ ¬ d (trace.event k).hit ∣ 210 := by
    have hr : 3 ≤ (trace.event k).hit := by
      have := (trace.event k).step.1.1
      have := (trace.event k).step.2.1
      omega
    exact ⟨(trace.event k).step.2.2.2.1, d_mod_two_eq_one_of_three_le hr,
      (trace.event k).rebalanced_cost_positive_unsupported (trace.rebalanced_demand_cost_positive hk)⟩
  have h₁ : demand i ≤ rebalancedCoarsePairCap210 e := hcost hi hlongI
  have h₂ : demand j ≤ rebalancedCoarsePairCap210 f := hcost hj hlongJ
  have coarse : (e, f) ∈ rebalancedCoarseDeficitPairs210 :=
    mem_rebalanced_coarse_deficit_pairs210 ⟨hsize hi hlongI, hadmissible hi⟩ ⟨hsize hj hlongJ, hadmissible hj⟩ ordered
      (by omega) (by omega) (by omega)
  obtain ⟨he, hf⟩ := rebalanced_coarse_pair_increments210 coarse
  have hc₁ := (trace.cost_demand_eq_cost hi).trans_le
    ((trace.event i).rebalanced_cost_le_pair_cap210 (trace.rebalanced_demand_cost_positive hi) he)
  have hc₂ := (trace.cost_demand_eq_cost hj).trans_le
    ((trace.event j).rebalanced_cost_le_pair_cap210 (trace.rebalanced_demand_cost_positive hj) hf)
  change demand i ≤ rebalancedPairCostCap210 e at hc₁
  change demand j ≤ rebalancedPairCostCap210 f at hc₂
  have member : (e, f) ∈ rebalancedDeficitPairs210 :=
    mem_rebalanced_deficit_pairs210 he hf ordered (by omega) (by omega) (by omega)
  have caps := rebalanced_pair_width_and_credit_caps210 ⟨_, member⟩
  change 3 * (rebalancedPairCostCap210 e + rebalancedPairCostCap210 f) ≤ 10188 ∧
    3 * (rebalancedPairCostCap210 e + rebalancedPairCostCap210 f) ≤
      2 * max (Nat.lcm 210 (2 * e)) (Nat.lcm 210 (2 * f)) + 4092 at caps
  change (e, f) ∈ rebalancedDeficitPairs210 ∧ b - a ≤ 5093 ∧ credit ≤ 1363
  exact ⟨member, by omega, by omega⟩

theorem classify_two_rebalanced_growth_requests210 {a b : Nat}
    (deficit : trace.GrowthDeficit (trace.costAnchor trace.rebalancedCosts) (trace.costDemand trace.rebalancedCosts)
      trace.rebalancedCosts a b)
    (count : ((trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b).filter
      (fun i => 0 < trace.costDemand trace.rebalancedCosts i)).card = 2) :
    ∃ i j : Fin n,
      (trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b).filter
        (fun k => 0 < trace.costDemand trace.rebalancedCosts k) = {i, j} ∧
      i ≠ j ∧ (trace.event i).phaseKey ≠ (trace.event j).phaseKey ∧
      (d (trace.event i).hit, d (trace.event j).hit) ∈ rebalancedDeficitPairs210 ∧ b - a ≤ 5093 ∧
      (∑ k ∈ trace.eventsInGrowthBlock a b, (-trace.rebalancedCosts k).toNat) ≤ 1363 := by
  let demand := trace.costDemand trace.rebalancedCosts
  let requests := trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b
  obtain ⟨i, j, hne, hpair⟩ := card_eq_two.mp count
  change requests.filter (fun k => 0 < demand k) = {i, j} at hpair
  have hi : i ∈ requests.filter (fun k => 0 < demand k) := by rw [hpair]; simp
  have hj : j ∈ requests.filter (fun k => 0 < demand k) := by rw [hpair]; simp
  have hsum : (∑ k ∈ requests, demand k) = demand i + demand j := by
    rw [sum_positive_requests, hpair, sum_pair hne]
  have hbad : trace.growthWindowCredit trace.rebalancedCosts a b < 3 * (demand i + demand j) := by
    rw [← hsum]
    exact deficit
  obtain ⟨hinI, hip⟩ := mem_filter.mp hi
  obtain ⟨hinJ, hjp⟩ := mem_filter.mp hj
  have hkey : (trace.event i).phaseKey ≠ (trace.event j).phaseKey := by
    intro h
    have hpaid := trace.same_key_rebalanced_requests_pay210 {i, j} (trace.event j).phaseKey
      (fun k hk => by simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl <;> assumption)
      (fun k hk => by simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl <;> assumption)
      (fun k hk => by simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl <;> first | exact h | rfl)
    rw [sum_pair hne] at hpaid
    change 3 * (demand i + demand j) ≤ 2 * (b - a) at hpaid
    unfold growthWindowCredit at hbad
    omega
  rcases le_total (d (trace.event i).hit) (d (trace.event j).hit) with h | h
  · exact ⟨i, j, hpair, hne, hkey, trace.two_rebalanced_request_deficit_bounds210 hinI hinJ hip hjp h hbad⟩
  · rw [Nat.add_comm (demand i)] at hbad
    rw [pair_comm] at hpair
    exact ⟨j, i, hpair, hne.symm, hkey.symm, trace.two_rebalanced_request_deficit_bounds210 hinJ hinI hjp hip h hbad⟩

theorem rebalanced_two_request_deficit_excludes_large_composite210 {a b : Nat}
    (deficit : trace.GrowthDeficit (trace.costAnchor trace.rebalancedCosts) (trace.costDemand trace.rebalancedCosts)
      trace.rebalancedCosts a b)
    (count : ((trace.growthRequests (trace.costAnchor trace.rebalancedCosts) a b).filter
      (fun i => 0 < trace.costDemand trace.rebalancedCosts i)).card = 2)
    {k : Fin n} (enclosed : k ∈ trace.eventsInGrowthBlock a b)
    (composite : ¬ NoProperFactor (d (trace.event k).hit)) :
    d (trace.event k).hit < 295 := by
  obtain ⟨_, _, _, _, _, _, _, credit⟩ := trace.classify_two_rebalanced_growth_requests210 deficit count
  by_contra hlarge
  let event := trace.event k
  change ¬ d event.hit < 295 at hlarge
  have hu : ¬ d event.hit ∣ 210 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 210) h
    omega
  obtain ⟨f, hf, hfd, hsquare⟩ := exists_small_factor_of_composite composite
  have hgap := moving_horizon_step_gap_le_twice_increment_factor event.step hf hfd
  have hcost := event.rebalanced_net_cost_le_of_unsupported hu
  have hle := event.rebalanced_cost_le_net
  have hnegative : event.rebalancedCost ≤ -1364 := by
    by_cases hsmall : f ≤ 17
    · omega
    · have hf18 : 18 ≤ f := by omega
      have hmul := Nat.mul_le_mul_right f hf18
      change f * f ≤ d event.hit at hsquare
      omega
  have hcredit : (-trace.rebalancedCosts k).toNat ≤
      ∑ i ∈ trace.eventsInGrowthBlock a b, (-trace.rebalancedCosts i).toNat :=
    single_le_sum (f := fun i => (-trace.rebalancedCosts i).toNat) (fun _ _ => Nat.zero_le _) enclosed
  change (-event.rebalancedCost).toNat ≤ _ at hcredit
  omega

end

end A166944Research.ResidualPhaseTrace210
