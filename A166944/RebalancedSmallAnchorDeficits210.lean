import A166944.RebalancedAnchorWindows210
import A166944.RebalancedSmallAnchorData210

/-! # Ordered bounds for two and three anchored demands -/

open Finset

namespace A166944Research

open RebalancedSmallAnchorData210

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def rebalancedWindowGrowth (l r : Fin n) : Nat :=
  (trace.event r).nextHorizon - (trace.event l).nextHorizon

private theorem small_anchor_demand_le_cap {i : Fin n} (positive : 0 < trace.rebalancedDemand i)
    (longBound : trace.ReusedLong i → d (trace.event i).hit ≤ 107) :
    trace.rebalancedDemand i ≤ smallAnchorCap210 (d (trace.event i).hit) := by
  let event := trace.event i
  let e := d event.hit
  let coarse := if Nat.Prime e ∧ e ≤ 107 then 37 * e + 1047 else min 1166 (startupWeightAtCap210 1036 e)
  have hcost := trace.cost_demand_eq_cost positive
  change trace.rebalancedDemand i = event.rebalancedCost.toNat at hcost
  have hpos : 0 < event.rebalancedCost := by omega
  have he : 1 < e := event.step.2.2.2.1
  have hcoarse : trace.rebalancedDemand i ≤ coarse := by
    dsimp only [coarse]
    split
    · exact trace.rebalanced_demand_linear_cap positive
    · rename_i hn
      have hnot : ¬ trace.ReusedLong i :=
        fun hl => hn ⟨prime_of_no_proper_factor he hl.1.2, longBound hl⟩
      exact Nat.le_min.mpr ⟨(trace.rebalanced_demand_nonlong_bounds positive hnot).2,
        hcost.trans_le (adjusted_phase_cost_weight_of_bound210 event (by decide : 1036 ≤ 1120)
          hnot hpos (event.rebalanced_cost_le_of_positive hpos)).2⟩
  change _ ≤ if e ∈ rebalancedPairIncrements210 then min coarse (rebalancedPairCostCap210 e) else coarse
  split
  · rename_i hm
    exact Nat.le_min.mpr ⟨hcoarse, hcost.trans_le (event.rebalanced_cost_le_pair_cap210 hpos hm)⟩
  · exact hcoarse

theorem rebalanced_next_horizon_mono210 : Monotone (fun i => (trace.event i).nextHorizon) := by
  intro i j order
  rcases lt_or_eq_of_le order with h | rfl
  · have hh := D_le_of_le ((trace.ordered h).trans (trace.event j).step.2.1.le)
    rwa [← (trace.event i).step.2.2.2.2.2.2.1, ← (trace.event j).step.2.2.2.2.2.2.1] at hh
  · exact le_rfl

private theorem next_horizon_le_before_of_lt {i j : Fin n} (order : i < j) :
    (trace.event i).nextHorizon ≤ (trace.event j).horizon := by
  have h := D_le_of_le (trace.ordered order)
  rwa [← (trace.event i).step.2.2.2.2.2.2.1, (trace.event j).step.1.2.1] at h

theorem rebalanced_credit_after_strict_mono210 : StrictMono trace.rebalancedCreditAfter := by
  intro i j order
  have h := trace.next_horizon_le_before_of_lt order
  have hj := moving_horizon_step_update (trace.event j).step
  have he := (trace.event j).step.2.2.2.1
  have hd := trace.rebalanced_credit_distance order.le
  omega

private theorem small_anchor_drift_le_growth {i j : Fin n} (order : i < j)
    (positive : 0 < trace.rebalancedDemand i) :
    smallAnchorDrift210 (d (trace.event i).hit) (d (trace.event j).hit) ≤
      (trace.event j).nextHorizon - (trace.event i).nextHorizon := by
  let I := trace.event i
  let J := trace.event j
  have hnext : I.nextHorizon ≤ J.horizon := trace.next_horizon_le_before_of_lt order
  have huI := moving_horizon_step_update I.step
  have huJ := moving_horizon_step_update J.step
  change smallAnchorDrift210 (d I.hit) (d J.hit) ≤ J.nextHorizon - I.nextHorizon
  unfold smallAnchorDrift210
  split
  · rename_i heq
    let e := d I.hit
    change e = d J.hit at heq
    have hcost := trace.cost_demand_eq_cost positive
    change trace.rebalancedDemand i = I.rebalancedCost.toNat at hcost
    have hpos : 0 < I.rebalancedCost := by omega
    have hunsupported : ¬ e ∣ 210 := I.rebalanced_cost_positive_unsupported hpos
    have hnonunit : 1 < e := I.step.2.2.2.1
    have hr : 3 ≤ I.hit := by have := I.step.1.1; have := I.step.2.1; omega
    have hodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le hr
    have hlarge : 5 ≤ e := by
      by_contra hn
      have hz : e = 3 := by omega
      exact hunsupported (hz.symm ▸ (by decide : 3 ∣ 210))
    have h₀ : e - 1 ≤ J.horizon - I.horizon := by omega
    have h₁ : 0 < J.horizon - I.horizon := by omega
    have hres := moving_horizon_factor_reuse_drift_residues I.step J.step (trace.ordered order)
      (by omega : 2 < e) (Nat.dvd_refl e) (heq ▸ Nat.dvd_refl e)
    have hd : 2 * e - 2 ≤ J.horizon - I.horizon := by
      rcases hres with h | h | h
      · have := Nat.le_of_dvd h₁ h.2.2
        omega
      · have := Nat.mod_le (J.horizon - I.horizon) (2 * e)
        omega
      · by_contra hbad
        have hrem := Nat.mod_eq_of_lt (by omega : J.horizon - I.horizon < 2 * e)
        omega
    omega
  · omega

theorem same_key_period_le_post_growth210 {a i : Fin n} (order : a < i)
    (key : (trace.event a).phaseKey = (trace.event i).phaseKey) :
    Nat.lcm 210 (2 * d (trace.event i).hit) ≤ trace.rebalancedWindowGrowth a i := by
  have hperiod := (same_phase_credit_interval_constraints210 (trace.samePhaseInterval order key)).2.2.1
  have he := congrArg Prod.fst key
  change d (trace.event a).hit = d (trace.event i).hit at he
  have hi := moving_horizon_step_update (trace.event i).step
  have ha := moving_horizon_step_update (trace.event a).step
  change Nat.lcm 210 (2 * d (trace.event a).hit) ≤ (trace.event i).horizon - (trace.event a).horizon at hperiod
  change _ ≤ (trace.event i).nextHorizon - (trace.event a).nextHorizon
  rw [he] at hperiod
  rw [hi, ha, he, Nat.add_sub_add_right]
  exact hperiod

private theorem small_anchor_period_with_tail {l r i j : Fin n}
    (inside : i ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r))
    (later : j ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r))
    (order : i ≤ j) :
    phaseCreditWidth210 (d (trace.event i).hit) + 2 * ((trace.event j).nextHorizon - (trace.event i).nextHorizon) ≤
      2 * trace.rebalancedWindowGrowth l r := by
  have hleft := trace.rebalanced_credit_after_strict_mono210.le_iff_le.mp (mem_filter.mp inside).2.2.1
  have hright := trace.rebalanced_credit_after_strict_mono210.le_iff_le.mp (mem_filter.mp later).2.2.2
  have hl : (trace.event l).nextHorizon ≤ (trace.event (trace.costAnchor trace.rebalancedCosts i)).nextHorizon :=
    trace.rebalanced_next_horizon_mono210 hleft
  have hr : (trace.event j).nextHorizon ≤ (trace.event r).nextHorizon := trace.rebalanced_next_horizon_mono210 hright
  obtain ⟨anchorOrder, key⟩ := trace.cost_demand_anchor (mem_filter.mp inside).2.1
  have hperiod := trace.same_key_period_le_post_growth210 anchorOrder key
  unfold rebalancedWindowGrowth at hperiod ⊢
  have hij : (trace.event i).nextHorizon ≤ (trace.event j).nextHorizon :=
    trace.rebalanced_next_horizon_mono210 order
  have hai : (trace.event (trace.costAnchor trace.rebalancedCosts i)).nextHorizon ≤ (trace.event i).nextHorizon :=
    trace.rebalanced_next_horizon_mono210 anchorOrder.le
  unfold phaseCreditWidth210
  omega

private theorem small_anchor_request_info {l r : Fin n}
    (deficit : 2 * trace.rebalancedWindowGrowth l r <
      3 * (∑ j ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l)
        (trace.rebalancedCreditAfter r), trace.rebalancedDemand j))
    (few : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l)
      (trace.rebalancedCreditAfter r)).card ≤ 3) {i : Fin n}
    (inside : i ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)) :
    d (trace.event i).hit ∈ smallAnchorIncrements210 ∧
      trace.rebalancedDemand i ≤ smallAnchorCap210 (d (trace.event i).hit) := by
  let req := trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)
  let event := trace.event i
  let e := d event.hit
  have periodFits (j : Fin n) (hj : j ∈ req) :
      trace.rebalancedPhasePeriodWidth j ≤ 2 * trace.rebalancedWindowGrowth l r := by
    simpa only [rebalancedPhasePeriodWidth, phaseCreditWidth210, Nat.sub_self, Nat.mul_zero,
      Nat.add_zero] using trace.small_anchor_period_with_tail hj hj le_rfl
  have hlong (j : Fin n) (hj : j ∈ req) (hl : trace.ReusedLong j) :
      d (trace.event j).hit ≤ 107 :=
    (trace.rebalanced_anchor_long_bounds_of_width_deficit210 deficit periodFits hj hl).2 few
  have cap (j : Fin n) (hj : j ∈ req) :
      trace.rebalancedDemand j ≤ smallAnchorCap210 (d (trace.event j).hit) :=
    trace.small_anchor_demand_le_cap (mem_filter.mp hj).2.1
      (hlong j hj)
  have hcap := cap i inside
  have hpos := (mem_filter.mp inside).2.1
  have hcost := trace.cost_demand_eq_cost hpos
  change trace.rebalancedDemand i = event.rebalancedCost.toNat at hcost
  have hpositive : 0 < event.rebalancedCost := by omega
  have hu : ¬ e ∣ 210 := event.rebalanced_cost_positive_unsupported hpositive
  have he : 1 < e := event.step.2.2.2.1
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have hodd : e % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hel : e ≤ 159 := by
    by_cases hl : trace.ReusedLong i
    · exact (hlong i inside hl).trans (by decide)
    · exact (trace.rebalanced_demand_nonlong_bounds hpos hl).1
  have hperiod : phaseCreditWidth210 e ≤ 2 * trace.rebalancedWindowGrowth l r := periodFits i inside
  have hrest : (∑ j ∈ req.erase i, trace.rebalancedDemand j) ≤ 10012 := by
    have hc : (req.erase i).card ≤ 2 := by
      rw [Finset.card_erase_of_mem inside]
      omega
    calc
      _ ≤ ∑ _j ∈ req.erase i, (5006 : Nat) :=
        Finset.sum_le_sum fun j hj => (cap j (mem_of_mem_erase hj)).trans (small_anchor_cap_le210 _)
      _ = (req.erase i).card * 5006 := by simp
      _ ≤ _ := by omega
  have hsplit := Finset.sum_erase_add _ inside (f := trace.rebalancedDemand)
  change (∑ j ∈ req.erase i, trace.rebalancedDemand j) + trace.rebalancedDemand i =
    (∑ j ∈ req, trace.rebalancedDemand j) at hsplit
  change 2 * trace.rebalancedWindowGrowth l r < 3 * (∑ j ∈ req, trace.rebalancedDemand j) at deficit
  change trace.rebalancedDemand i ≤ smallAnchorCap210 e at hcap
  have hwidth : phaseCreditWidth210 e < 3 * (smallAnchorCap210 e + 10012) := by omega
  exact ⟨small_anchor_increment_checked210 ⟨e, by omega⟩ he hodd hu (hpos.trans_le hcap) hwidth, hcap⟩

private theorem sum_small_anchor_requests_in_order {q : Nat} (requests : Finset (Fin n)) (card : requests.card = q) :
    (∑ i ∈ requests, trace.rebalancedDemand i) =
      ∑ k : Fin q, trace.rebalancedDemand (requests.orderEmbOfFin card k) := by
  calc
    _ = ∑ i ∈ (univ : Finset (Fin q)).map (requests.orderEmbOfFin card).toEmbedding, trace.rebalancedDemand i := by
      rw [Finset.map_orderEmbOfFin_univ]
    _ = _ := by rw [Finset.sum_map]; rfl

private theorem credit_window_order_of_request {l r i : Fin n}
    (inside : i ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)) :
    l < r := by
  obtain ⟨positive, ha, hb⟩ := (mem_filter.mp inside).2
  obtain ⟨order, key⟩ := trace.cost_demand_anchor positive
  have hfit := (trace.rebalanced_request_pays_period210 positive).trans
    (trace.same_key_rebalanced_credit_period order key)
  change 3 * trace.rebalancedDemand i ≤ trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i at hfit
  exact trace.rebalanced_credit_after_strict_mono210.lt_iff_lt.mp (by omega)

theorem rebalanced_anchor_pair_raw_deficit_bounds210 {l r : Fin n}
    (deficit : 2 * trace.rebalancedWindowGrowth l r <
      3 * (∑ i ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l)
        (trace.rebalancedCreditAfter r), trace.rebalancedDemand i))
    (card : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)).card = 2) :
    let req := trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)
    let cost := 3 * (∑ i ∈ req, trace.rebalancedDemand i)
    cost ≤ 10188 ∧ cost ≤ 2 * trace.rebalancedWindowGrowth l r + 4052 ∧
      4 * cost ≤ 15 * trace.rebalancedWindowGrowth l r ∧
      ∀ i ∈ req, d (trace.event i).hit ≤ 77 := by
  dsimp only
  let a := trace.rebalancedCreditAfter l
  let b := trace.rebalancedCreditAfter r
  let req := trace.rebalancedAnchorRequests a b
  change req.card = 2 at card
  let f := req.orderEmbOfFin card
  let i := f 0
  let j := f 1
  have hi : i ∈ req := req.orderEmbOfFin_mem card 0
  have hj : j ∈ req := req.orderEmbOfFin_mem card 1
  have hij : i < j := f.strictMono (by decide : (0 : Fin 2) < 1)
  obtain ⟨hei, hci⟩ := trace.small_anchor_request_info deficit (by omega : req.card ≤ 3) hi
  obtain ⟨hej, hcj⟩ := trace.small_anchor_request_info deficit (by omega : req.card ≤ 3) hj
  let e := d (trace.event i).hit
  let f' := d (trace.event j).hit
  have hsum := trace.sum_small_anchor_requests_in_order req card
  rw [Fin.sum_univ_two] at hsum
  change (∑ k ∈ req, trace.rebalancedDemand k) = trace.rebalancedDemand i + trace.rebalancedDemand j at hsum
  have hfirst : phaseCreditWidth210 e + 2 * ((trace.event j).nextHorizon - (trace.event i).nextHorizon) ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) := trace.small_anchor_period_with_tail hi hj hij.le
  have hlast : phaseCreditWidth210 f' + 2 * ((trace.event j).nextHorizon - (trace.event j).nextHorizon) ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) := trace.small_anchor_period_with_tail hj hj le_rfl
  have hstep : smallAnchorDrift210 e f' ≤ (trace.event j).nextHorizon - (trace.event i).nextHorizon :=
    trace.small_anchor_drift_le_growth hij (mem_filter.mp hi).2.1
  have hfloor : smallAnchorPairFloor210 e f' ≤ 2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) := by
    apply max_le
    · change phaseCreditWidth210 e + 2 * smallAnchorDrift210 e f' ≤ _
      omega
    · change phaseCreditWidth210 f' ≤ _
      omega
  change _ ≤ 2 * trace.rebalancedWindowGrowth l r at hfloor
  have htable := small_anchor_pair_width_test210 hei hej
  change 2 * trace.rebalancedWindowGrowth l r < 3 * (∑ k ∈ req, trace.rebalancedDemand k) at deficit
  change _ ≤ smallAnchorCap210 e at hci
  change _ ≤ smallAnchorCap210 f' at hcj
  have htest : smallAnchorPairFloor210 e f' < 3 * (smallAnchorCap210 e + smallAnchorCap210 f') := by omega
  obtain ⟨hc, hshort, he, hrate⟩ := htable htest
  change 3 * (smallAnchorCap210 e + smallAnchorCap210 f') ≤ 10188 at hc
  change 3 * (smallAnchorCap210 e + smallAnchorCap210 f') ≤ smallAnchorPairFloor210 e f' + 4052 at hshort
  change 8 * (3 * (smallAnchorCap210 e + smallAnchorCap210 f')) ≤ 15 * smallAnchorPairFloor210 e f' at hrate
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 10188 ∧
    3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 2 * trace.rebalancedWindowGrowth l r + 4052 ∧
    4 * (3 * (∑ i ∈ req, trace.rebalancedDemand i)) ≤ 15 * trace.rebalancedWindowGrowth l r ∧ _
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro k hk
  change k ∈ req at hk
  have hmap : (univ : Finset (Fin 2)).map f.toEmbedding = req := req.map_orderEmbOfFin_univ card
  rw [← hmap] at hk
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hk
  fin_cases t
  · exact (le_max_left e f').trans he
  · exact (le_max_right e f').trans he

theorem rebalanced_anchor_pair_deficit_ordered_bounds210 {l r : Fin n}
    (deficit : trace.RebalancedAnchorDeficit (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r))
    (card : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)).card = 2) :
    let a := trace.rebalancedCreditAfter l
    let b := trace.rebalancedCreditAfter r
    b - a ≤ 10187 ∧ (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) ≤ 1350 ∧
      3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) +
        3 * (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) ≤ b - a + 4052 ∧
      ∀ i ∈ trace.rebalancedAnchorRequests a b, d (trace.event i).hit ≤ 77 := by
  dsimp only
  let a := trace.rebalancedCreditAfter l
  let b := trace.rebalancedCreditAfter r
  let req := trace.rebalancedAnchorRequests a b
  change req.card = 2 at card
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < req.card)
  have hw := trace.rebalanced_credit_distance (trace.credit_window_order_of_request hi).le
  change b - a = 2 * trace.rebalancedWindowGrowth l r +
    3 * (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) at hw
  change b - a < 3 * (∑ i ∈ req, trace.rebalancedDemand i) at deficit
  have raw : 2 * trace.rebalancedWindowGrowth l r < 3 * (∑ i ∈ req, trace.rebalancedDemand i) := by omega
  obtain ⟨hcost, hshort, _, hinc⟩ := trace.rebalanced_anchor_pair_raw_deficit_bounds210 raw card
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 10188 at hcost
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 2 * trace.rebalancedWindowGrowth l r + 4052 at hshort
  change b - a ≤ _ ∧ _ ∧ 3 * (∑ i ∈ req, trace.rebalancedDemand i) + _ ≤ b - a + 4052 ∧ _
  exact ⟨by omega, by omega, by omega, hinc⟩

theorem rebalanced_anchor_triple_raw_deficit_bounds210 {l r : Fin n}
    (deficit : 2 * trace.rebalancedWindowGrowth l r <
      3 * (∑ i ∈ trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l)
        (trace.rebalancedCreditAfter r), trace.rebalancedDemand i))
    (card : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)).card = 3) :
    let req := trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)
    let cost := 3 * (∑ i ∈ req, trace.rebalancedDemand i)
    cost ≤ 43278 ∧ cost ≤ 2 * trace.rebalancedWindowGrowth l r + 8368 ∧
      5 * cost ≤ 28 * trace.rebalancedWindowGrowth l r ∧
      ∀ i ∈ req, d (trace.event i).hit ≤ 119 := by
  dsimp only
  let a := trace.rebalancedCreditAfter l
  let b := trace.rebalancedCreditAfter r
  let req := trace.rebalancedAnchorRequests a b
  change req.card = 3 at card
  let f := req.orderEmbOfFin card
  let i := f 0
  let j := f 1
  let k := f 2
  have hi : i ∈ req := req.orderEmbOfFin_mem card 0
  have hj : j ∈ req := req.orderEmbOfFin_mem card 1
  have hk : k ∈ req := req.orderEmbOfFin_mem card 2
  have hij : i < j := f.strictMono (by decide : (0 : Fin 3) < 1)
  have hjk : j < k := f.strictMono (by decide : (1 : Fin 3) < 2)
  obtain ⟨hei, hci⟩ := trace.small_anchor_request_info deficit card.le hi
  obtain ⟨hej, hcj⟩ := trace.small_anchor_request_info deficit card.le hj
  obtain ⟨hek, hck⟩ := trace.small_anchor_request_info deficit card.le hk
  let e := d (trace.event i).hit
  let f' := d (trace.event j).hit
  let g := d (trace.event k).hit
  have hsum := trace.sum_small_anchor_requests_in_order req card
  rw [Fin.sum_univ_three] at hsum
  change (∑ u ∈ req, trace.rebalancedDemand u) =
    trace.rebalancedDemand i + trace.rebalancedDemand j + trace.rebalancedDemand k at hsum
  have hfirst : phaseCreditWidth210 e + 2 * ((trace.event k).nextHorizon - (trace.event i).nextHorizon) ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) :=
    trace.small_anchor_period_with_tail hi hk (hij.trans hjk).le
  have hmiddle : phaseCreditWidth210 f' + 2 * ((trace.event k).nextHorizon - (trace.event j).nextHorizon) ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) :=
    trace.small_anchor_period_with_tail hj hk hjk.le
  have hlast : phaseCreditWidth210 g + 2 * ((trace.event k).nextHorizon - (trace.event k).nextHorizon) ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) :=
    trace.small_anchor_period_with_tail hk hk le_rfl
  have hstepI : smallAnchorDrift210 e f' ≤ (trace.event j).nextHorizon - (trace.event i).nextHorizon :=
    trace.small_anchor_drift_le_growth hij (mem_filter.mp hi).2.1
  have hstepJ : smallAnchorDrift210 f' g ≤ (trace.event k).nextHorizon - (trace.event j).nextHorizon :=
    trace.small_anchor_drift_le_growth hjk (mem_filter.mp hj).2.1
  have hnextI : (trace.event i).nextHorizon ≤ (trace.event j).nextHorizon := trace.rebalanced_next_horizon_mono210 hij.le
  have hnextJ : (trace.event j).nextHorizon ≤ (trace.event k).nextHorizon := trace.rebalanced_next_horizon_mono210 hjk.le
  have hfloor : smallAnchorTripleFloor210 e f' g ≤
      2 * ((trace.event r).nextHorizon - (trace.event l).nextHorizon) := by
    apply max_le
    · change phaseCreditWidth210 e + 2 * smallAnchorDrift210 e f' + 2 * smallAnchorDrift210 f' g ≤ _
      omega
    · apply max_le
      · change phaseCreditWidth210 f' + 2 * smallAnchorDrift210 f' g ≤ _
        omega
      · change phaseCreditWidth210 g ≤ _
        omega
  change _ ≤ 2 * trace.rebalancedWindowGrowth l r at hfloor
  have htable := small_anchor_triple_width_test210 hei hej hek
  change 2 * trace.rebalancedWindowGrowth l r < 3 * (∑ u ∈ req, trace.rebalancedDemand u) at deficit
  change _ ≤ smallAnchorCap210 e at hci
  change _ ≤ smallAnchorCap210 f' at hcj
  change _ ≤ smallAnchorCap210 g at hck
  have htest : smallAnchorTripleFloor210 e f' g <
      3 * (smallAnchorCap210 e + smallAnchorCap210 f' + smallAnchorCap210 g) := by omega
  obtain ⟨hc, hshort, he, hrate⟩ := htable htest
  change 3 * (smallAnchorCap210 e + smallAnchorCap210 f' + smallAnchorCap210 g) ≤ 43278 at hc
  change 3 * (smallAnchorCap210 e + smallAnchorCap210 f' + smallAnchorCap210 g) ≤
    smallAnchorTripleFloor210 e f' g + 8368 at hshort
  change 5 * (3 * (smallAnchorCap210 e + smallAnchorCap210 f' + smallAnchorCap210 g)) ≤ 14 * smallAnchorTripleFloor210 e f' g at hrate
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 43278 ∧
    3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 2 * trace.rebalancedWindowGrowth l r + 8368 ∧
    5 * (3 * (∑ i ∈ req, trace.rebalancedDemand i)) ≤ 28 * trace.rebalancedWindowGrowth l r ∧ _
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro u hu
  change u ∈ req at hu
  have hmap : (univ : Finset (Fin 3)).map f.toEmbedding = req := req.map_orderEmbOfFin_univ card
  rw [← hmap] at hu
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hu
  fin_cases t
  · exact (le_max_left e (max f' g)).trans he
  · exact (le_max_left f' g).trans ((le_max_right e (max f' g)).trans he)
  · exact (le_max_right f' g).trans ((le_max_right e (max f' g)).trans he)

theorem rebalanced_anchor_triple_deficit_ordered_bounds210 {l r : Fin n}
    (deficit : trace.RebalancedAnchorDeficit (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r))
    (card : (trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter l) (trace.rebalancedCreditAfter r)).card = 3) :
    let a := trace.rebalancedCreditAfter l
    let b := trace.rebalancedCreditAfter r
    b - a ≤ 43277 ∧ (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) ≤ 2789 ∧
      3 * (∑ i ∈ trace.rebalancedAnchorRequests a b, trace.rebalancedDemand i) +
        3 * (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) ≤ b - a + 8368 ∧
      ∀ i ∈ trace.rebalancedAnchorRequests a b, d (trace.event i).hit ≤ 119 := by
  dsimp only
  let a := trace.rebalancedCreditAfter l
  let b := trace.rebalancedCreditAfter r
  let req := trace.rebalancedAnchorRequests a b
  change req.card = 3 at card
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < req.card)
  have hw := trace.rebalanced_credit_distance (trace.credit_window_order_of_request hi).le
  change b - a = 2 * trace.rebalancedWindowGrowth l r +
    3 * (∑ k ∈ Ioc l r, trace.rebalancedNegativeCost k) at hw
  change b - a < 3 * (∑ i ∈ req, trace.rebalancedDemand i) at deficit
  have raw : 2 * trace.rebalancedWindowGrowth l r < 3 * (∑ i ∈ req, trace.rebalancedDemand i) := by omega
  obtain ⟨hcost, hshort, _, hinc⟩ := trace.rebalanced_anchor_triple_raw_deficit_bounds210 raw card
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 43278 at hcost
  change 3 * (∑ i ∈ req, trace.rebalancedDemand i) ≤ 2 * trace.rebalancedWindowGrowth l r + 8368 at hshort
  change b - a ≤ _ ∧ _ ∧ 3 * (∑ i ∈ req, trace.rebalancedDemand i) + _ ≤ b - a + 8368 ∧ _
  exact ⟨by omega, by omega, by omega, hinc⟩

end

end ResidualPhaseTrace210

end A166944Research
