import A166944.RebalancedOverlapBudget210
import A166944.ResidualRebalancedTwoRequests210

/-! # Terminal demand intervals in cumulative signed credit -/

open Finset

namespace A166944Research

private theorem sum_cards_eq_union_add_earlier_intersections {α β : Type*} [LinearOrder α] [DecidableEq β]
    (selected : Finset α) (window : α → Finset β) :
    (∑ j ∈ selected, (window j).card) = (selected.biUnion window).card +
      ∑ j ∈ selected, (window j ∩ ((selected.filter fun i => i < j).biUnion window)).card := by
  classical
  induction selected using Finset.induction_on_max with
  | empty => simp
  | insert j selected earlier ih =>
      have hnew : j ∉ selected := fun hj => (lt_irrefl j) (earlier j hj)
      have hbefore : (insert j selected).filter (fun i => i < j) = selected := by
        ext i
        simp only [mem_filter, mem_insert]
        exact ⟨fun ⟨hi, hij⟩ => hi.resolve_left (ne_of_lt hij), fun hi => ⟨Or.inr hi, earlier i hi⟩⟩
      have hold (k : α) (hk : k ∈ selected) :
          (insert j selected).filter (fun i => i < k) = selected.filter (fun i => i < k) := by
        ext i
        simp only [mem_filter, mem_insert]
        exact ⟨fun ⟨hi, hik⟩ => ⟨hi.resolve_left (ne_of_lt (hik.trans (earlier k hk))), hik⟩,
          fun ⟨hi, hik⟩ => ⟨Or.inr hi, hik⟩⟩
      rw [Finset.sum_insert hnew, Finset.sum_insert hnew, Finset.biUnion_insert, hbefore]
      have hsum : (∑ k ∈ selected, (window k ∩ (((insert j selected).filter fun i => i < k).biUnion window)).card) =
          ∑ k ∈ selected, (window k ∩ ((selected.filter fun i => i < k).biUnion window)).card := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hold k hk]
      rw [hsum]
      have hcard := Finset.card_union_add_card_inter (window j) (selected.biUnion window)
      omega

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

abbrev rebalancedNegativeCost (i : Fin n) : Nat := (-trace.rebalancedCosts i).toNat

/-- Credit available immediately after event i, including its growth
and all negative residual costs up to that point. -/
def rebalancedCreditAfter (i : Fin n) : Nat :=
  2 * ((trace.event i).nextHorizon - D s) +
    3 * (∑ k ∈ Iic i, trace.rebalancedNegativeCost k)

def rebalancedTotalCredit : Nat :=
  2 * (D sf - D s) + 3 * (∑ k, trace.rebalancedNegativeCost k)

private theorem hit_monotone_for_credit : Monotone (fun i => (trace.event i).hit) := by
  intro i j order
  rcases lt_or_eq_of_le order with h | rfl
  · exact (trace.ordered h).trans (trace.event j).step.2.1.le
  · exact le_rfl

private theorem rebalanced_next_horizon_eq_D (i : Fin n) :
    (trace.event i).nextHorizon = D (trace.event i).hit := (trace.event i).step.2.2.2.2.2.2.1

private theorem rebalanced_next_horizon_ge_start (i : Fin n) :
    D s ≤ (trace.event i).nextHorizon := by
  rw [trace.rebalanced_next_horizon_eq_D]
  exact D_le_of_le ((trace.start_ge i).trans (trace.event i).step.2.1.le)

theorem rebalanced_credit_after_le_total (i : Fin n) :
    trace.rebalancedCreditAfter i ≤ trace.rebalancedTotalCredit := by
  have hC : (trace.event i).nextHorizon ≤ D sf :=
    trace.rebalanced_next_horizon_eq_D i ▸ D_le_of_le (trace.hit_le i)
  have hneg : (∑ k ∈ Iic i, trace.rebalancedNegativeCost k) ≤ ∑ k, trace.rebalancedNegativeCost k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  unfold rebalancedCreditAfter rebalancedTotalCredit
  omega

theorem rebalanced_credit_after_monotone : Monotone trace.rebalancedCreditAfter := by
  intro i j order
  have hC := D_le_of_le (trace.hit_monotone_for_credit order)
  rw [← trace.rebalanced_next_horizon_eq_D i, ← trace.rebalanced_next_horizon_eq_D j] at hC
  have hneg : (∑ k ∈ Iic i, trace.rebalancedNegativeCost k) ≤ ∑ k ∈ Iic j, trace.rebalancedNegativeCost k :=
    Finset.sum_le_sum_of_subset (Iic_subset_Iic.mpr order)
  unfold rebalancedCreditAfter
  omega

theorem rebalanced_credit_distance {i j : Fin n} (order : i ≤ j) :
    trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i =
      2 * ((trace.event j).nextHorizon - (trace.event i).nextHorizon) +
        3 * (∑ k ∈ Ioc i j, trace.rebalancedNegativeCost k) := by
  have hC := D_le_of_le (trace.hit_monotone_for_credit order)
  rw [← trace.rebalanced_next_horizon_eq_D i, ← trace.rebalanced_next_horizon_eq_D j] at hC
  have hstart := trace.rebalanced_next_horizon_ge_start i
  have hneg := Finset.sum_sdiff (f := trace.rebalancedNegativeCost)
    (Iic_subset_Iic.mpr order)
  have hd : Iic j \ Iic i = Ioc i j := by
    ext k
    simp only [mem_sdiff, mem_Iic, mem_Ioc, not_le]
    exact and_comm
  rw [hd] at hneg
  unfold rebalancedCreditAfter
  omega

/-- The growth between two hits is the sum of the actual increments
strictly after the first hit through the second hit. -/
theorem rebalanced_sum_growth_between_hits210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j : Fin n} (order : i ≤ j) :
    (∑ k ∈ Ioc i j, (d (trace.event k).hit - 1)) =
      (trace.event j).nextHorizon - (trace.event i).nextHorizon := by
  let a := (trace.event i).hit
  let b := (trace.event j).hit
  let f (x : Nat) : Int := (D (max a (min x b)) : Int)
  have hab : a ≤ b := trace.hit_monotone_for_credit order
  have below (x : Nat) (h : x ≤ a) : f x = (D a : Int) := by
    simp [f, max_eq_left ((min_le_left x b).trans h)]
  have above (x : Nat) (h : b ≤ x) : f x = (D b : Int) := by
    simp [f, min_eq_right h, max_eq_right hab]
  have inside (x : Nat) (ha : a ≤ x) (hb : x ≤ b) : f x = (D x : Int) := by
    simp [f, min_eq_left hb, max_eq_right ha]
  have hsum : (∑ k, (f (trace.event k).hit - f (trace.event k).start)) =
      ∑ k ∈ Ioc i j, ((d (trace.event k).hit - 1 : Nat) : Int) := by
    have hfilter : Ioc i j = univ.filter (fun k : Fin n => i < k ∧ k ≤ j) := by ext k; simp
    rw [hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    have hsh := (trace.event k).step.2.1.le
    by_cases hk : i < k ∧ k ≤ j
    · have hlo : a ≤ (trace.event k).start := trace.ordered hk.1
      have hhi : (trace.event k).hit ≤ b := trace.hit_monotone_for_credit hk.2
      have hupdate := moving_horizon_step_update (trace.event k).step
      have hpre := (trace.event k).step.1.2.1
      have hpost := trace.rebalanced_next_horizon_eq_D k
      rw [if_pos hk, inside _ (hlo.trans hsh) hhi, inside _ hlo (hsh.trans hhi)]
      omega
    · rw [if_neg hk]
      by_cases hki : k ≤ i
      · have hhi : (trace.event k).hit ≤ a := trace.hit_monotone_for_credit hki
        rw [below _ hhi, below _ (hsh.trans hhi), sub_self]
      · have hjk : j < k := lt_of_not_ge (fun h => hk ⟨lt_of_not_ge hki, h⟩)
        have hlo : b ≤ (trace.event k).start := trace.ordered hjk
        rw [above _ (hlo.trans hsh), above _ hlo, sub_self]
  have h := delta f
  have hs : s ≤ a := (trace.start_ge i).trans (trace.event i).step.2.1.le
  have hb : b ≤ sf := trace.hit_le j
  rw [hsum, ← Nat.cast_sum, below _ hs, above _ hb] at h
  change _ = (D (trace.event j).hit : Int) - D (trace.event i).hit at h
  rw [← trace.rebalanced_next_horizon_eq_D i, ← trace.rebalanced_next_horizon_eq_D j] at h
  omega

theorem rebalanced_credit_distance_eq_sum210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j : Fin n} (order : i ≤ j) :
    trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i =
      ∑ k ∈ Ioc i j, (2 * (d (trace.event k).hit - 1) + 3 * trace.rebalancedNegativeCost k) := by
  rw [trace.rebalanced_credit_distance order, ← trace.rebalanced_sum_growth_between_hits210 delta order,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem same_key_rebalanced_credit_period_with_negative {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    2 * Nat.lcm 210 (2 * d (trace.event j).hit) + 3 * (∑ k ∈ Ioc i j, trace.rebalancedNegativeCost k) ≤
      trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i := by
  let interval := trace.samePhaseInterval order key
  have hperiod := (same_phase_credit_interval_constraints210 interval).2.2.1
  have hincrement := interval.same_increment
  change d (trace.event i).hit = d (trace.event j).hit at hincrement
  change Nat.lcm 210 (2 * d (trace.event i).hit) ≤ (trace.event j).horizon - (trace.event i).horizon at hperiod
  rw [hincrement] at hperiod
  have hi := moving_horizon_step_update (trace.event i).step
  have hj := moving_horizon_step_update (trace.event j).step
  have h := trace.rebalanced_credit_distance order.le
  omega

theorem same_key_rebalanced_credit_period {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    2 * Nat.lcm 210 (2 * d (trace.event j).hit) ≤ trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i :=
  (Nat.le_add_right _ _).trans (trace.same_key_rebalanced_credit_period_with_negative order key)

def rebalancedCreditInterval (i : Fin n) : Finset Nat :=
  Ico (trace.rebalancedCreditAfter i - 3 * trace.rebalancedDemand i) (trace.rebalancedCreditAfter i)

theorem rebalanced_credit_interval_inside_anchor {i : Fin n} (positive : 0 < trace.rebalancedDemand i) :
    trace.rebalancedCreditInterval i ⊆ Ico
      (trace.rebalancedCreditAfter (trace.costAnchor trace.rebalancedCosts i)) (trace.rebalancedCreditAfter i) := by
  obtain ⟨order, key⟩ := trace.cost_demand_anchor positive
  have hp := (trace.rebalanced_request_pays_period210 positive).trans
    (trace.same_key_rebalanced_credit_period order key)
  change 3 * trace.rebalancedDemand i ≤ _ at hp
  intro x hx
  simp only [rebalancedCreditInterval, mem_Ico] at hx
  simp only [mem_Ico]
  omega

private theorem rebalanced_demand_le_credit_after (i : Fin n) :
    3 * trace.rebalancedDemand i ≤ trace.rebalancedCreditAfter i := by
  by_cases h : 0 < trace.rebalancedDemand i
  · obtain ⟨order, key⟩ := trace.cost_demand_anchor h
    exact ((trace.rebalanced_request_pays_period210 h).trans
      (trace.same_key_rebalanced_credit_period order key)).trans (Nat.sub_le _ _)
  · omega

theorem card_rebalanced_credit_interval (i : Fin n) :
    (trace.rebalancedCreditInterval i).card = 3 * trace.rebalancedDemand i := by
  rw [rebalancedCreditInterval, Nat.card_Ico]
  have h := trace.rebalanced_demand_le_credit_after i
  omega

theorem rebalanced_credit_intervals_disjoint_of_distance {i j : Fin n}
    (distance : 3 * trace.rebalancedDemand j ≤ trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i) :
    Disjoint (trace.rebalancedCreditInterval i) (trace.rebalancedCreditInterval j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [rebalancedCreditInterval, mem_Ico] at hx hy
  omega

theorem same_key_rebalanced_credit_intervals_disjoint {i j : Fin n}
    (order : i < j) (key : (trace.event i).phaseKey = (trace.event j).phaseKey) :
    Disjoint (trace.rebalancedCreditInterval i) (trace.rebalancedCreditInterval j) := by
  by_cases h : 0 < trace.rebalancedDemand j
  · exact trace.rebalanced_credit_intervals_disjoint_of_distance
      ((trace.rebalanced_request_pays_period210 h).trans (trace.same_key_rebalanced_credit_period order key))
  · have hz : trace.rebalancedDemand j = 0 := by omega
    simp [rebalancedCreditInterval, hz]

/-- A request whose own growth covers its cost lies to the right of
every earlier demand interval. -/
theorem rebalanced_credit_intervals_disjoint_of_own_growth {i j : Fin n} (order : i < j)
    (own : 3 * trace.rebalancedDemand j ≤ 2 * (d (trace.event j).hit - 1)) :
    Disjoint (trace.rebalancedCreditInterval i) (trace.rebalancedCreditInterval j) := by
  have hC := D_le_of_le (trace.ordered order)
  rw [← trace.rebalanced_next_horizon_eq_D i, (trace.event j).step.1.2.1] at hC
  have hj := moving_horizon_step_update (trace.event j).step
  have h := trace.rebalanced_credit_distance order.le
  exact trace.rebalanced_credit_intervals_disjoint_of_distance (by omega)

/-- Each large increment with a small relative gap supplies two
units per growth unit and three times its guaranteed negative cost. -/
theorem rebalanced_credit_distance_ge_large_increment_sum210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j : Fin n} (order : i ≤ j) (selected : Finset (Fin n)) (inside : selected ⊆ Ioc i j)
    (large : ∀ k ∈ selected, 339 ≤ d (trace.event k).hit ∧
      3 * ((trace.event k).hit - (trace.event k).start + 1) ≤ d (trace.event k).hit - 1) :
    11 * (∑ k ∈ selected, (d (trace.event k).hit - 1)) ≤
      trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i + 3036 * selected.card := by
  rw [trace.rebalanced_credit_distance_eq_sum210 delta order, Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ selected, (2 * (d (trace.event k).hit - 1) + 3 * trace.rebalancedNegativeCost k + 3036) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨he, hgap⟩ := large k hk
      have hunsupported : ¬ d (trace.event k).hit ∣ 210 := by
        intro hd
        have := Nat.le_of_dvd (by decide : 0 < 210) hd
        omega
      have hnet := (trace.event k).rebalanced_net_cost_le_outside_large_gaps210 hunsupported hgap
      have hcost := (trace.event k).rebalanced_cost_le_net
      change _ ≤ 2 * (d (trace.event k).hit - 1) + 3 * (-(trace.event k).rebalancedCost).toNat + 3036
      omega
    _ = (∑ k ∈ selected, (2 * (d (trace.event k).hit - 1) + 3 * trace.rebalancedNegativeCost k)) +
          3036 * selected.card := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum_of_subset inside) _

theorem rebalanced_credit_overlap_limits_large_increment_sum210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j : Fin n} (order : i < j)
    (overlap : ¬ Disjoint (trace.rebalancedCreditInterval i) (trace.rebalancedCreditInterval j))
    (selected : Finset (Fin n)) (inside : selected ⊆ Ioc i j)
    (large : ∀ k ∈ selected, 339 ≤ d (trace.event k).hit ∧
      3 * ((trace.event k).hit - (trace.event k).start + 1) ≤ d (trace.event k).hit - 1) :
    11 * (∑ k ∈ selected, (d (trace.event k).hit - 1)) <
      3 * trace.rebalancedDemand j + 3036 * selected.card := by
  have hsum := trace.rebalanced_credit_distance_ge_large_increment_sum210 delta order.le selected inside large
  have hdist : trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i < 3 * trace.rebalancedDemand j :=
    Nat.lt_of_not_ge (fun h => overlap (trace.rebalanced_credit_intervals_disjoint_of_distance h))
  omega

/-- An intervening increment of at least 595 with a small relative
gap separates the later request from every earlier interval if it
does not reuse a long prime phase. -/
theorem rebalanced_nonlong_credit_intervals_disjoint_of_large_separator210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j k : Fin n} (order : i < k) (inside : k ≤ j)
    (large : 595 ≤ d (trace.event k).hit)
    (smallGap : 3 * ((trace.event k).hit - (trace.event k).start + 1) ≤ d (trace.event k).hit - 1)
    (nonlong : ¬ trace.ReusedLong j) :
    Disjoint (trace.rebalancedCreditInterval i) (trace.rebalancedCreditInterval j) := by
  by_cases hpos : 0 < trace.rebalancedDemand j
  · have hcap : trace.rebalancedDemand j ≤ 1166 := (trace.rebalanced_demand_nonlong_bounds hpos nonlong).2
    have hsep := trace.rebalanced_credit_distance_ge_large_increment_sum210 delta (order.le.trans inside) {k}
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_Ioc] using And.intro order inside)
      (by intro x hx; obtain rfl := Finset.mem_singleton.mp hx; exact ⟨by omega, smallGap⟩)
    simp only [Finset.sum_singleton, Finset.card_singleton, mul_one] at hsep
    exact trace.rebalanced_credit_intervals_disjoint_of_distance (by omega)
  · have hz : trace.rebalancedDemand j = 0 := by omega
    simp [rebalancedCreditInterval, hz]

def rebalancedCreditUnion : Finset Nat := univ.biUnion trace.rebalancedCreditInterval

theorem rebalanced_credit_union_le_total : trace.rebalancedCreditUnion.card ≤ trace.rebalancedTotalCredit := by
  have hsub : trace.rebalancedCreditUnion ⊆ Ico 0 trace.rebalancedTotalCredit := by
    intro x hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
    have hr := (mem_Ico.mp hi).2
    exact mem_Ico.mpr ⟨Nat.zero_le _, hr.trans_le (trace.rebalanced_credit_after_le_total i)⟩
  simpa only [Nat.card_Ico, Nat.sub_zero] using Finset.card_le_card hsub

def rebalancedPriorDifferentCredit (i : Fin n) : Nat :=
  (univ.filter fun j => j < i ∧ 0 < trace.rebalancedDemand j ∧
    (trace.event j).phaseKey ≠ (trace.event i).phaseKey).sup trace.rebalancedCreditAfter

/-- Part of a demand that extends before the latest earlier positive
request of another key, in units of cumulative credit. -/
private def rebalancedCreditOverhang (i : Fin n) : Nat :=
  3 * trace.rebalancedDemand i - (trace.rebalancedCreditAfter i - trace.rebalancedPriorDifferentCredit i)

def rebalancedEarlierCreditOverlap (j : Fin n) : Nat :=
  (trace.rebalancedCreditInterval j ∩ ((Iio j).biUnion trace.rebalancedCreditInterval)).card

/-- The cost units used more than once are counted at the later
interval that uses them. -/
theorem rebalanced_demand_eq_credit_union_and_overlap :
    3 * (∑ i, trace.rebalancedDemand i) =
      trace.rebalancedCreditUnion.card + ∑ j, trace.rebalancedEarlierCreditOverlap j := by
  have h := sum_cards_eq_union_add_earlier_intersections (univ : Finset (Fin n)) trace.rebalancedCreditInterval
  have hfilter (j : Fin n) : univ.filter (fun i => i < j) = Iio j := by ext i; simp
  simp only [trace.card_rebalanced_credit_interval, hfilter, ← Finset.mul_sum] at h
  exact h

theorem card_rebalanced_credit_pair_intersection {i j : Fin n} (order : i < j) :
    (trace.rebalancedCreditInterval i ∩ trace.rebalancedCreditInterval j).card =
      min (3 * trace.rebalancedDemand i)
        (3 * trace.rebalancedDemand j - (trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i)) := by
  let a := trace.rebalancedCreditAfter i
  let b := trace.rebalancedCreditAfter j
  let wi := 3 * trace.rebalancedDemand i
  let wj := 3 * trace.rebalancedDemand j
  have hab : a ≤ b := trace.rebalanced_credit_after_monotone order.le
  have hwi : wi ≤ a := trace.rebalanced_demand_le_credit_after i
  have hwj : wj ≤ b := trace.rebalanced_demand_le_credit_after j
  have hinter : trace.rebalancedCreditInterval i ∩ trace.rebalancedCreditInterval j =
      Ico (max (a - wi) (b - wj)) a := by
    ext x
    change x ∈ Ico (a - wi) a ∩ Ico (b - wj) b ↔ x ∈ Ico (max (a - wi) (b - wj)) a
    simp only [mem_inter, mem_Ico, max_le_iff]
    omega
  rw [hinter, Nat.card_Ico]
  change a - max (a - wi) (b - wj) = min wi (wj - (b - a))
  rw [max_def, min_def]
  split <;> split <;> omega

theorem rebalanced_credit_pair_overlap_le_of_separators210
    (delta : ∀ f : Nat → Int, (∑ k, (f (trace.event k).hit - f (trace.event k).start)) = f sf - f s)
    {i j : Fin n} (order : i < j) (selected : Finset (Fin n)) (inside : selected ⊆ Ioc i j)
    (large : ∀ k ∈ selected, 339 ≤ d (trace.event k).hit ∧
      3 * ((trace.event k).hit - (trace.event k).start + 1) ≤ d (trace.event k).hit - 1) :
    (trace.rebalancedCreditInterval i ∩ trace.rebalancedCreditInterval j).card ≤
      min (3 * trace.rebalancedDemand i) (3 * trace.rebalancedDemand j + 3036 * selected.card -
        11 * (∑ k ∈ selected, (d (trace.event k).hit - 1))) := by
  rw [trace.card_rebalanced_credit_pair_intersection order]
  have h := trace.rebalanced_credit_distance_ge_large_increment_sum210 delta order.le selected inside large
  exact min_le_min_left _ (by omega)

private theorem rebalanced_earlier_credit_overlap_le_overhang (j : Fin n) :
    trace.rebalancedEarlierCreditOverlap j ≤ trace.rebalancedCreditOverhang j := by
  let r := trace.rebalancedCreditAfter j
  let width := 3 * trace.rebalancedDemand j
  let cut := trace.rebalancedPriorDifferentCredit j
  have hsub : trace.rebalancedCreditInterval j ∩ ((Iio j).biUnion trace.rebalancedCreditInterval) ⊆
      Ico (r - width) (min r cut) := by
    intro x hx
    obtain ⟨hj, hx⟩ := mem_inter.mp hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    have hij := mem_Iio.mp hi
    have hk : (trace.event i).phaseKey ≠ (trace.event j).phaseKey := by
      intro key
      exact (Finset.disjoint_left.mp (trace.same_key_rebalanced_credit_intervals_disjoint hij key)) hxi hj
    have hpos : 0 < trace.rebalancedDemand i := by
      obtain ⟨hl, hr⟩ := mem_Ico.mp hxi
      omega
    have hcut : trace.rebalancedCreditAfter i ≤ cut :=
      Finset.le_sup (f := trace.rebalancedCreditAfter) (mem_filter.mpr ⟨mem_univ _, hij, hpos, hk⟩)
    exact mem_Ico.mpr ⟨(mem_Ico.mp hj).1,
      lt_min ((mem_Ico.mp hj).2) ((mem_Ico.mp hxi).2.trans_le hcut)⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  change trace.rebalancedEarlierCreditOverlap j ≤ min r cut - (r - width) at hcard
  have hw : width ≤ r := trace.rebalanced_demand_le_credit_after j
  change trace.rebalancedEarlierCreditOverlap j ≤ width - (r - cut)
  rw [min_def] at hcard
  split at hcard <;> omega

/-- Bound each interval's duplicate credit by both its overhang past
the latest different key and the sum of its pairwise intersections. -/
def rebalancedCreditExcess (j : Fin n) : Nat :=
  min (trace.rebalancedCreditOverhang j)
    (∑ i ∈ Iio j, min (3 * trace.rebalancedDemand i)
      (3 * trace.rebalancedDemand j - (trace.rebalancedCreditAfter j - trace.rebalancedCreditAfter i)))

theorem rebalanced_earlier_credit_overlap_le_excess (j : Fin n) :
    trace.rebalancedEarlierCreditOverlap j ≤ trace.rebalancedCreditExcess j := by
  apply Nat.le_min.mpr
  refine ⟨trace.rebalanced_earlier_credit_overlap_le_overhang j, ?_⟩
  unfold rebalancedEarlierCreditOverlap
  rw [Finset.inter_biUnion]
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.inter_comm, trace.card_rebalanced_credit_pair_intersection (mem_Iio.mp hi)]

theorem rebalanced_demand_le_credit_union_and_excess :
    3 * (∑ i, trace.rebalancedDemand i) ≤ trace.rebalancedCreditUnion.card + ∑ i, trace.rebalancedCreditExcess i := by
  rw [trace.rebalanced_demand_eq_credit_union_and_overlap]
  exact Nat.add_le_add_left (Finset.sum_le_sum fun j _ => trace.rebalanced_earlier_credit_overlap_le_excess j) _

def rebalancedCreditAdjustment : Int :=
  ((∑ i, trace.rebalancedCreditExcess i : Nat) : Int) -
    (trace.rebalancedTotalCredit - trace.rebalancedCreditUnion.card : Nat)

def rebalancedCreditDebt : Int :=
  3 * ((∑ i, trace.rebalancedDemand i : Nat) : Int) - trace.rebalancedTotalCredit

theorem rebalanced_credit_debt_le_adjustment : trace.rebalancedCreditDebt ≤ trace.rebalancedCreditAdjustment := by
  have hdemand := trace.rebalanced_demand_le_credit_union_and_excess
  have hunion := trace.rebalanced_credit_union_le_total
  unfold rebalancedCreditDebt rebalancedCreditAdjustment
  omega

theorem rebalanced_net_cost_eq_credit_debt210 :
    3 * (∑ i, (trace.event i).rebalancedNetCost) =
      (3 * trace.totalCappedFirstPayment + 3 * trace.costStartupSum trace.rebalancedCosts +
        2 * (D sf - D s) : Nat) + trace.rebalancedCreditDebt := by
  rw [trace.sum_rebalanced_net_cost_parts210]
  unfold rebalancedCreditDebt rebalancedTotalCredit
  simp only [rebalancedNegativeCost]
  omega

theorem rebalanced_net_cost_le_of_credit_intervals210 :
    3 * (∑ i, (trace.event i).rebalancedNetCost) ≤
      (3 * trace.totalCappedFirstPayment + 3 * trace.costStartupSum trace.rebalancedCosts +
        2 * (D sf - D s) : Nat) + trace.rebalancedCreditAdjustment := by
  rw [trace.rebalanced_net_cost_eq_credit_debt210]
  have h := trace.rebalanced_credit_debt_le_adjustment
  omega

/-- Unused credit outside any band containing the intervals may be
deducted from the sum of their excesses. -/
theorem rebalanced_credit_adjustment_le_of_band {lo hi : Nat}
    (band : ∀ i, trace.rebalancedCreditInterval i ⊆ Ico lo hi) :
    trace.rebalancedCreditAdjustment ≤
      ((∑ i, trace.rebalancedCreditExcess i : Nat) : Int) - (trace.rebalancedTotalCredit - (hi - lo) : Nat) := by
  have hsub : trace.rebalancedCreditUnion ⊆ Ico lo hi := by
    intro x hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
    exact band i hi
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  unfold rebalancedCreditAdjustment
  omega

end

end ResidualPhaseTrace210

private theorem rebalanced_crossing_signed_of_credit_debt_budget210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (budget : (3 * firstUpper + 3 * trace.costStartupSum trace.rebalancedCosts +
      35 * (C - (2 * M - 2)) + 72 * (r - s) +
      3 * rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) + trace.rebalancedCreditDebt <
      ((36 * (M + 1) + 3 * rebalancedPotential210 s C : Nat) : Int)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hcost := trace.rebalanced_net_cost_eq_credit_debt210
  rw [hstart, hend] at hcost
  omega

/-- The cumulative credit estimate can be combined with an upper
bound on first payments to contradict the signed crossing lower bound. -/
theorem rebalanced_crossing_signed_of_credit_budget210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (budget : (3 * firstUpper + 3 * trace.costStartupSum trace.rebalancedCosts +
      35 * (C - (2 * M - 2)) + 72 * (r - s) +
      3 * rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) + trace.rebalancedCreditAdjustment <
      ((36 * (M + 1) + 3 * rebalancedPotential210 s C : Nat) : Int)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  apply rebalanced_crossing_signed_of_credit_debt_budget210 ledger trace firstBound
  have h := trace.rebalanced_credit_debt_le_adjustment
  omega

/-- The first payments and the exact repeat demand minus available
credit share one allowance at and above the finite threshold. -/
theorem rebalanced_crossing_signed_of_credit_debt_allowance210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (allowance : 10 * (3 * (firstUpper : Int) + trace.rebalancedCreditDebt) ≤ (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  apply rebalanced_crossing_signed_of_credit_debt_budget210 ledger trace firstBound
  have hpath := residual_phase_balances210_path ledger
  have hC := canonical_horizon_bound_of_short_travel hpath short
  have hstate := moving_horizon_path_endpoint hpath
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hModd := canonical ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
  have hgap := (Nat.mul_le_mul_left 1536 gap).trans (fifty_million_sqrt_budget (by omega : 50000000 ≤ M))
  have hV := rebalanced_potential210_le (M + 2) (2 * M - 2) (by omega)
  have hstartup := trace.rebalanced_startup_cost_le
  omega

theorem rebalanced_crossing_signed_of_credit_allowance210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (allowance : 10 * (3 * (firstUpper : Int) + trace.rebalancedCreditAdjustment) ≤ (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  apply rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace firstBound
  have h := trace.rebalanced_credit_debt_le_adjustment
  omega

/-- For sufficiently large records the sublinear first-payment
estimate leaves at least 27/80 of the record for a positive adjustment. -/
theorem rebalanced_crossing_signed_of_credit_allowance_eventually210 :
    ∃ threshold : Nat, ∀ {M s C r p first : Nat} {balance : Int},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
        (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M → r - s ≤ Nat.sqrt (4 * (3 * M + 4)) →
      ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance,
        80 * trace.rebalancedCreditAdjustment ≤ (27 * M : Nat) →
        (∑ i, (trace.event i).rebalancedNetCost) +
          (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
            ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  obtain ⟨B, hB⟩ := canonical_first_prime_phase_travel_sublinear 420 128 (by decide)
  refine ⟨max 367232911 B, ?_⟩
  intro M s C r p first balance hM canonical ledger short gap trace adjustment
  obtain ⟨_, hphase⟩ := residual_phase_balances210_original ledger
  have hfirst : 128 * first ≤ M := hB ((le_max_right 367232911 B).trans hM) canonical hphase short
  have hpayment : trace.totalCappedFirstPayment ≤ 24 * first :=
    trace.total_capped_first_payment_le.trans (Nat.mul_le_mul_left 24 trace.scaled_first_travel_le)
  exact rebalanced_crossing_signed_of_credit_allowance210 ((le_max_left 367232911 B).trans hM)
    canonical ledger short gap trace (Nat.le_refl _) (by omega)

end A166944Research
