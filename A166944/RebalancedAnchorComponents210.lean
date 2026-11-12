import A166944.RebalancedSmallAnchorDeficits210

/-! # Disjoint anchored components and the signed prefix budget -/

open Finset

namespace A166944Research

/-- Cover a finite union of half-open intervals by disjoint intervals
with the original endpoints. Every input interval stays in one component. -/
private theorem interval_component_cover {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (requests : Finset ι) (start finish : ι → α) (credit : α → Nat) :
    ∀ lo hi : Nat,
      (∀ i ∈ requests, lo ≤ credit (start i) ∧ credit (start i) < credit (finish i) ∧ credit (finish i) ≤ hi) →
      ∃ blocks : Finset (α × α),
        (∀ w ∈ blocks, lo ≤ credit w.1 ∧ credit w.1 < credit w.2 ∧ credit w.2 ≤ hi) ∧
        (blocks : Set (α × α)).PairwiseDisjoint (fun w => Ico (credit w.1) (credit w.2)) ∧
        (∀ i ∈ requests, ∃ w ∈ blocks, credit w.1 ≤ credit (start i) ∧ credit (finish i) ≤ credit w.2) ∧
        blocks.biUnion (fun w => Ico (credit w.1) (credit w.2)) =
          requests.biUnion (fun i => Ico (credit (start i)) (credit (finish i))) := by
  classical
  let span (w : α × α) := Ico (credit w.1) (credit w.2)
  let interval (i : ι) := Ico (credit (start i)) (credit (finish i))
  refine Finset.strongInductionOn requests ?_
  intro req ih lo hi valid
  rcases req.eq_empty_or_nonempty with hempty | hne
  · subst req
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  obtain ⟨i, hiL, hmin⟩ := Finset.exists_min_image req (fun i => credit (start i)) hne
  obtain ⟨j, hiR, hmax⟩ := Finset.exists_max_image req (fun i => credit (finish i)) hne
  let a := credit (start i)
  let b := credit (finish j)
  have hab : a < b := (valid i hiL).2.1.trans_le (hmax i hiL)
  have hsub : req.biUnion interval ⊆ Ico a b := by
    intro x hx
    obtain ⟨k, hk, hmem⟩ := mem_biUnion.mp hx
    obtain ⟨hl, hr⟩ := mem_Ico.mp hmem
    exact mem_Ico.mpr ⟨(hmin k hk).trans hl, hr.trans_le (hmax k hk)⟩
  by_cases covered : Ico a b ⊆ req.biUnion interval
  · refine ⟨{(start i, finish j)}, ?_, ?_, ?_, ?_⟩
    · intro w hw
      obtain rfl := mem_singleton.mp hw
      exact ⟨(valid i hiL).1, hab, (valid j hiR).2.2⟩
    · intro w hw z hz hne
      exact (hne ((mem_singleton.mp hw).trans (mem_singleton.mp hz).symm)).elim
    · exact fun k hk => ⟨(start i, finish j), mem_singleton_self _, hmin k hk, hmax k hk⟩
    · change ({(start i, finish j)} : Finset (α × α)).biUnion span = _
      rw [Finset.singleton_biUnion]
      exact subset_antisymm covered hsub
  · obtain ⟨x, hx, hgap⟩ := Finset.not_subset.mp covered
    have ⟨hax, hxb⟩ := mem_Ico.mp hx
    have side (k : ι) (hk : k ∈ req) :
        credit (finish k) ≤ x ∨ x < credit (start k) := by
      by_contra h
      apply hgap
      exact mem_biUnion.mpr ⟨k, hk, mem_Ico.mpr ⟨by omega, by omega⟩⟩
    let before := req.filter fun k => credit (finish k) ≤ x
    let after := req.filter fun k => x < credit (start k)
    have hbefore : before ⊂ req :=
      Finset.filter_ssubset.mpr ⟨j, hiR, by omega⟩
    have hafter : after ⊂ req :=
      Finset.filter_ssubset.mpr ⟨i, hiL, by omega⟩
    have hleftValid (k : ι) (hk : k ∈ before) :
        lo ≤ credit (start k) ∧ credit (start k) < credit (finish k) ∧ credit (finish k) ≤ x := by
      obtain ⟨hk', h⟩ := mem_filter.mp hk
      exact ⟨(valid k hk').1, (valid k hk').2.1, h⟩
    have hrightValid (k : ι) (hk : k ∈ after) :
        x + 1 ≤ credit (start k) ∧ credit (start k) < credit (finish k) ∧ credit (finish k) ≤ hi := by
      obtain ⟨hk', h⟩ := mem_filter.mp hk
      exact ⟨by omega, (valid k hk').2.1, (valid k hk').2.2⟩
    obtain ⟨L, hL, hLd, hLc, hLu⟩ := ih before hbefore lo x hleftValid
    obtain ⟨R, hR, hRd, hRc, hRu⟩ := ih after hafter (x + 1) hi hrightValid
    have hlox := (valid i hiL).1.trans hax
    have hxhi := hxb.le.trans (valid j hiR).2.2
    have hcross {u v : α × α} (hu : u ∈ L) (hv : v ∈ R) : Disjoint (span u) (span v) := by
      rw [Finset.disjoint_left]
      intro z hzu hzv
      have hlt := (mem_Ico.mp hzu).2.trans_le (hL u hu).2.2
      have hle := (hR v hv).1.trans (mem_Ico.mp hzv).1
      omega
    refine ⟨L ∪ R, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases mem_union.mp hw with h | h
      · exact ⟨(hL w h).1, (hL w h).2.1, (hL w h).2.2.trans hxhi⟩
      · exact ⟨hlox.trans ((Nat.le_succ _).trans (hR w h).1), (hR w h).2⟩
    · intro u hu v hv hne
      rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
      · exact hLd hu hv hne
      · exact hcross hu hv
      · exact (hcross hv hu).symm
      · exact hRd hu hv hne
    · intro k hk
      rcases side k hk with h | h
      · obtain ⟨w, hw, hb⟩ := hLc k (mem_filter.mpr ⟨hk, h⟩)
        exact ⟨w, mem_union_left _ hw, hb⟩
      · obtain ⟨w, hw, hb⟩ := hRc k (mem_filter.mpr ⟨hk, h⟩)
        exact ⟨w, mem_union_right _ hw, hb⟩
    · change (L ∪ R).biUnion span = req.biUnion interval
      change L.biUnion span = before.biUnion interval at hLu
      change R.biUnion span = after.biUnion interval at hRu
      rw [Finset.union_biUnion, hLu, hRu, ← Finset.union_biUnion]
      congr 1
      ext k
      constructor
      · intro hk
        rcases mem_union.mp hk with hk | hk
        · exact (mem_filter.mp hk).1
        · exact (mem_filter.mp hk).1
      · intro hk
        rcases side k hk with h | h
        · exact mem_union_left _ (mem_filter.mpr ⟨hk, h⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hk, h⟩)

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def rebalancedComponentInterval (w : Fin n × Fin n) : Finset Nat :=
  Ico (trace.rebalancedCreditAfter w.1) (trace.rebalancedCreditAfter w.2)

def rebalancedComponentRequests (w : Fin n × Fin n) : Finset (Fin n) :=
  trace.rebalancedAnchorRequests (trace.rebalancedCreditAfter w.1) (trace.rebalancedCreditAfter w.2)

def rebalancedComponentDebt (w : Fin n × Fin n) : Int :=
  3 * ((∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i : Nat) : Int) -
    ((trace.rebalancedComponentInterval w).card : Int)

structure RebalancedAnchorComponents where
  windows : Finset (Fin n × Fin n)
  ordered : ∀ w ∈ windows, w.1 < w.2
  disjoint : (windows : Set (Fin n × Fin n)).PairwiseDisjoint trace.rebalancedComponentInterval
  covered : ∀ i, 0 < trace.rebalancedDemand i → ∃ w ∈ windows, i ∈ trace.rebalancedComponentRequests w
  exactUnion : windows.biUnion trace.rebalancedComponentInterval =
    (univ.filter fun i => 0 < trace.rebalancedDemand i).biUnion trace.rebalancedAnchorInterval

theorem rebalanced_anchor_components_exist210 : Nonempty trace.RebalancedAnchorComponents := by
  let requests := univ.filter fun i => 0 < trace.rebalancedDemand i
  have hvalid (i : Fin n) (hi : i ∈ requests) :
      0 ≤ trace.rebalancedAnchorCredit i ∧
        trace.rebalancedAnchorCredit i < trace.rebalancedCreditAfter i ∧
          trace.rebalancedCreditAfter i ≤ trace.rebalancedTotalCredit := by
    have hp := (mem_filter.mp hi).2
    obtain ⟨order, key⟩ := trace.cost_demand_anchor hp
    have hfit := (trace.rebalanced_request_pays_period210 hp).trans
      (trace.same_key_rebalanced_credit_period order key)
    change 3 * trace.rebalancedDemand i ≤ trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i at hfit
    exact ⟨Nat.zero_le _, by omega, trace.rebalanced_credit_after_le_total i⟩
  obtain ⟨blocks, bounds, disjoint, covered, union⟩ :=
    interval_component_cover requests (trace.costAnchor trace.rebalancedCosts) id trace.rebalancedCreditAfter
      0 trace.rebalancedTotalCredit hvalid
  refine ⟨⟨blocks, ?_, disjoint, ?_, union⟩⟩
  · intro w hw
    exact trace.rebalanced_credit_after_strict_mono210.lt_iff_lt.mp (bounds w hw).2.1
  · intro i hp
    obtain ⟨w, hw, hleft, hright⟩ := covered i (mem_filter.mpr ⟨mem_univ _, hp⟩)
    exact ⟨w, hw, mem_filter.mpr ⟨mem_univ _, hp, hleft, hright⟩⟩

def RebalancedAnchorComponents.unused (cover : trace.RebalancedAnchorComponents) : Nat :=
  trace.rebalancedTotalCredit - ∑ w ∈ cover.windows, (trace.rebalancedComponentInterval w).card

theorem rebalanced_credit_debt_eq_component_debts210 (cover : trace.RebalancedAnchorComponents) :
    trace.rebalancedCreditDebt =
      (∑ w ∈ cover.windows, trace.rebalancedComponentDebt w) - (cover.unused : Int) := by
  let requests := univ.filter fun i => 0 < trace.rebalancedDemand i
  have hdisjoint : (cover.windows : Set (Fin n × Fin n)).PairwiseDisjoint trace.rebalancedComponentRequests := by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨hp, ha, hb⟩ := (mem_filter.mp hi).2
    obtain ⟨_, hc, hd⟩ := (mem_filter.mp hj).2
    obtain ⟨order, key⟩ := trace.cost_demand_anchor hp
    have hfit := (trace.rebalanced_request_pays_period210 hp).trans
      (trace.same_key_rebalanced_credit_period order key)
    change 3 * trace.rebalancedDemand i ≤ trace.rebalancedCreditAfter i - trace.rebalancedAnchorCredit i at hfit
    have hpos : trace.rebalancedAnchorCredit i < trace.rebalancedCreditAfter i := by omega
    exact (Finset.disjoint_left.mp (cover.disjoint hu hv hne))
      (mem_Ico.mpr ⟨ha, hpos.trans_le hb⟩) (mem_Ico.mpr ⟨hc, hpos.trans_le hd⟩)
  have hreq : cover.windows.biUnion trace.rebalancedComponentRequests = requests := by
    ext i
    constructor
    · intro hi
      obtain ⟨w, hw, hiw⟩ := mem_biUnion.mp hi
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hiw).2.1⟩
    · intro hi
      obtain ⟨w, hw, hiw⟩ := cover.covered i (mem_filter.mp hi).2
      exact mem_biUnion.mpr ⟨w, hw, hiw⟩
  have hsum : (∑ w ∈ cover.windows, ∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) =
      ∑ i, trace.rebalancedDemand i := by
    rw [← Finset.sum_biUnion hdisjoint, hreq]
    exact (sum_positive_requests _ _).symm
  have hwidth : (∑ w ∈ cover.windows, (trace.rebalancedComponentInterval w).card) ≤ trace.rebalancedTotalCredit := by
    rw [← Finset.card_biUnion cover.disjoint]
    have hsub : cover.windows.biUnion trace.rebalancedComponentInterval ⊆ Ico 0 trace.rebalancedTotalCredit := by
      intro x hx
      obtain ⟨w, _, hw⟩ := mem_biUnion.mp hx
      exact mem_Ico.mpr ⟨Nat.zero_le _,
        (mem_Ico.mp hw).2.trans_le (trace.rebalanced_credit_after_le_total w.2)⟩
    simpa only [Nat.card_Ico, Nat.sub_zero] using Finset.card_le_card hsub
  unfold rebalancedCreditDebt rebalancedComponentDebt RebalancedAnchorComponents.unused
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, hsum]
  omega

/-- Use the finite shortfall caps, less the negative costs already
credited, for small components. Use the actual debt elsewhere. -/
def rebalancedComponentAllowance (w : Fin n × Fin n) : Nat :=
  let negative := ∑ k ∈ Ioc w.1 w.2, trace.rebalancedNegativeCost k
  if 0 < trace.rebalancedComponentDebt w ∧ (trace.rebalancedComponentRequests w).card = 2 then
    4052 - 3 * negative
  else if 0 < trace.rebalancedComponentDebt w ∧ (trace.rebalancedComponentRequests w).card = 3 then
    8368 - 3 * negative
  else (trace.rebalancedComponentDebt w).toNat

theorem rebalanced_component_debt_le_allowance210 (w : Fin n × Fin n) :
    trace.rebalancedComponentDebt w ≤ (trace.rebalancedComponentAllowance w : Int) := by
  dsimp only [rebalancedComponentAllowance]
  have deficient (positive : 0 < trace.rebalancedComponentDebt w) :
      trace.RebalancedAnchorDeficit (trace.rebalancedCreditAfter w.1) (trace.rebalancedCreditAfter w.2) := by
    unfold rebalancedComponentDebt rebalancedComponentInterval at positive
    rw [Nat.card_Ico] at positive
    change _ < 3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i)
    omega
  split
  · rename_i h2
    have h := (trace.rebalanced_anchor_pair_deficit_ordered_bounds210 (deficient h2.1) h2.2).2.2.1
    unfold rebalancedComponentDebt rebalancedComponentInterval
    rw [Nat.card_Ico]
    change 3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) +
      3 * (∑ k ∈ Ioc w.1 w.2, trace.rebalancedNegativeCost k) ≤ _ at h
    omega
  · split
    · rename_i h3
      have h := (trace.rebalanced_anchor_triple_deficit_ordered_bounds210 (deficient h3.1) h3.2).2.2.1
      unfold rebalancedComponentDebt rebalancedComponentInterval
      rw [Nat.card_Ico]
      change 3 * (∑ i ∈ trace.rebalancedComponentRequests w, trace.rebalancedDemand i) +
        3 * (∑ k ∈ Ioc w.1 w.2, trace.rebalancedNegativeCost k) ≤ _ at h
      omega
    · omega

theorem rebalanced_credit_debt_le_component_allowance210 (cover : trace.RebalancedAnchorComponents) :
    trace.rebalancedCreditDebt ≤
      ((∑ w ∈ cover.windows, trace.rebalancedComponentAllowance w : Nat) : Int) - (cover.unused : Int) := by
  have h := Finset.sum_le_sum (s := cover.windows)
    (fun w _ => trace.rebalanced_component_debt_le_allowance210 w)
  rw [← Nat.cast_sum] at h
  rw [trace.rebalanced_credit_debt_eq_component_debts210 cover]
  omega

end

end ResidualPhaseTrace210

theorem rebalanced_crossing_signed_of_component_allowance210
    {M s C r p first firstUpper : Nat} {balance : Int}
    (hM : 367232911 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (firstBound : trace.totalCappedFirstPayment ≤ firstUpper)
    (cover : trace.RebalancedAnchorComponents)
    (allowance : 10 * (3 * (firstUpper : Int) +
      ((∑ w ∈ cover.windows, trace.rebalancedComponentAllowance w : Nat) : Int) - (cover.unused : Int)) ≤
        (9 * M : Nat)) :
    (∑ i, (trace.event i).rebalancedNetCost) +
      (24 * (r - s) + 11 * (C - (2 * M - 2)) + rebalancedPotential210 (M + 2) (2 * M - 2) : Nat) <
        ((12 * (M + 1) + rebalancedPotential210 s C : Nat) : Int) := by
  have h := trace.rebalanced_credit_debt_le_component_allowance210 cover
  exact rebalanced_crossing_signed_of_credit_debt_allowance210 hM canonical ledger short gap trace firstBound (by omega)

end A166944Research
