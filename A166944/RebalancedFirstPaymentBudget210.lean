import A166944.RebalancedCrossingGrowth210

/-! # Reachable phases and growth for capped first payments -/

open Finset

namespace A166944Research

namespace ResidualPhaseEvent210

private theorem avoids_horizon_residues (event : ResidualPhaseEvent210) {p : Nat}
    (hp : 1 < p) (gap : 2 * p < event.hit - event.start) :
    event.horizon % p ≠ 1 ∧ event.horizon % p ≠ p - 1 := by
  have hleft : ¬ p ∣ event.horizon - 1 := by
    intro h
    have := moving_horizon_gap_le_twice_even_factor event.step hp h
    omega
  have hright : ¬ p ∣ event.horizon + 1 := by
    intro h
    have := moving_horizon_gap_le_twice_odd_factor event.step hp h
    omega
  constructor
  · intro hC
    have hpos := event.step.1.2.2
    have hsum := congrArg (fun x : Nat => x % p) (Nat.sub_add_cancel (by omega : 1 ≤ event.horizon))
    rw [Nat.add_mod, Nat.mod_eq_of_lt hp, hC] at hsum
    have hrem := Nat.mod_lt (event.horizon - 1) (by omega : 0 < p)
    by_cases h : (event.horizon - 1) % p + 1 = p
    · rw [h, Nat.mod_self] at hsum
      omega
    · rw [Nat.mod_eq_of_lt (by omega : (event.horizon - 1) % p + 1 < p)] at hsum
      exact hleft (Nat.dvd_of_mod_eq_zero (by omega))
  · intro hC
    apply hright
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, Nat.mod_eq_of_lt hp, hC, Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.mod_self]

private theorem positive_net_of_positive_first_payment (event : ResidualPhaseEvent210)
    (positive : 0 < event.cappedFirstPayment) :
    0 < event.rebalancedNetCost ∧ ¬ d event.hit ∣ 210 := by
  have hcap : event.cappedFirstPayment ≤ event.rebalancedNetCost.toNat := min_le_right _ _
  have hpos : 0 < event.rebalancedNetCost := by omega
  refine ⟨hpos, ?_⟩
  intro hd
  simp [potentialNetCost, hd] at hpos

theorem first_payment_horizon_residues210 (event : ResidualPhaseEvent210)
    (positive : 0 < event.cappedFirstPayment) :
    event.horizon % 2 = 0 ∧ event.horizon % 3 = 0 ∧
      event.horizon % 5 ≠ 1 ∧ event.horizon % 5 ≠ 4 ∧
      (127 ≤ d event.hit → event.horizon % 7 ≠ 1 ∧ event.horizon % 7 ≠ 6) := by
  have hgap := (event.first_phase_of_positive_capped_payment positive).1
  have heven := event.step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le event.step.1.1
  have h3 := event.avoids_horizon_residues (p := 3) (by decide) (by omega)
  obtain ⟨h5a, h5b⟩ := event.avoids_horizon_residues (p := 5) (by decide) (by omega)
  refine ⟨heven, by omega, h5a, h5b, ?_⟩
  intro he
  obtain ⟨hpos, hu⟩ := event.positive_net_of_positive_first_payment positive
  have hcost := event.rebalanced_net_cost_le_of_unsupported hu
  exact event.avoids_horizon_residues (p := 7) (by decide) (by omega)

theorem rebalanced_net_cost_le_outside_large_gaps210 (event : ResidualPhaseEvent210)
    (hu : ¬ d event.hit ∣ 210)
    (smallGap : 3 * (event.hit - event.start + 1) ≤ d event.hit - 1) :
    event.rebalancedNetCost ≤ 1012 - 3 * ((d event.hit - 1 : Nat) : Int) := by
  have hcost := event.rebalanced_net_cost_le_of_unsupported hu
  omega

theorem positive_first_payment_large_gap (event : ResidualPhaseEvent210)
    (large : 339 ≤ d event.hit) (positive : 0 < event.cappedFirstPayment) :
    d event.hit - 1 < 3 * (event.hit - event.start + 1) := by
  obtain ⟨hpos, hu⟩ := event.positive_net_of_positive_first_payment positive
  by_contra h
  have hcost := event.rebalanced_net_cost_le_outside_large_gaps210 hu (by omega)
  omega

end ResidualPhaseEvent210

def firstPaymentPhaseSlots210 (e : Nat) : Nat :=
  if e ∣ 210 then 0 else if e < 127 then 42 else 30

private def firstPaymentPhases (avoidSeven : Bool) : Finset (Fin 420) :=
  univ.filter fun phase =>
    let C := phase.val / 2
    C % 2 = 0 ∧ C % 3 = 0 ∧ C % 5 ≠ 1 ∧ C % 5 ≠ 4 ∧
      (avoidSeven = true → C % 7 ≠ 1 ∧ C % 7 ≠ 6)

private def firstPaymentPhasesAt (e : Nat) : Finset (Fin 420) :=
  if e ∣ 210 then ∅ else firstPaymentPhases (decide (127 ≤ e))

private theorem card_first_payment_phases_at (e : Nat) :
    (firstPaymentPhasesAt e).card = firstPaymentPhaseSlots210 e := by
  have hshort : (firstPaymentPhases false).card = 42 := by decide
  have hlong : (firstPaymentPhases true).card = 30 := by decide
  by_cases hd : e ∣ 210
  · simp [firstPaymentPhasesAt, firstPaymentPhaseSlots210, hd]
  by_cases he : e < 127
  · simp [firstPaymentPhasesAt, firstPaymentPhaseSlots210, hd, he, show ¬ 127 ≤ e by omega, hshort]
  · simp [firstPaymentPhasesAt, firstPaymentPhaseSlots210, hd, he, show 127 ≤ e by omega, hlong]

private theorem first_payment_phase_mem (event : ResidualPhaseEvent210)
    (positive : 0 < event.cappedFirstPayment) :
    event.phaseKey.2 ∈ firstPaymentPhasesAt (d event.hit) := by
  have hu := (event.positive_net_of_positive_first_payment positive).2
  obtain ⟨h2, h3, h5a, h5b, h7⟩ := event.first_payment_horizon_residues210 positive
  rw [firstPaymentPhasesAt, if_neg hu, firstPaymentPhases]
  apply Finset.mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hphase : event.phaseKey.2.val / 2 = event.horizon % 210 := by
    change (2 * (event.horizon % 210) + event.hit % 2) / 2 = _
    omega
  simp only [hphase, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 210),
    Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 210), Nat.mod_mod_of_dvd _ (by decide : 5 ∣ 210),
    Nat.mod_mod_of_dvd _ (by decide : 7 ∣ 210), decide_eq_true_eq]
  exact ⟨h2, h3, h5a, h5b, h7⟩

private def firstPaymentLowBound210 (L : Nat) : Nat :=
  ∑ p ∈ Nat.primesLE L, firstPaymentPhaseSlots210 p * min (48 * p) (37 * p + 1047)

private def firstPaymentCofactorWeight210 (L U : Nat) : Nat :=
  48 * (U + 1) + 1036 * (L + 1) - 11 * (L * (L + 1))

/-- Positive first payments at low increments use at most 42 phases per
prime, or 30 from increment 127. -/
def refinedFirstPaymentCutoffBound210 (L U largeGapGrowth : Nat) : Nat :=
  firstPaymentLowBound210 L + firstPaymentCofactorWeight210 L U * largeGapGrowth / (L * (L + 1))

def refinedFirstPaymentGrowthBound210 (L U highGrowth : Nat) : Nat :=
  firstPaymentLowBound210 L +
    min (firstPaymentCofactorWeight210 L U) ((37 * L + 1084) * (L + 1)) * highGrowth / (L * (L + 1))

private theorem capped_first_payment_large_linear_weighted (event : ResidualPhaseEvent210) {L : Nat}
    (large : L < d event.hit) :
    (L * (L + 1)) * event.cappedFirstPayment ≤ ((37 * L + 1084) * (L + 1)) * (d event.hit - 1) := by
  let g := d event.hit - 1
  have hg : L ≤ g := by dsimp [g]; omega
  have hp := event.capped_first_payment_le_increment.trans (min_le_right _ _)
  have h : L * event.cappedFirstPayment ≤ (37 * L + 1084) * g := calc
    _ ≤ L * (37 * g + 1084) := Nat.mul_le_mul_left _ (by dsimp [g]; omega)
    _ = 37 * L * g + 1084 * L := by rw [Nat.mul_add]; ac_rfl
    _ ≤ 37 * L * g + 1084 * g := Nat.add_le_add_left (Nat.mul_le_mul_left _ hg) _
    _ = _ := by rw [Nat.add_mul]
  calc
    _ = (L + 1) * (L * event.cappedFirstPayment) := by ac_rfl
    _ ≤ (L + 1) * ((37 * L + 1084) * g) := Nat.mul_le_mul_left _ h
    _ = _ := by change _ = ((37 * L + 1084) * (L + 1)) * g; ac_rfl

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def highFirstPaymentEvents (L : Nat) : Finset (Fin n) :=
  univ.filter fun i => 0 < (trace.event i).cappedFirstPayment ∧ L < d (trace.event i).hit

def growthAtHighFirstPayments (L : Nat) : Nat :=
  ∑ i ∈ trace.highFirstPaymentEvents L, (d (trace.event i).hit - 1)

private def lowFirstPaymentEvents (L : Nat) : Finset (Fin n) :=
  univ.filter fun i => 0 < (trace.event i).cappedFirstPayment ∧ d (trace.event i).hit ≤ L

private theorem first_payment_low_sum_le (L : Nat) :
    (∑ i ∈ trace.lowFirstPaymentEvents L, (trace.event i).cappedFirstPayment) ≤ firstPaymentLowBound210 L := by
  classical
  let payment (i : Fin n) := (trace.event i).cappedFirstPayment
  let low := trace.lowFirstPaymentEvents L
  let weight (e : Nat) := min (48 * e) (37 * e + 1047)
  let codes := (Nat.primesLE L).sigma firstPaymentPhasesAt
  let encode (i : Fin n) : Σ _ : Nat, Fin 420 := ⟨d (trace.event i).hit, (trace.event i).phaseKey.2⟩
  have hsubset : low.image encode ⊆ codes := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hpositive, hle⟩ := (Finset.mem_filter.mp hi).2
    have hphase := (trace.event i).first_phase_of_positive_capped_payment hpositive
    have he : 1 < d (trace.event i).hit := (trace.event i).step.2.2.2.1
    have hp := prime_of_no_proper_factor (by omega : 2 ≤ d (trace.event i).hit) hphase.2.1
    exact Finset.mem_sigma.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hle, hp⟩, first_payment_phase_mem (trace.event i) hpositive⟩
  have hinj : Set.InjOn encode (low : Set (Fin n)) := by
    intro i hi j hj h
    apply trace.positive_first_payment_key_unique (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hj).2.1
    exact Prod.ext (congrArg Sigma.fst h) (congrArg (fun x : Σ _ : Nat, Fin 420 => x.2) h)
  change (∑ i ∈ low, payment i) ≤ _
  unfold firstPaymentLowBound210
  calc
    _ ≤ ∑ i ∈ low, weight (encode i).1 :=
      Finset.sum_le_sum fun i _ => (trace.event i).capped_first_payment_le_increment
    _ = ∑ x ∈ low.image encode, weight x.1 := by rw [Finset.sum_image hinj]
    _ ≤ ∑ x ∈ codes, weight x.1 := Finset.sum_le_sum_of_subset hsubset
    _ = _ := by simp [codes, weight, Finset.sum_sigma, Finset.sum_const, card_first_payment_phases_at]

private theorem sum_capped_first_payment_split (L : Nat) :
    trace.totalCappedFirstPayment =
      (∑ i ∈ trace.lowFirstPaymentEvents L, (trace.event i).cappedFirstPayment) +
      ∑ i ∈ trace.highFirstPaymentEvents L, (trace.event i).cappedFirstPayment := by
  unfold totalCappedFirstPayment lowFirstPaymentEvents highFirstPaymentEvents
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpos : 0 < (trace.event i).cappedFirstPayment
  · by_cases hle : d (trace.event i).hit ≤ L
    · simp [hpos, hle, Nat.not_lt_of_ge hle]
    · simp [hpos, hle, Nat.lt_of_not_ge hle]
  · simp [Nat.eq_zero_of_not_pos hpos]

theorem refined_rebalanced_first_payment_bound_of_high_growth210 (L U : Nat) (hL : 0 < L)
    (hU : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ refinedFirstPaymentGrowthBound210 L U (trace.growthAtHighFirstPayments L) := by
  let high := trace.highFirstPaymentEvents L
  let payment (i : Fin n) := (trace.event i).cappedFirstPayment
  let W := L * (L + 1)
  let A := min (firstPaymentCofactorWeight210 L U) ((37 * L + 1084) * (L + 1))
  have hhigh : (∑ i ∈ high, payment i) ≤ A * trace.growthAtHighFirstPayments L / W := by
    have hW : 0 < W := Nat.mul_pos hL (by omega)
    apply (Nat.le_div_iff_mul_le hW).mpr
    rw [Nat.mul_comm (∑ i ∈ high, payment i), Finset.mul_sum, growthAtHighFirstPayments, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have he := (mem_filter.mp hi).2.2
    change _ ≤ min (firstPaymentCofactorWeight210 L U) ((37 * L + 1084) * (L + 1)) *
      (d (trace.event i).hit - 1)
    rw [min_def]
    split
    · exact (trace.event i).capped_first_payment_large_weighted he (hU i)
    · exact capped_first_payment_large_linear_weighted (trace.event i) he
  rw [trace.sum_capped_first_payment_split L]
  exact Nat.add_le_add (trace.first_payment_low_sum_le L) hhigh

theorem growth_at_high_first_payments_le_large_gaps210 {L : Nat} (hL : 338 ≤ L) :
    trace.growthAtHighFirstPayments L ≤ trace.growthAtLargeGaps := by
  unfold growthAtHighFirstPayments growthAtLargeGaps ResidualPhaseEvent210.growthWithLargeGap
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  obtain ⟨hpos, he⟩ := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _, (trace.event i).positive_first_payment_large_gap (by omega) hpos⟩

theorem refined_rebalanced_first_payment_bound210 (L U : Nat) (hL : 338 ≤ L)
    (hU : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ refinedFirstPaymentCutoffBound210 L U trace.growthAtLargeGaps := by
  apply (trace.refined_rebalanced_first_payment_bound_of_high_growth210 L U (by omega) hU).trans
  unfold refinedFirstPaymentGrowthBound210 refinedFirstPaymentCutoffBound210
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul (min_le_left _ _)
    (trace.growth_at_high_first_payments_le_large_gaps210 hL))) _

set_option maxRecDepth 16384 in
private theorem first_payment_low_bound_at_338 : firstPaymentLowBound210 338 = 13887360 := by
  decide +kernel

theorem rebalanced_first_payment_bound_at_338210 (U : Nat) (hU : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ 13887360 + 41 * trace.growthAtHighFirstPayments 338 := by
  apply (trace.refined_rebalanced_first_payment_bound_of_high_growth210 338 U (by decide) hU).trans
  unfold refinedFirstPaymentGrowthBound210
  rw [first_payment_low_bound_at_338]
  apply Nat.add_le_add_left
  apply Nat.div_le_of_le_mul
  calc
    _ ≤ (41 * (338 * (338 + 1))) * trace.growthAtHighFirstPayments 338 :=
      Nat.mul_le_mul_right _ ((min_le_right _ _).trans (by decide))
    _ = _ := by ac_rfl

private noncomputable def runEnds (selected : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact selected.filter fun i => ¬ ∃ j ∈ selected, j.val = i.val + 1

noncomputable def highFirstPaymentRunEnds (L : Nat) : Finset (Fin n) :=
  runEnds (trace.highFirstPaymentEvents L)

def highFirstPaymentGapShortfall (L : Nat) : Nat :=
  ∑ i ∈ trace.highFirstPaymentEvents L, (2 * d (trace.event i).hit - ((trace.event i).hit - (trace.event i).start))

private theorem rebalanced_potential_change_le_run_ends (selected : Finset (Fin n)) :
    (∑ i ∈ selected,
      ((rebalancedPotential210 (trace.event i).hit (trace.event i).nextHorizon : Int) -
        rebalancedPotential210 (trace.event i).start (trace.event i).horizon)) ≤
      (1036 * (runEnds selected).card : Nat) := by
  classical
  let ends := runEnds selected
  let interior := selected \ ends
  let before (i : Fin n) := rebalancedPotential210 (trace.event i).start (trace.event i).horizon
  let after (i : Fin n) := rebalancedPotential210 (trace.event i).hit (trace.event i).nextHorizon
  let next (i : Fin n) : Fin n := if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i
  have hnext (i : Fin n) (hi : i ∈ interior) : (next i).val = i.val + 1 ∧ next i ∈ selected := by
    obtain ⟨hs, he⟩ := mem_sdiff.mp hi
    have hex : ∃ j ∈ selected, j.val = i.val + 1 := by
      by_contra h
      exact he (mem_filter.mpr ⟨hs, h⟩)
    obtain ⟨j, hj, hv⟩ := hex
    have hn : i.val + 1 < n := hv ▸ j.isLt
    have h : next i = j := Fin.ext (by simp [next, hn, hv])
    exact ⟨by simp [next, hn], h.symm ▸ hj⟩
  have hinj : Set.InjOn next (interior : Set (Fin n)) := by
    intro i hi j hj h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [(hnext i hi).1, (hnext j hj).1] at hv
    omega
  have hpaid : (∑ i ∈ interior, after i) ≤ ∑ i ∈ selected, before i := by
    calc
      _ = ∑ i ∈ interior, before (next i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hstart := trace.consecutive (hnext i hi).1
        have hbefore := (trace.event (next i)).step.1.2.1
        have hafter := (trace.event i).step.2.2.2.2.2.2.1
        simp only [before, after]
        rw [← hbefore, hstart, hafter]
      _ = ∑ j ∈ interior.image next, before j := (Finset.sum_image hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        exact (hnext i hi).2)
  have hend : (∑ i ∈ ends, after i) ≤ 1036 * ends.card := by
    calc
      _ ≤ ∑ _i ∈ ends, (1036 : Nat) := by
        apply Finset.sum_le_sum
        intro i _
        have heven := (trace.event i).step.2.2.2.2.2.2.1 ▸
          D_mod_two_eq_zero_of_two_le (trace.event i).step.2.2.2.2.2.2.2.2.1
        exact rebalanced_potential210_le _ _ heven
      _ = _ := by simp [Nat.mul_comm]
  have hsplit := Finset.sum_sdiff (f := after) (show ends ⊆ selected from filter_subset _ _)
  change (∑ i ∈ interior, after i) + (∑ i ∈ ends, after i) = ∑ i ∈ selected, after i at hsplit
  change (∑ i ∈ selected, ((after i : Int) - before i)) ≤ (1036 * ends.card : Nat)
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum]
  omega

/-- Use the actual gap shortfalls and one potential allowance per
consecutive run of high first payments. -/
theorem rebalanced_first_payment_bound_of_gap_shortfall_at_338210 :
    trace.totalCappedFirstPayment + 24 * trace.highFirstPaymentGapShortfall 338 ≤
      13887360 + 37 * trace.growthAtHighFirstPayments 338 +
        48 * (trace.highFirstPaymentEvents 338).card + 1036 * (trace.highFirstPaymentRunEnds 338).card := by
  let high := trace.highFirstPaymentEvents 338
  let growth (i : Fin n) := d (trace.event i).hit - 1
  let gapShortfall (i : Fin n) := 2 * d (trace.event i).hit - ((trace.event i).hit - (trace.event i).start)
  let changePotential (i : Fin n) : Int :=
    (rebalancedPotential210 (trace.event i).hit (trace.event i).nextHorizon : Int) -
      rebalancedPotential210 (trace.event i).start (trace.event i).horizon
  have hlocal (i : Fin n) (hi : i ∈ high) :
      ((trace.event i).cappedFirstPayment : Int) + 24 * gapShortfall i ≤
        37 * growth i + 48 + changePotential i := by
    let event := trace.event i
    have hpos : 0 < event.cappedFirstPayment := (mem_filter.mp hi).2.1
    have ⟨_, hu⟩ := event.positive_net_of_positive_first_payment hpos
    have hcap : event.cappedFirstPayment ≤ event.rebalancedNetCost.toNat := min_le_right _ _
    have hpay : (event.cappedFirstPayment : Int) ≤ event.rebalancedNetCost := by omega
    unfold ResidualPhaseEvent210.rebalancedNetCost ResidualPhaseEvent210.potentialNetCost at hpay
    rw [if_neg hu] at hpay
    have hgap := moving_horizon_step_gap_le_twice_increment event.step
    have he := event.step.2.2.2.1
    change (event.cappedFirstPayment : Int) + 24 * (2 * d event.hit - (event.hit - event.start) : Nat) ≤
      37 * (d event.hit - 1 : Nat) + 48 +
        ((rebalancedPotential210 event.hit event.nextHorizon : Int) - rebalancedPotential210 event.start event.horizon)
    omega
  have hsum := Finset.sum_le_sum hlocal
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hrun := trace.rebalanced_potential_change_le_run_ends high
  change (∑ i ∈ high, changePotential i) ≤ (1036 * (trace.highFirstPaymentRunEnds 338).card : Nat) at hrun
  have hlow := trace.first_payment_low_sum_le 338
  rw [first_payment_low_bound_at_338] at hlow
  rw [trace.sum_capped_first_payment_split 338]
  change _ + (∑ i ∈ high, (trace.event i).cappedFirstPayment) + 24 * (∑ i ∈ high, gapShortfall i) ≤
    13887360 + 37 * (∑ i ∈ high, growth i) + 48 * high.card + 1036 * (trace.highFirstPaymentRunEnds 338).card
  omega

end ResidualPhaseTrace210

end A166944Research
