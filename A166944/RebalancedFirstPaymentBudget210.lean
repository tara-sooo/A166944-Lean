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

theorem refined_rebalanced_first_payment_bound_of_high_growth210 (L U : Nat) (hL : 0 < L)
    (hU : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ refinedFirstPaymentGrowthBound210 L U (trace.growthAtHighFirstPayments L) := by
  classical
  let payment (i : Fin n) := (trace.event i).cappedFirstPayment
  let low := univ.filter fun i : Fin n => 0 < payment i ∧ d (trace.event i).hit ≤ L
  let high := (univ : Finset (Fin n)) \ low
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
  have hlow : (∑ i ∈ low, payment i) ≤
      ∑ e ∈ Nat.primesLE L, firstPaymentPhaseSlots210 e * weight e := by
    calc
      _ ≤ ∑ i ∈ low, weight (encode i).1 :=
        Finset.sum_le_sum fun i _ => (trace.event i).capped_first_payment_le_increment
      _ = ∑ x ∈ low.image encode, weight x.1 := by rw [Finset.sum_image hinj]
      _ ≤ ∑ x ∈ codes, weight x.1 := Finset.sum_le_sum_of_subset hsubset
      _ = _ := by simp [codes, Finset.sum_sigma, Finset.sum_const, card_first_payment_phases_at]
  let W := L * (L + 1)
  let A := min (firstPaymentCofactorWeight210 L U) ((37 * L + 1084) * (L + 1))
  have hhigh : (∑ i ∈ high, payment i) ≤ A * trace.growthAtHighFirstPayments L / W := by
    have hW : 0 < W := Nat.mul_pos (by omega) (by omega)
    apply (Nat.le_div_iff_mul_le hW).mpr
    rw [Nat.mul_comm (∑ i ∈ high, payment i), Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ high, if 0 < payment i then A * (d (trace.event i).hit - 1) else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzero : payment i = 0
        · simp [hzero]
        · have hpos : 0 < payment i := by omega
          have he : L < d (trace.event i).hit := by
            by_contra h
            have hle : d (trace.event i).hit ≤ L := by omega
            exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨mem_univ _, hpos, hle⟩)
          rw [if_pos hpos]
          change _ ≤ min (firstPaymentCofactorWeight210 L U) ((37 * L + 1084) * (L + 1)) *
            (d (trace.event i).hit - 1)
          rw [min_def]
          split
          · exact (trace.event i).capped_first_payment_large_weighted he (hU i)
          · exact capped_first_payment_large_linear_weighted (trace.event i) he
      _ = A * trace.growthAtHighFirstPayments L := by
        rw [← Finset.sum_filter, growthAtHighFirstPayments, Finset.mul_sum]
        congr 1
        ext i
        simp only [high, low, highFirstPaymentEvents, mem_sdiff, mem_filter, mem_univ, true_and, payment]
        omega
  have hsplit := Finset.sum_sdiff (f := payment) (Finset.subset_univ low)
  change (∑ i ∈ high, payment i) + (∑ i ∈ low, payment i) = trace.totalCappedFirstPayment at hsplit
  change trace.totalCappedFirstPayment ≤ (∑ e ∈ Nat.primesLE L, firstPaymentPhaseSlots210 e * weight e) +
    A * trace.growthAtHighFirstPayments L / W
  omega

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
theorem rebalanced_first_payment_bound_at_338210 (U : Nat) (hU : ∀ i, (trace.event i).horizon ≤ U) :
    trace.totalCappedFirstPayment ≤ 13887360 + 41 * trace.growthAtHighFirstPayments 338 := by
  apply (trace.refined_rebalanced_first_payment_bound_of_high_growth210 338 U (by decide) hU).trans
  have hlow : firstPaymentLowBound210 338 = 13887360 := by decide +kernel
  unfold refinedFirstPaymentGrowthBound210
  rw [hlow]
  apply Nat.add_le_add_left
  apply Nat.div_le_of_le_mul
  calc
    _ ≤ (41 * (338 * (338 + 1))) * trace.growthAtHighFirstPayments 338 :=
      Nat.mul_le_mul_right _ ((min_le_right _ _).trans (by decide))
    _ = _ := by ac_rfl

end ResidualPhaseTrace210

end A166944Research
