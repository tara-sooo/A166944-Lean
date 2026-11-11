import A166944.ResidualScaledPotential210

/-! # First-hit bounds for two small prime reuse requests -/

open Finset

namespace A166944Research

def smallReusePrimes210 : Finset Nat := {11, 13, 17, 19, 23, 29, 31}

private theorem small_unsupported_prime_cases210 :
    ∀ p : Fin 35, 1 < p.val → NoProperFactor p.val → ¬ p.val ∣ 210 → p.val ∈ smallReusePrimes210 := by
  decide +kernel

private def longGapHorizons210 : List Nat := [0, 12, 18, 30, 42, 60, 72, 102, 108, 138, 150, 168, 180, 192, 198]

private theorem long_gap_horizon_cases210 :
    ∀ c : Fin 210, c.val % 2 = 0 →
      ¬ 3 ∣ c.val + 209 → ¬ 3 ∣ c.val + 1 →
      ¬ 5 ∣ c.val + 209 → ¬ 5 ∣ c.val + 1 →
      ¬ 7 ∣ c.val + 209 → ¬ 7 ∣ c.val + 1 → c.val ∈ longGapHorizons210 := by
  decide +kernel

/-- A factor 3, 5 or 7 of either horizon term would force an earlier
hit within fourteen steps. The remaining even horizon residues are finite. -/
private theorem moving_horizon_long_gap_residue210 {s C r C' : Nat}
    (step : IsMovingHorizonStep s C r C') (long : 14 < r - s) : C % 210 ∈ longGapHorizons210 := by
  have hC := step.1.2.2
  have heven := step.1.2.1 ▸ D_mod_two_eq_zero_of_two_le step.1.1
  have hleft {f : Nat} (hf : 1 < f) (hsmall : f ≤ 7) (hperiod : f ∣ 210) : ¬ f ∣ C % 210 + 209 := by
    intro hd
    have hd' : f ∣ C - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd (C - 1) hperiod,
        show (C - 1) % 210 = (C % 210 + 209) % 210 by omega, Nat.mod_mod_of_dvd _ hperiod]
      exact Nat.mod_eq_zero_of_dvd hd
    have hgap := moving_horizon_gap_le_twice_even_factor step hf hd'
    omega
  have hright {f : Nat} (hf : 1 < f) (hsmall : f ≤ 7) (hperiod : f ∣ 210) : ¬ f ∣ C % 210 + 1 := by
    intro hd
    have hd' : f ∣ C + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd (C + 1) hperiod,
        show (C + 1) % 210 = (C % 210 + 1) % 210 by omega, Nat.mod_mod_of_dvd _ hperiod]
      exact Nat.mod_eq_zero_of_dvd hd
    have hgap := moving_horizon_gap_le_twice_odd_factor step hf hd'
    omega
  exact long_gap_horizon_cases210 ⟨C % 210, Nat.mod_lt _ (by decide)⟩
    (by change (C % 210) % 2 = 0; omega)
    (hleft (f := 3) (by decide) (by decide) (by decide))
    (hright (f := 3) (by decide) (by decide) (by decide))
    (hleft (f := 5) (by decide) (by decide) (by decide))
    (hright (f := 5) (by decide) (by decide) (by decide))
    (hleft (f := 7) (by decide) (by decide) (by decide))
    (hright (f := 7) (by decide) (by decide) (by decide))

private def longGapPotentialCap210 : Nat → Nat
  | 11 => 1104
  | 13 => 1045
  | 17 => 1082
  | 19 => 1045
  | 23 => 842
  | 29 => 725
  | 31 => 586
  | _ => 1120

def firstHitReuseCostCap210 (p : Nat) : Nat := 37 * p + 11 + longGapPotentialCap210 p

private def checkLongGapPotential210 (p : Nat) : Bool :=
  longGapHorizons210.all fun c => (List.range 210).all fun r =>
    decide (scaledPotential210 r (c + p - 1) ≤ longGapPotentialCap210 p)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem long_gap_potentials_checked210 (p : Nat) (hp : p ∈ smallReusePrimes210) :
    checkLongGapPotential210 p = true := by
  simp only [smallReusePrimes210, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem long_gap_potential_le210 (r C p : Nat) (hp : p ∈ smallReusePrimes210)
    (hC : C % 210 ∈ longGapHorizons210) (hsize : 1 < p) :
    scaledPotential210 r (C + p - 1) ≤ longGapPotentialCap210 p := by
  have h := long_gap_potentials_checked210 p hp
  have hc := List.all_eq_true.mp h (C % 210) hC
  have hr := List.all_eq_true.mp hc (r % 210) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hb := of_decide_eq_true hr
  change scaledPotential210 (r % 210) (C % 210 + p - 1) ≤ longGapPotentialCap210 p at hb
  unfold scaledPotential210 supportedPotential210 at hb ⊢
  rwa [Nat.mod_mod, show (C % 210 + p - 1) % 210 = (C + p - 1) % 210 by omega] at hb

theorem scaled_net_cost_small_prime_cap210 (event : ResidualPhaseEvent210)
    (hp : d event.hit ∈ smallReusePrimes210) :
    event.scaledNetCost.toNat ≤ firstHitReuseCostCap210 (d event.hit) := by
  let p := d event.hit
  have hsize : 1 < p := event.step.2.2.2.1
  have hgap := moving_horizon_step_gap_le_twice_increment event.step
  have hup := moving_horizon_step_update event.step
  change _ ≤ firstHitReuseCostCap210 p
  by_cases hd : p ∣ 210
  · simp [ResidualPhaseEvent210.scaledNetCost, show d event.hit ∣ 210 from hd]
  · have hraw := event.scaled_net_cost_le_of_unsupported hd
    by_cases hlong : 14 < event.hit - event.start
    · have hr := moving_horizon_long_gap_residue210 event.step hlong
      have hV := long_gap_potential_le210 event.hit event.horizon p hp hr hsize
      have hupdate : event.nextHorizon = event.horizon + p - 1 := by
        change _ = _ + d event.hit - 1
        omega
      rw [← hupdate] at hV
      rw [ResidualPhaseEvent210.scaledNetCost, if_neg (show ¬ d event.hit ∣ 210 from hd)]
      unfold firstHitReuseCostCap210
      change 1 < d event.hit at hsize
      change scaledPotential210 event.hit event.nextHorizon ≤ longGapPotentialCap210 (d event.hit) at hV
      change _ ≤ 37 * d event.hit + 11 + longGapPotentialCap210 (d event.hit)
      change _ ≤ 2 * d event.hit at hgap
      omega
    · have hshort : 336 + 1120 ≤ 48 * p + longGapPotentialCap210 p := by
        have hm : p ∈ smallReusePrimes210 := hp
        simp only [smallReusePrimes210, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h | h | h | h | h | h <;> rw [h] <;> decide
      unfold firstHitReuseCostCap210
      change _ ≤ 37 * d event.hit + 11 + longGapPotentialCap210 (d event.hit)
      change _ ≤ 48 * d event.hit + longGapPotentialCap210 (d event.hit) at hshort
      omega

private def reuseDeficitPairs210 (cap : Nat → Nat) : Finset (Nat × Nat) :=
  (smallReusePrimes210 ×ˢ smallReusePrimes210).filter fun (p, q) =>
    p ≤ q ∧ 420 * q < 3 * (cap p + cap q)

def coarseReuseDeficitPairs210 : Finset (Nat × Nat) := reuseDeficitPairs210 (fun p => 37 * p + 1131)

def firstHitReuseDeficitPairs210 : Finset (Nat × Nat) := reuseDeficitPairs210 firstHitReuseCostCap210

theorem coarse_reuse_deficit_pair_count210 : coarseReuseDeficitPairs210.card = 19 := by decide +kernel

theorem first_hit_reuse_deficit_pair_count210 : firstHitReuseDeficitPairs210.card = 15 := by decide +kernel

private theorem coarse_pair_max_cost210 : ∀ p : coarseReuseDeficitPairs210,
    3 * ((37 * p.val.1 + 1131) + (37 * p.val.2 + 1131)) ≤ 13668 := by decide +kernel

private theorem first_hit_pair_max_cost210 : ∀ p : firstHitReuseDeficitPairs210,
    3 * (firstHitReuseCostCap210 p.val.1 + firstHitReuseCostCap210 p.val.2) ≤ 10554 := by decide +kernel

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

private theorem small_primes_of_two_reuse_deficit {a b c e : Fin n} {lo hi : Nat}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (horder : d (trace.event c).hit ≤ d (trace.event e).hit)
    (inside : trace.growthWindow a c ∪ trace.growthWindow b e ⊆ Finset.Ico lo hi)
    (deficit : 2 * (hi - lo) < 3 * ((trace.event c).scaledNetCost.toNat + (trace.event e).scaledNetCost.toNat)) :
    d (trace.event c).hit ∈ smallReusePrimes210 ∧ d (trace.event e).hit ∈ smallReusePrimes210 ∧
      210 * d (trace.event e).hit ≤ hi - lo := by
  have hcard := Finset.card_le_card inside
  rw [Nat.card_Ico] at hcard
  have hsmall : d (trace.event e).hit < 35 := by
    by_contra h
    have hpaid := trace.two_reuses_scaled_net_cost_two_thirds_of_large p q
      (by rw [max_eq_right horder]; omega)
    omega
  have hc := small_unsupported_prime_cases210 ⟨d (trace.event c).hit, by omega⟩
    (trace.event c).step.2.2.2.1 p.prime p.unsupported
  have he := small_unsupported_prime_cases210 ⟨d (trace.event e).hit, hsmall⟩
    (trace.event e).step.2.2.2.1 q.prime q.unsupported
  have hwidth := (trace.prime_reuse_drift q).2
  have hright := Finset.card_le_card (Finset.subset_union_right (s₁ := trace.growthWindow a c)
    (s₂ := trace.growthWindow b e))
  refine ⟨hc, he, hwidth.trans ?_⟩
  rw [← Nat.card_Ico]
  exact hright.trans hcard

theorem coarse_two_reuse_deficit210 {a b c e : Fin n} {lo hi : Nat}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (horder : d (trace.event c).hit ≤ d (trace.event e).hit)
    (inside : trace.growthWindow a c ∪ trace.growthWindow b e ⊆ Finset.Ico lo hi)
    (deficit : 2 * (hi - lo) < 3 * ((trace.event c).scaledNetCost.toNat + (trace.event e).scaledNetCost.toNat)) :
    (d (trace.event c).hit, d (trace.event e).hit) ∈ coarseReuseDeficitPairs210 ∧ hi - lo ≤ 6833 := by
  obtain ⟨hp, hq, hwidth⟩ := trace.small_primes_of_two_reuse_deficit p q horder inside deficit
  have h₁ := (trace.event c).scaled_net_cost_positive_part_le
  have h₂ := (trace.event e).scaled_net_cost_positive_part_le
  have hmem : (d (trace.event c).hit, d (trace.event e).hit) ∈ coarseReuseDeficitPairs210 :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, horder, by
      change 420 * d (trace.event e).hit <
        3 * ((37 * d (trace.event c).hit + 1131) + (37 * d (trace.event e).hit + 1131))
      omega⟩
  have hcap := coarse_pair_max_cost210 ⟨_, hmem⟩
  change 3 * ((37 * d (trace.event c).hit + 1131) + (37 * d (trace.event e).hit + 1131)) ≤ 13668 at hcap
  exact ⟨hmem, by omega⟩

/-- The actual first-hit condition excludes the pairs involving 29 or
31 and shortens the maximum window that can still be deficient. -/
theorem first_hit_two_reuse_deficit210 {a b c e : Fin n} {lo hi : Nat}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (horder : d (trace.event c).hit ≤ d (trace.event e).hit)
    (inside : trace.growthWindow a c ∪ trace.growthWindow b e ⊆ Finset.Ico lo hi)
    (deficit : 2 * (hi - lo) + 3 * trace.scaledGrowthCredit (Finset.Ico lo hi) <
      3 * ((trace.event c).scaledNetCost.toNat + (trace.event e).scaledNetCost.toNat)) :
    (d (trace.event c).hit, d (trace.event e).hit) ∈ firstHitReuseDeficitPairs210 ∧ hi - lo ≤ 5276 := by
  obtain ⟨hp, hq, hwidth⟩ := trace.small_primes_of_two_reuse_deficit p q horder inside (by omega)
  have h₁ := scaled_net_cost_small_prime_cap210 (trace.event c) hp
  have h₂ := scaled_net_cost_small_prime_cap210 (trace.event e) hq
  have hmem : (d (trace.event c).hit, d (trace.event e).hit) ∈ firstHitReuseDeficitPairs210 :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, horder, by omega⟩
  have hcap := first_hit_pair_max_cost210 ⟨_, hmem⟩
  change 3 * (firstHitReuseCostCap210 (d (trace.event c).hit) +
    firstHitReuseCostCap210 (d (trace.event e).hit)) ≤ 10554 at hcap
  exact ⟨hmem, by omega⟩

end ResidualPhaseTrace210

end A166944Research
