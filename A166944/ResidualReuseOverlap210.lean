import A166944.ResidualNetContributions210
import Mathlib.Order.Interval.Finset.Nat

/-! # Counting the growth shared by two prime reuses -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

structure PrimeReuse (earlier later : Fin n) : Prop where
  ordered : earlier < later
  same_key : (trace.event earlier).phaseKey = (trace.event later).phaseKey
  prime : NoProperFactor (d (trace.event later).hit)
  unsupported : ¬ d (trace.event later).hit ∣ 210

def growthWindow (earlier later : Fin n) : Finset Nat :=
  Finset.Ico (trace.event earlier).horizon (trace.event later).horizon

theorem prime_reuse_drift {i j : Fin n} (reuse : trace.PrimeReuse i j) :
    (210 * d (trace.event j).hit) ∣ (trace.event j).horizon - (trace.event i).horizon ∧
    210 * d (trace.event j).hit ≤ (trace.event j).horizon - (trace.event i).horizon := by
  let w := trace.samePhaseInterval reuse.ordered reuse.same_key
  have hp : NoProperFactor (d w.r) := w.same_increment.symm ▸ reuse.prime
  have hu : ¬ d w.r ∣ 210 := w.same_increment.symm ▸ reuse.unsupported
  have h := unsupported_prime_reuse_drift w hp hu
  rw [w.same_increment] at h
  exact h

theorem crossing_growth_union {a b c e : Fin n} (hab : a < b) (hbc : b < c) (hce : c < e) :
    trace.growthWindow a c ∪ trace.growthWindow b e = trace.growthWindow a e := by
  have h₁ : (trace.event a).horizon < (trace.event b).horizon := trace.horizon_strict_mono hab
  have h₂ : (trace.event b).horizon < (trace.event c).horizon := trace.horizon_strict_mono hbc
  have h₃ : (trace.event c).horizon < (trace.event e).horizon := trace.horizon_strict_mono hce
  ext x
  simp only [growthWindow, Finset.mem_union, Finset.mem_Ico]
  omega

theorem crossing_growth_count {a b c e : Fin n} (hab : a < b) (hbc : b < c) (hce : c < e) :
    (trace.growthWindow a c ∪ trace.growthWindow b e).card =
      (trace.growthWindow a b).card + (trace.growthWindow b c).card + (trace.growthWindow c e).card := by
  have h₁ : (trace.event a).horizon < (trace.event b).horizon := trace.horizon_strict_mono hab
  have h₂ : (trace.event b).horizon < (trace.event c).horizon := trace.horizon_strict_mono hbc
  have h₃ : (trace.event c).horizon < (trace.event e).horizon := trace.horizon_strict_mono hce
  rw [trace.crossing_growth_union hab hbc hce]
  simp only [growthWindow, Nat.card_Ico]
  omega

private theorem left_width_le_union (a b c e : Fin n) :
    (trace.event c).horizon - (trace.event a).horizon ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  calc
    _ = (trace.growthWindow a c).card := (Nat.card_Ico _ _).symm
    _ ≤ _ := Finset.card_le_card Finset.subset_union_left

/-- Both costs fit in the union when the larger increment is at least 86.
This uses one full period of that increment, even if the other window
overlaps it or is contained in it. -/
theorem two_reuses_net_cost_of_large {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hlarge : 86 ≤ max (d (trace.event c).hit) (d (trace.event e).hit)) :
    2 * ((trace.event c).netCost.toNat + (trace.event e).netCost.toNat) ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  have hp := (trace.prime_reuse_drift p).2
  have hq := (trace.prime_reuse_drift q).2
  have hleft := trace.left_width_le_union a b c e
  have hright : (trace.event e).horizon - (trace.event b).horizon ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
    rw [Finset.union_comm]
    exact trace.left_width_le_union b a e c
  rcases le_total (d (trace.event c).hit) (d (trace.event e).hit) with h | h
  · rw [max_eq_right h] at hlarge
    have hcost := (trace.event c).two_net_costs_le_prime_period (trace.event e) h hlarge
    omega
  · rw [max_eq_left h] at hlarge
    have hcost := (trace.event e).two_net_costs_le_prime_period (trace.event c) h hlarge
    omega

theorem prime_reuse_net_cost_two_thirds {i j : Fin n} (reuse : trace.PrimeReuse i j)
    (hsize : 13 ≤ d (trace.event j).hit) :
    3 * (trace.event j).netCost.toNat ≤ 2 * (trace.growthWindow i j).card := by
  have hwidth := (trace.prime_reuse_drift reuse).2
  have hcost := (trace.event j).net_cost_positive_part_le
  simp only [growthWindow, Nat.card_Ico]
  omega

theorem two_reuses_net_cost_two_thirds_of_large {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hlarge : 41 ≤ max (d (trace.event c).hit) (d (trace.event e).hit)) :
    3 * ((trace.event c).netCost.toNat + (trace.event e).netCost.toNat) ≤
      2 * (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  have hp := (trace.prime_reuse_drift p).2
  have hq := (trace.prime_reuse_drift q).2
  have hcost₁ := (trace.event c).net_cost_positive_part_le
  have hcost₂ := (trace.event e).net_cost_positive_part_le
  have hleft := trace.left_width_le_union a b c e
  have hright : (trace.event e).horizon - (trace.event b).horizon ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
    rw [Finset.union_comm]
    exact trace.left_width_le_union b a e c
  rcases le_total (d (trace.event c).hit) (d (trace.event e).hit) with h | h
  · rw [max_eq_right h] at hlarge
    omega
  · rw [max_eq_left h] at hlarge
    omega

private theorem distinct_prime_coprime {p q : Nat} (hp : 1 < p) (hq : 1 < q)
    (hprime : NoProperFactor p) (hprime' : NoProperFactor q) (hne : p ≠ q) : Nat.Coprime p q := by
  let g := Nat.gcd p q
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgp : g ∣ p := Nat.gcd_dvd_left _ _
  have hgq : g ∣ q := Nat.gcd_dvd_right _ _
  have hle := Nat.le_of_dvd (by omega : 0 < p) hgp
  have hle' := Nat.le_of_dvd (by omega : 0 < q) hgq
  change g = 1
  by_contra h
  have hbig : 1 < g := by omega
  have hgp' : g = p := by
    by_contra hne'
    exact hprime ⟨g, lt_of_le_of_ne hle hne'⟩ hbig hgp
  have hgq' : g = q := by
    by_contra hne'
    exact hprime' ⟨g, lt_of_le_of_ne hle' hne'⟩ hbig hgq
  exact hne (hgp'.symm.trans hgq')

private theorem product_period_dvd {p q width : Nat} (hcop : Nat.Coprime p q)
    (hp : 210 * p ∣ width) (hq : 210 * q ∣ width) : 210 * p * q ∣ width := by
  obtain ⟨k, hk⟩ := (show 210 ∣ 210 * p from ⟨p, rfl⟩).trans hp
  rw [hk] at hp hq
  have hd := hcop.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 210) hp)
    (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 210) hq)
  obtain ⟨l, hl⟩ := hd
  exact ⟨l, by rw [hk, hl]; ac_rfl⟩

theorem distinct_prime_common_drift {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hne : d (trace.event c).hit ≠ d (trace.event e).hit)
    (sameDrift : (trace.event c).horizon - (trace.event a).horizon =
      (trace.event e).horizon - (trace.event b).horizon) :
    (210 * d (trace.event c).hit * d (trace.event e).hit) ∣
      (trace.event c).horizon - (trace.event a).horizon := by
  have hp := trace.prime_reuse_drift p
  have hq := trace.prime_reuse_drift q
  have hcop := distinct_prime_coprime (trace.event c).step.2.2.2.1
    (trace.event e).step.2.2.2.1 p.prime q.prime hne
  exact product_period_dvd hcop hp.1 (sameDrift.symm ▸ hq.1)

private theorem unsupported_increment_ge_nine (event : ResidualPhaseEvent210)
    (hu : ¬ d event.hit ∣ 210) : 9 ≤ d event.hit := by
  have hstep := event.step.2.2.2.1
  have hr : 3 ≤ event.hit := by have := event.step.1.1; have := event.step.2.1; omega
  have hodd := d_mod_two_eq_one_of_three_le hr
  by_contra h
  have hcases : d event.hit = 3 ∨ d event.hit = 5 ∨ d event.hit = 7 := by omega
  apply hu
  rcases hcases with h₁ | h₂ | h₃
  · rw [h₁]; decide
  · rw [h₂]; decide
  · rw [h₃]; decide

theorem distinct_prime_common_drift_pays {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hne : d (trace.event c).hit ≠ d (trace.event e).hit)
    (sameDrift : (trace.event c).horizon - (trace.event a).horizon =
      (trace.event e).horizon - (trace.event b).horizon) :
    2 * ((trace.event c).netCost.toNat + (trace.event e).netCost.toNat) ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  let f := d (trace.event c).hit
  let g := d (trace.event e).hit
  have hf : 9 ≤ f := unsupported_increment_ge_nine (trace.event c) p.unsupported
  have hg : 9 ≤ g := unsupported_increment_ge_nine (trace.event e) q.unsupported
  have hp := trace.prime_reuse_drift p
  have hwidth : 210 * f * g ≤ (trace.event c).horizon - (trace.event a).horizon :=
    Nat.le_of_dvd (by omega) (trace.distinct_prime_common_drift p q hne sameDrift)
  have hleft := trace.left_width_le_union a b c e
  have hfcost : (trace.event c).netCost.toNat ≤ 37 * f + 1326 := (trace.event c).net_cost_positive_part_le
  have hgcost : (trace.event e).netCost.toNat ≤ 37 * g + 1326 := (trace.event e).net_cost_positive_part_le
  have hprod₁ : 9 * f ≤ f * g := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left f hg
  have hprod₂ : 9 * g ≤ f * g := Nat.mul_le_mul_right g hf
  rw [Nat.mul_assoc] at hwidth
  omega

/-- The common period of two distinct primes can also pay additional
events, provided their count and increments fit this bound. -/
theorem common_drift_net_cost_of_card_bound {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e)
    (hne : d (trace.event c).hit ≠ d (trace.event e).hit)
    (sameDrift : (trace.event c).horizon - (trace.event a).horizon =
      (trace.event e).horizon - (trace.event b).horizon)
    (selected : Finset (Fin n))
    (hsize : ∀ i ∈ selected, d (trace.event i).hit ≤ max (d (trace.event c).hit) (d (trace.event e).hit))
    (hcount : 2 * selected.card ≤ min (d (trace.event c).hit) (d (trace.event e).hit)) :
    2 * (∑ i ∈ selected, (trace.event i).netCost.toNat) ≤
      (trace.growthWindow a c ∪ trace.growthWindow b e).card := by
  let f := d (trace.event c).hit
  let g := d (trace.event e).hit
  have hf : 9 ≤ f := unsupported_increment_ge_nine (trace.event c) p.unsupported
  have hpeak : 9 ≤ max f g := hf.trans (le_max_left _ _)
  have hfirst := (trace.prime_reuse_drift p).2
  have hwidth : 210 * f * g ≤ (trace.event c).horizon - (trace.event a).horizon :=
    Nat.le_of_dvd (by omega) (trace.distinct_prime_common_drift p q hne sameDrift)
  have hsum : (∑ i ∈ selected, (trace.event i).netCost.toNat) ≤ selected.card * (210 * max f g) := by
    calc
      _ ≤ ∑ _i ∈ selected, 210 * max f g := Finset.sum_le_sum fun i hi => by
        have h := (trace.event i).net_cost_positive_part_le
        have hmax : d (trace.event i).hit ≤ max f g := hsize i hi
        omega
      _ = _ := by simp
  have hmul := Nat.mul_le_mul_left 2 hsum
  rw [← Nat.mul_assoc] at hmul
  have hscaled := Nat.mul_le_mul_right (210 * max f g) hcount
  have heq : min f g * (210 * max f g) = 210 * f * g := by
    rcases le_total f g with h | h
    · rw [min_eq_left h, max_eq_right h]
      ac_rfl
    · rw [min_eq_right h, max_eq_left h]
      ac_rfl
  rw [heq] at hscaled
  exact hmul.trans (hscaled.trans (hwidth.trans (trace.left_width_le_union a b c e)))

/-- For two interlaced reuses, the difference between their widths is
the difference between the flanks. Widths are multiples of 210. -/
theorem crossing_same_drift_of_close_flanks {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e) (hbc : b < c)
    (hl : (trace.event b).horizon - (trace.event a).horizon <
      (trace.event e).horizon - (trace.event c).horizon + 210)
    (hr : (trace.event e).horizon - (trace.event c).horizon <
      (trace.event b).horizon - (trace.event a).horizon + 210)
    (hab : a < b) (hce : c < e) :
    (trace.event c).horizon - (trace.event a).horizon =
      (trace.event e).horizon - (trace.event b).horizon := by
  have h₁ : (trace.event a).horizon < (trace.event b).horizon := trace.horizon_strict_mono hab
  have h₂ : (trace.event b).horizon < (trace.event c).horizon := trace.horizon_strict_mono hbc
  have h₃ : (trace.event c).horizon < (trace.event e).horizon := trace.horizon_strict_mono hce
  obtain ⟨x, hx⟩ := (show 210 ∣ 210 * d (trace.event c).hit from ⟨_, rfl⟩).trans
    (trace.prime_reuse_drift p).1
  obtain ⟨y, hy⟩ := (show 210 ∣ 210 * d (trace.event e).hit from ⟨_, rfl⟩).trans
    (trace.prime_reuse_drift q).1
  omega

theorem crossing_same_drift_of_consecutive_flanks {a b c e : Fin n}
    (p : trace.PrimeReuse a c) (q : trace.PrimeReuse b e) (hbc : b < c)
    (hab : b.val = a.val + 1) (hce : e.val = c.val + 1) :
    (trace.event c).horizon - (trace.event a).horizon =
      (trace.event e).horizon - (trace.event b).horizon := by
  have h₁ := trace.consecutive_horizon hab
  have h₂ := trace.consecutive_horizon hce
  rw [moving_horizon_step_update (trace.event a).step] at h₁
  rw [moving_horizon_step_update (trace.event c).step] at h₂
  have hs := congrArg Prod.fst p.same_key
  change d (trace.event a).hit = d (trace.event c).hit at hs
  apply trace.crossing_same_drift_of_close_flanks p q hbc
  · omega
  · omega
  · omega
  · omega

end A166944Research.ResidualPhaseTrace210
