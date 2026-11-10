import A166944.RecordIndex

/-!
# The last events at a large horizon crossing

A first hit comparable to the horizon has a fixed position and horizon.
The first-hit condition and the exact backward gcd equations constrain
the preceding events.
-/

namespace A166944Research

private theorem eq_three_mul_of_odd_dvd {e n : Nat}
    (he : e % 2 = 1) (hn : n % 2 = 1) (hdiv : e ∣ n)
    (hlo : 3 * e ≤ n) (hhi : n < 5 * e) : n = 3 * e := by
  obtain ⟨q, hq⟩ := hdiv
  have hqodd : q % 2 = 1 := by simpa only [hq, Nat.mul_mod, he, Nat.one_mul, Nat.mod_mod] using hn
  have hqlo : 3 ≤ q := by
    by_cases h : 3 ≤ q
    · exact h
    · have hlt := Nat.mul_lt_mul_of_pos_left (by omega : q < 3) (by omega : 0 < e)
      rw [← hq, Nat.mul_comm e 3] at hlt
      omega
  have hqhi : q < 5 := by
    apply Nat.lt_of_mul_lt_mul_left (a := e)
    simpa only [← hq, Nat.mul_comm e 5] using hhi
  have : q = 3 := by omega
  simpa [this, Nat.mul_comm] using hq

/-- A first hit after `e+2` with `C+1 < 5*e` has horizon `3*e+1`
and occurs at `2*e`. -/
theorem moving_horizon_large_old_event_shape {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C') (he : d r = e)
    (hstart : e + 2 ≤ s) (hlarge : C + 1 < 5 * e) :
    r = 2 * e ∧ C = 3 * e + 1 ∧ C' = 4 * e := by
  have hsr := hstep.2.1
  have hrC := hstep.2.2.1
  have hCpar : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hepar : e % 2 = 1 := he ▸ d_mod_two_eq_one_of_three_le (by have := hstep.1.1; omega)
  have he3 : 3 ≤ e := he ▸ moving_horizon_step_event_ge_three hstep
  have hupdate := moving_horizon_step_update hstep
  rw [he] at hupdate
  rcases moving_horizon_step_event_package hstep with ⟨hr, hdiv, _, hlo⟩ | ⟨hr, hdiv, _, hlo⟩
  · rw [he] at hdiv hlo
    have hC₀ := eq_three_mul_of_odd_dvd hepar (by omega : (C - 1) % 2 = 1)
      hdiv hlo (by omega)
    have hC : C = 3 * e + 1 := by omega
    obtain ⟨q, hq⟩ := (moving_horizon_event_divisibility_even hstep he hr).1
    have hqeven : q % 2 = 0 := by
      simpa only [hq, Nat.mul_mod, hepar, Nat.one_mul, Nat.mod_mod] using hr
    have hqhi : q < 4 := by
      apply Nat.lt_of_mul_lt_mul_left (a := e)
      rw [← hq, Nat.mul_comm e 4]
      omega
    have hqpos : 0 < q := by
      by_cases hz : q = 0
      · simp [hz] at hq
        omega
      · omega
    have hqtwo : q = 2 := by omega
    exact ⟨by simpa [hqtwo, Nat.mul_comm] using hq, hC, by omega⟩
  · rw [he] at hdiv hlo
    have hC := eq_three_mul_of_odd_dvd hepar (by omega : (C + 1) % 2 = 1)
      hdiv hlo hlarge
    obtain ⟨q, hq⟩ := (moving_horizon_event_divisibility_odd hstep he hr).1
    have hqodd : q % 2 = 1 := by
      have h : (r - 2) % 2 = 1 := by omega
      simpa only [hq, Nat.mul_mod, hepar, Nat.one_mul, Nat.mod_mod] using h
    have hqhi : q < 3 := by
      apply Nat.lt_of_mul_lt_mul_left (a := e)
      rw [← hq, Nat.mul_comm e 3]
      omega
    have hqone : q = 1 := by omega
    simp only [hqone, Nat.mul_one] at hq
    omega

/-- The six possibilities from the gap and the preceding event's divisibility. -/
abbrev LargeOldEventPredecessor (t f : Nat) : Prop :=
  (t = 1 ∧ (f = 3 ∨ f = 5 ∨ f = 15)) ∨ (t = 3 ∧ f = 7) ∨
    (t = 4 ∧ f = 7) ∨ (t = 6 ∧ f = 5)

private theorem large_old_event_predecessor_finite :
    ∀ (u : Fin 3) (t : Fin 7) (f : Fin 28),
      1 ≤ t.val → 3 ≤ f.val → f.val % 2 = 1 →
      (u.val = 1 → t.val ≤ 2) → (u.val = 2 → t.val ≤ 4) →
      (t.val % 2 = 0 → f.val ∣ 3 * t.val + 2) →
      (t.val % 2 = 1 → f.val ∣ 3 * t.val + 12) →
      (t.val % 2 = 1 → f.val % 3 = 0 → (2 * u.val) % 3 = (t.val + 2) % 3) →
      LargeOldEventPredecessor t.val f.val := by decide

private theorem large_old_event_gap_mod_three {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hr : r = 2 * e) (hC : C = 3 * e + 1) :
    r - s ≤ 6 ∧ (e % 3 = 1 → r - s ≤ 2) ∧ (e % 3 = 2 → r - s ≤ 4) := by
  let t := r - s
  have hdiv : 3 ∣ C - 1 := ⟨e, by omega⟩
  have ht6 : t ≤ 6 := moving_horizon_gap_le_twice_even_factor hstep (by decide) hdiv
  have hsmall (k : Nat) (hkpos : 0 < k) (hkeven : k % 2 = 0) (hkdiv : 3 ∣ r - k) : t ≤ k := by
    by_cases ht : t ≤ k
    · exact ht
    · have hsj : s < r - k := by omega
      have hjr : r - k < r := by omega
      have hpar : (r - k) % 2 = 0 := by omega
      have hunit : Nat.gcd (r - k) (C - 1) = 1 := by
        rcases moving_horizon_first_hit_map hstep with h | h
        · exact (h.2.2.2 (r - k) hsj hjr).1 hpar
        · omega
      have hone := Nat.dvd_gcd hkdiv hdiv
      rw [hunit] at hone
      exact False.elim ((by decide : ¬ 3 ∣ 1) hone)
  have ht2 (h : e % 3 = 1) : t ≤ 2 := by
    apply hsmall 2 (by decide) (by decide)
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have ht4 (h : e % 3 = 2) : t ≤ 4 := by
    apply hsmall 4 (by decide) (by decide)
    exact Nat.dvd_of_mod_eq_zero (by omega)
  exact ⟨ht6, ht2, ht4⟩

/-- The endpoint determines the two numbers whose common divisors are
possible increments. The gcd with the increment subtracted tests the
exact preceding transition, including a unit increment. -/
theorem D_backward_gcd {n : Nat} (hn : 3 ≤ n) :
    let u := if n % 2 = 0 then n else n - 2
    let v := if n % 2 = 0 then D n else D n + 2
    d n ∣ u ∧ d n ∣ v ∧ Nat.gcd u (v - d n) = d n ∧
      D (n - 1) + d n = D n + 1 := by
  have hD := D_succ_add_one_eq_add_d (n - 1)
  rw [show n - 1 + 1 = n by omega] at hD
  have hDlo : 2 ≤ D (n - 1) :=
    Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le (by omega))
  have hmap := constant_D_event_map (by omega : 2 ≤ n) (rfl : D (n - 1) = D (n - 1))
  dsimp
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_pos] at hmap ⊢
    have hsub : D n - d n = D (n - 1) - 1 := by omega
    have hdiv : d n ∣ D n - d n := hsub.symm ▸ hmap.symm ▸ Nat.gcd_dvd_right _ _
    refine ⟨hmap.symm ▸ Nat.gcd_dvd_left _ _, ?_, by rw [hsub, ← hmap], hD.symm⟩
    rw [show D n = (D n - d n) + d n by omega]
    exact Nat.dvd_add hdiv (Nat.dvd_refl _)
  · simp only [hpar, if_false] at hmap ⊢
    have hsub : D n + 2 - d n = D (n - 1) + 1 := by omega
    have hdiv : d n ∣ D n + 2 - d n := hsub.symm ▸ hmap.symm ▸ Nat.gcd_dvd_right _ _
    refine ⟨hmap.symm ▸ Nat.gcd_dvd_left _ _, ?_, by rw [hsub, ← hmap], hD.symm⟩
    rw [show D n + 2 = (D n + 2 - d n) + d n by omega]
    exact Nat.dvd_add hdiv (Nat.dvd_refl _)

private theorem D_endpoint_divisibility {s C : Nat} (hs : 3 ≤ s) (hC : D s = C) :
    (s % 2 = 0 ∧ d s ∣ s ∧ d s ∣ C) ∨
      (s % 2 = 1 ∧ d s ∣ s - 2 ∧ d s ∣ C + 2) := by
  have hb := D_backward_gcd hs
  dsimp at hb
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · simp only [h, if_pos, hC] at hb
    exact Or.inl ⟨h, hb.1, hb.2.1⟩
  · simp only [h, Nat.one_ne_zero, if_false, hC] at hb
    exact Or.inr ⟨h, hb.1, hb.2.1⟩

private theorem large_old_event_predecessor_of_nonunit {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hs3 : 3 ≤ s) (hf3 : 3 ≤ d s)
    (hr : r = 2 * e) (hC : C = 3 * e + 1) :
    LargeOldEventPredecessor (r - s) (d s) := by
  let t := r - s
  let f := d s
  have hsr := hstep.2.1
  have htpos : 1 ≤ t := by omega
  have hfodd : f % 2 = 1 := d_mod_two_eq_one_of_three_le hs3
  obtain ⟨ht6, ht2, ht4⟩ := large_old_event_gap_mod_three hstep hr hC
  have hanchor := D_endpoint_divisibility hs3 hstep.1.2.1
  change (s % 2 = 0 ∧ f ∣ s ∧ f ∣ C) ∨ (s % 2 = 1 ∧ f ∣ s - 2 ∧ f ∣ C + 2) at hanchor
  have hdivEven (ht : t % 2 = 0) : f ∣ 3 * t + 2 := by
    rcases hanchor with ⟨_, hfs, hfC⟩ | ⟨hs, _, _⟩
    · have h := Nat.dvd_sub (Nat.dvd_trans hfC (Nat.dvd_mul_left C 2))
        (Nat.dvd_trans hfs (Nat.dvd_mul_left s 3))
      rwa [show 2 * C - 3 * s = 3 * t + 2 by omega] at h
    · omega
  have hdivOdd (ht : t % 2 = 1) : f ∣ 3 * t + 12 := by
    rcases hanchor with ⟨hs, _, _⟩ | ⟨_, hfs, hfC⟩
    · omega
    · have h := Nat.dvd_sub (Nat.dvd_trans hfC (Nat.dvd_mul_left (C + 2) 2))
        (Nat.dvd_trans hfs (Nat.dvd_mul_left (s - 2) 3))
      rwa [show 2 * (C + 2) - 3 * (s - 2) = 3 * t + 12 by omega] at h
  have hmodOdd (ht : t % 2 = 1) (hf : f % 3 = 0) :
      (2 * (e % 3)) % 3 = (t + 2) % 3 := by
    rcases hanchor with ⟨hs, _, _⟩ | ⟨_, hfs, _⟩
    · omega
    · have h := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hf) hfs)
      omega
  have hf28 : f < 28 := by
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have hle := Nat.le_of_dvd (by omega : 0 < 3 * t + 2) (hdivEven h)
      omega
    · have hle := Nat.le_of_dvd (by omega : 0 < 3 * t + 12) (hdivOdd h)
      omega
  exact large_old_event_predecessor_finite ⟨e % 3, Nat.mod_lt _ (by decide)⟩
    ⟨t, by omega⟩ ⟨f, hf28⟩ htpos hf3 hfodd ht2 ht4 hdivEven hdivOdd hmodOdd

theorem moving_horizon_large_old_event_predecessor {sp Cp s C r C' e : Nat}
    (hprev : IsMovingHorizonStep sp Cp s C) (hstep : IsMovingHorizonStep s C r C')
    (hr : r = 2 * e) (hC : C = 3 * e + 1) :
    LargeOldEventPredecessor (r - s) (d s) :=
  large_old_event_predecessor_of_nonunit hstep (by have := hprev.1.1; have := hprev.2.1; omega)
    (moving_horizon_step_event_ge_three hprev) hr hC

/-- In the one-index gap with preceding increment 5, the earlier horizon
is `3*(e-1)` at index `2*(e-1)`. Every odd divisor of `e-1` is a possible
increment for the local inverse gcd equation at that state. -/
theorem large_old_event_predecessor_five_resonance {e f : Nat}
    (he : 3 ≤ e) (heodd : e % 2 = 1) (hfodd : f % 2 = 1) (hdiv : f ∣ e - 1) :
    Nat.gcd (2 * (e - 1)) (3 * (e - 1) - f) = f := by
  obtain ⟨q, hq⟩ := hdiv
  have hqeven : q % 2 = 0 := by
    rw [quotient_mod_two_of_left_odd hfodd, ← hq]
    omega
  have hqpos : 0 < q := by
    by_cases h : q = 0
    · simp [h] at hq
      omega
    · omega
  let g := Nat.gcd (2 * q) (3 * q - 1)
  have h₁ : g ∣ 2 * q := Nat.gcd_dvd_left _ _
  have h₂ : g ∣ 3 * q - 1 := Nat.gcd_dvd_right _ _
  have hdiff := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd h₁ 3) (Nat.dvd_mul_left_of_dvd h₂ 2)
  have hg₂ : g ∣ 2 := by rwa [show 3 * (2 * q) - 2 * (3 * q - 1) = 2 by omega] at hdiff
  have hg₁ : g = 1 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hg₂
    have hpos := Nat.gcd_pos_of_pos_left (3 * q - 1) (by omega : 0 < 2 * q)
    by_cases h : g = 1
    · exact h
    · have htwo : g = 2 := by change 0 < g at hpos; omega
      rw [htwo] at h₂
      have hpar := Nat.mod_eq_zero_of_dvd h₂
      omega
  have hleft : 2 * (e - 1) = f * (2 * q) := by rw [hq]; ac_rfl
  have hright : 3 * (e - 1) - f = f * (3 * q - 1) := by
    rw [hq, Nat.mul_sub, Nat.mul_one]
    congr 1
    ac_rfl
  rw [hleft, hright, Nat.gcd_mul_left]
  change f * g = f
  simp [hg₁]

private theorem no_seven_before_large_old_event {e s : Nat}
    (he : 10 ≤ e) (hC : D s = 3 * e + 1) (hf : d s = 7)
    (hs : s = 2 * e - 3 ∨ s = 2 * e - 4) : False := by
  have hcommon : Nat.gcd (2 * e - 4) (3 * e - 6) = e - 2 := by
    rw [show 2 * e - 4 = (e - 2) * 2 by omega,
      show 3 * e - 6 = (e - 2) * 3 by omega, Nat.gcd_mul_left]
    simp [show Nat.gcd 2 3 = 1 by decide]
  have hs3 : 3 ≤ s := by omega
  have hstep := D_backward_gcd hs3
  dsimp at hstep
  rcases hs with hs | hs
  · let n := 2 * e - 4
    have hn3 : 3 ≤ n := by omega
    have hnpar : n % 2 = 0 := by omega
    have hDn : D n = 3 * e - 5 := by
      have hD := hstep.2.2.2
      rw [hf, hC, show s - 1 = n by omega] at hD
      omega
    have hb := D_backward_gcd hn3
    simp only [hnpar, if_pos] at hb
    have hdiv := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hb.2.1 2)
      (Nat.dvd_mul_left_of_dvd hb.1 3)
    have hdiv2 : d n ∣ 2 := by
      rwa [show 2 * D n - 3 * n = 2 by omega] at hdiv
    have hunit : d n = 1 := by
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv2
      have hodd := d_mod_two_eq_one_of_three_le hn3
      omega
    have hgcd := hb.2.2.1
    rw [hDn, hunit, show 3 * e - 5 - 1 = 3 * e - 6 by omega] at hgcd
    change Nat.gcd (2 * e - 4) (3 * e - 6) = 1 at hgcd
    omega
  · have hspar : s % 2 = 0 := by omega
    simp only [hspar, if_pos] at hstep
    have hgcd := hstep.2.2.1
    rw [hC, hf, hs, show 3 * e + 1 - 7 = 3 * e - 6 by omega] at hgcd
    omega

private def backwardOffsetWidth (k δ : Nat) : Nat :=
  let K := 3 * k + 2 + 10 * (k % 2)
  (K - 2 * δ) + (2 * δ - K)

private theorem backward_offset {e k δ : Nat} (hn : k + 3 ≤ 2 * e)
    (hD : D (2 * e - k) + δ = 3 * e + 1) :
    let n := 2 * e - k
    let f := d n
    let u := n - 2 * (k % 2)
    f % 2 = 1 ∧ f ∣ u ∧ f ∣ backwardOffsetWidth k δ ∧
      (u % 3 = 0 → (3 * e + 1 + 2 * (k % 2)) % 3 = (δ + f) % 3 → f % 3 = 0) ∧
      D (2 * e - (k + 1)) + (δ + f - 1) = 3 * e + 1 := by
  let n := 2 * e - k
  let f := d n
  let u := n - 2 * (k % 2)
  let v := D n + 2 * (k % 2)
  let K := 3 * k + 2 + 10 * (k % 2)
  change D n + δ = 3 * e + 1 at hD
  have hn3 : 3 ≤ n := by omega
  have hback := D_backward_gcd hn3
  have hexact : f ∣ u ∧ f ∣ v ∧ Nat.gcd u (v - f) = f ∧
      D (n - 1) + f = D n + 1 := by
    have hpar : n % 2 = k % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · simpa [hpar, h, f, u, v] using hback
    · simpa [hpar, h, f, u, v] using hback
  obtain ⟨hfu, hfv, hgcd, hprev⟩ := hexact
  have hDpos : 2 ≤ D (n - 1) :=
    Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le (by omega))
  have hfle : f ≤ v := by omega
  have hfone : 1 ≤ f := one_le_d_of_two_le (by omega)
  have hrel : 2 * v + 2 * δ = 3 * u + K := by omega
  have hdiv : f ∣ backwardOffsetWidth k δ := by
    have h1 := Nat.dvd_mul_left_of_dvd hfv 2
    have h2 := Nat.dvd_mul_left_of_dvd hfu 3
    have hplus := Nat.dvd_sub h1 h2
    have hminus := Nat.dvd_sub h2 h1
    rw [show 2 * v - 3 * u = K - 2 * δ by omega] at hplus
    rw [show 3 * u - 2 * v = 2 * δ - K by omega] at hminus
    exact Nat.dvd_add hplus hminus
  refine ⟨d_mod_two_eq_one_of_three_le hn3, hfu, hdiv, ?_, ?_⟩
  · intro hu hv
    change (3 * e + 1 + 2 * (k % 2)) % 3 = (δ + f) % 3 at hv
    have hsub : (v - f) % 3 = 0 := by omega
    have hdvd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hsub)
    rw [hgcd] at hdvd
    exact Nat.mod_eq_zero_of_dvd hdvd
  · change D (2 * e - (k + 1)) + (δ + f - 1) = 3 * e + 1
    rw [show 2 * e - (k + 1) = n - 1 by omega]
    omega

/-- Candidate offsets for the finite backward window with preceding
increment 15. At index `2*e-k` an offset `δ` means `D = 3*e+1-δ`. -/
private def fifteenOffsets : Nat → List Nat
  | 2 => [14]
  | 3 => [14]
  | 4 => [14, 20]
  | 5 => [14, 20, 32]
  | 6 => [14, 20, 32, 68]
  | 7 => [14, 20, 32, 68]
  | _ => []

private theorem fifteen_offset_bounds : ∀ (k : Fin 8) (δ : Fin 69),
    δ.val ∈ fifteenOffsets k.val →
      δ.val % 3 = 2 ∧ 0 < backwardOffsetWidth k.val δ.val ∧
        backwardOffsetWidth k.val δ.val < 117 := by decide

set_option maxRecDepth 4096 in
private theorem fifteen_offset_check : ∀ (k : Fin 8) (δ : Fin 69),
    δ.val ∈ fifteenOffsets k.val → ∀ f : Fin 117,
      f.val % 2 = 1 → f.val ∣ backwardOffsetWidth k.val δ.val →
      (k.val = 2 ∨ k.val = 7 → f.val ≠ 5) →
      (k.val = 6 → f.val % 3 ≠ 2) → (k.val = 7 → f.val % 3 ≠ 1) →
      δ.val + f.val - 1 ∈ fifteenOffsets (k.val + 1) := by decide

private theorem fifteen_offset_step {e k δ : Nat} (he : 20 ≤ e)
    (he3 : e % 3 = 0) (he5 : e % 5 = 4) (hk : k < 8)
    (hδ : δ ∈ fifteenOffsets k) (hD : D (2 * e - k) + δ = 3 * e + 1) :
    ∃ δ', δ' ∈ fifteenOffsets (k + 1) ∧ D (2 * e - (k + 1)) + δ' = 3 * e + 1 := by
  let f := d (2 * e - k)
  obtain ⟨hfodd, hfu, hdiv, hmod, hDnext⟩ := backward_offset (by omega) hD
  change f % 2 = 1 at hfodd
  change f ∣ 2 * e - k - 2 * (k % 2) at hfu
  have hδbound : δ < 69 := by
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> simp [h, fifteenOffsets] at hδ <;> omega
  obtain ⟨hδmod, hwpos, hwbound⟩ := fifteen_offset_bounds ⟨k, hk⟩ ⟨δ, hδbound⟩ hδ
  change δ % 3 = 2 at hδmod
  have hfbound : f < 117 := by
    have hle := Nat.le_of_dvd hwpos hdiv
    exact Nat.lt_of_le_of_lt hle hwbound
  have hf5 (h : k = 2 ∨ k = 7) : f ≠ 5 := by
    intro hf
    rw [hf] at hfu
    have hmod5 := Nat.mod_eq_zero_of_dvd hfu
    rcases h with rfl | rfl <;> omega
  have hf6 (h : k = 6) : f % 3 ≠ 2 := by
    intro hf
    change f % 3 = 2 at hf
    have hz := hmod (by omega) (by change (3 * e + 1 + 2 * (k % 2)) % 3 = (δ + f) % 3; omega)
    change f % 3 = 0 at hz
    omega
  have hf7 (h : k = 7) : f % 3 ≠ 1 := by
    intro hf
    change f % 3 = 1 at hf
    have hz := hmod (by omega) (by change (3 * e + 1 + 2 * (k % 2)) % 3 = (δ + f) % 3; omega)
    change f % 3 = 0 at hz
    omega
  exact ⟨δ + f - 1,
    fifteen_offset_check ⟨k, hk⟩ ⟨δ, hδbound⟩ hδ ⟨f, hfbound⟩ hfodd hdiv hf5 hf6 hf7,
    hDnext⟩

private theorem no_fifteen_before_large_old_event {e : Nat} (he : 20 ≤ e)
    (hC : D (2 * e - 1) = 3 * e + 1) (hf : d (2 * e - 1) = 15) : False := by
  have hb := D_backward_gcd (by omega : 3 ≤ 2 * e - 1)
  simp only [show (2 * e - 1) % 2 ≠ 0 by omega, if_false, hf, hC] at hb
  have hd3 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (by decide : 3 ∣ 15) hb.1)
  have hd5 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (by decide : 5 ∣ 15) hb.1)
  have he3 : e % 3 = 0 := by omega
  have he5 : e % 5 = 4 := by omega
  have hD2 : D (2 * e - 2) + 14 = 3 * e + 1 := by
    have hD := hb.2.2.2
    rw [show 2 * e - 1 - 1 = 2 * e - 2 by omega] at hD
    omega
  obtain ⟨δ3, hδ3, hD3⟩ := fifteen_offset_step (k := 2) he he3 he5 (by decide) (by decide) hD2
  obtain ⟨δ4, hδ4, hD4⟩ := fifteen_offset_step (k := 3) he he3 he5 (by decide) hδ3 hD3
  obtain ⟨δ5, hδ5, hD5⟩ := fifteen_offset_step (k := 4) he he3 he5 (by decide) hδ4 hD4
  obtain ⟨δ6, hδ6, hD6⟩ := fifteen_offset_step (k := 5) he he3 he5 (by decide) hδ5 hD5
  obtain ⟨δ7, hδ7, hD7⟩ := fifteen_offset_step (k := 6) he he3 he5 (by decide) hδ6 hD6
  obtain ⟨δ8, hδ8, _⟩ := fifteen_offset_step (k := 7) he he3 he5 (by decide) hδ7 hD7
  simp [fifteenOffsets] at hδ8

/-- The surviving gap-increment pairs and the corresponding residues
of the large increment. -/
abbrev LargeOldEventRemaining (e t f : Nat) : Prop :=
  (t = 1 ∧ f = 3 ∧ e % 3 = 0) ∨ (t = 1 ∧ f = 5 ∧ e % 5 = 4) ∨
    (t = 6 ∧ f = 5 ∧ e % 3 = 0 ∧ e % 5 = 3)

private theorem large_old_event_remaining_of_nonunit {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hs3 : 3 ≤ s) (hf3 : 3 ≤ d s)
    (he : 20 ≤ e) (hr : r = 2 * e) (hC : C = 3 * e + 1) :
    LargeOldEventRemaining e (r - s) (d s) := by
  have hsr := hstep.2.1
  have hDs : D s = 3 * e + 1 := hstep.1.2.1.trans hC
  have hanchor := D_endpoint_divisibility hs3 hstep.1.2.1
  rcases large_old_event_predecessor_of_nonunit hstep hs3 hf3 hr hC with
    ⟨ht, hf | hf | hf⟩ | ⟨ht, hf⟩ | ⟨ht, hf⟩ | ⟨ht, hf⟩
  · refine Or.inl ⟨ht, hf, ?_⟩
    rcases hanchor with ⟨hs, _, _⟩ | ⟨_, hdiv, _⟩
    · omega
    · rw [hf] at hdiv
      have hmod := Nat.mod_eq_zero_of_dvd hdiv
      omega
  · refine Or.inr (Or.inl ⟨ht, hf, ?_⟩)
    rcases hanchor with ⟨hs, _, _⟩ | ⟨_, hdiv, _⟩
    · omega
    · rw [hf] at hdiv
      have hmod := Nat.mod_eq_zero_of_dvd hdiv
      omega
  · have hs : s = 2 * e - 1 := by omega
    rw [hs] at hDs hf
    exact False.elim (no_fifteen_before_large_old_event he hDs hf)
  · exact False.elim (no_seven_before_large_old_event (by omega) hDs hf (Or.inl (by omega)))
  · exact False.elim (no_seven_before_large_old_event (by omega) hDs hf (Or.inr (by omega)))
  · obtain ⟨_, ht2, ht4⟩ := large_old_event_gap_mod_three hstep hr hC
    have he3 : e % 3 = 0 := by
      by_cases h : e % 3 = 1
      · have := ht2 h
        omega
      · by_cases h' : e % 3 = 2
        · have := ht4 h'
          omega
        · omega
    refine Or.inr (Or.inr ⟨ht, hf, he3, ?_⟩)
    rcases hanchor with ⟨_, hdiv, _⟩ | ⟨hs, _, _⟩
    · rw [hf] at hdiv
      have hmod := Nat.mod_eq_zero_of_dvd hdiv
      omega
    · omega

/-- Exact backward transitions eliminate both preceding increments 7
and the preceding increment 15 from the large case. -/
theorem moving_horizon_large_old_event_three_predecessors {sp Cp s C r C' e : Nat}
    (hprev : IsMovingHorizonStep sp Cp s C) (hstep : IsMovingHorizonStep s C r C')
    (he : 20 ≤ e) (hr : r = 2 * e) (hC : C = 3 * e + 1) :
    LargeOldEventRemaining e (r - s) (d s) :=
  large_old_event_remaining_of_nonunit hstep (by have := hprev.1.1; have := hprev.2.1; omega)
    (moving_horizon_step_event_ge_three hprev) he hr hC

/-- A half-index increment in the original recurrence is equivalent to
a single exact horizon value, without a previous-record assumption. -/
theorem half_index_increment_iff {e : Nat} (he : 5 ≤ e) :
    d (2 * e) = e ↔ D (2 * e - 1) = 3 * e + 1 := by
  have hmap : d (2 * e) = Nat.gcd (2 * e) (D (2 * e - 1) - 1) := by
    have h := constant_D_event_map (by omega : 2 ≤ 2 * e)
      (rfl : D (2 * e - 1) = D (2 * e - 1))
    simpa only [show (2 * e) % 2 = 0 by omega, if_pos] using h
  constructor
  · intro hd
    have hpar := D_mod_two_eq_zero_of_two_le (by omega : 2 ≤ 2 * e - 1)
    have heodd := hd ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ 2 * e)
    have hdiv : e ∣ D (2 * e - 1) - 1 := by
      have h : d (2 * e) ∣ D (2 * e - 1) - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
      simpa only [hd] using h
    have hlower := two_mul_le_a_add_two (by omega : 2 ≤ 2 * e - 1)
    have hupper := a_le_three_mul (2 * e - 1)
    have hsum : D (2 * e - 1) + (2 * e - 1) = a (2 * e - 1) :=
      Nat.sub_add_cancel (index_le_a _)
    obtain ⟨q, hq⟩ := hdiv
    have hqodd : q % 2 = 1 := by
      rw [quotient_mod_two_of_left_odd heodd, ← hq]
      omega
    have hqlo : 3 ≤ q := by
      by_cases h : 3 ≤ q
      · exact h
      · have hm := Nat.mul_le_mul_left e (show q ≤ 1 by omega)
        rw [← hq, Nat.mul_one] at hm
        omega
    have hqhi : q < 4 := by
      by_cases h : q < 4
      · exact h
      · have hm := Nat.mul_le_mul_left e (show 4 ≤ q by omega)
        rw [← hq, Nat.mul_comm e 4] at hm
        omega
    have hqthree : q = 3 := by omega
    rw [hqthree, Nat.mul_comm e 3] at hq
    omega
  · intro hD
    rw [hmap, hD, show 3 * e + 1 - 1 = 3 * e by omega,
      Nat.mul_comm 2 e, Nat.mul_comm 3 e, Nat.gcd_mul_left]
    simp [show Nat.gcd 2 3 = 1 by decide]

/-- The three preceding forms are necessary for any sufficiently large
half-index increment, even when no canonical replay is assumed. -/
theorem half_index_increment_predecessor {e : Nat} (he : 20 ≤ e) (hd : d (2 * e) = e) :
    ∃ s : Nat, s < 2 * e ∧ D s = 3 * e + 1 ∧
      (∀ j : Nat, s < j → j < 2 * e → d j = 1) ∧
      LargeOldEventRemaining e (2 * e - s) (d s) := by
  have hC := (half_index_increment_iff (by omega)).1 hd
  have hlast : ∃ s : Nat, 2 ≤ s ∧ s < 2 * e ∧ 1 < d s ∧
      ∀ j : Nat, s < j → j < 2 * e → d j = 1 := by
    by_cases h : d (2 * e - 1) = 1
    · obtain ⟨s, hs, hlt, hf, htail⟩ := exists_last_nontrivial_before h
        ⟨2, by decide, by omega, by decide⟩
      exact ⟨s, hs, by omega, hf, fun j hsj hj => htail j hsj (by omega)⟩
    · have hone := one_le_d_of_two_le (by omega : 2 ≤ 2 * e - 1)
      exact ⟨2 * e - 1, by omega, by omega, by omega, fun j hj hjr => False.elim (by omega)⟩
  obtain ⟨s, hs, hsr, hf, hunit⟩ := hlast
  have hDs := (first_later_event_D_eq hs (rfl : D s = D s) hsr hunit).symm.trans hC
  have hs3 : 3 ≤ s := by
    by_cases h : s = 2
    · rw [h, show D 2 = 2 by decide] at hDs
      omega
    · omega
  have hf3 : 3 ≤ d s := by have := d_mod_two_eq_one_of_three_le hs3; omega
  have hD' : D (2 * e) = 4 * e := by
    have hup := D_succ_add_one_eq_add_d (2 * e - 1)
    rw [show 2 * e - 1 + 1 = 2 * e by omega, hC, hd] at hup
    omega
  have hstep : IsMovingHorizonStep s (3 * e + 1) (2 * e) (4 * e) :=
    ⟨⟨hs, hDs, by omega⟩, hsr, by omega, by omega, hunit, hC, hD'.symm, by omega,
      ⟨by omega, hD', by omega⟩⟩
  exact ⟨s, hsr, hDs, hunit, large_old_event_remaining_of_nonunit hstep hs3 hf3 he rfl rfl⟩

/-- The first crossing of `3*M+4` by an old increment begins in this band. -/
theorem moving_horizon_old_crossing_band {M s C r C' : Nat}
    (hModd : M % 2 = 1) (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') :
    2 * M + 6 ≤ C ∧ C ≤ 3 * M + 3 := by
  have hCpar : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hupdate := moving_horizon_step_update hstep
  omega

/-- A large old crossing from a canonical origin has a forced last event
and one of three possible preceding gap-increment pairs. -/
theorem canonical_path_large_old_crossing {M s C p r C' : Nat}
    (hM : 25 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r) :
    r = 2 * d r ∧ C = 3 * d r + 1 ∧ C' = 4 * d r ∧ a r = 3 * r ∧
      LargeOldEventRemaining (d r) (r - s) (d s) := by
  have hModd : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
  obtain ⟨hClo, hChi⟩ := moving_horizon_old_crossing_band hModd hstep hcap hbelow hcross
  have hstart := moving_horizon_path_index_le hpath
  have he3 := moving_horizon_step_event_ge_three hstep
  obtain ⟨hr, hC, hC'⟩ := moving_horizon_large_old_event_shape hstep rfl (by omega) (by omega)
  have hstrict : M + 2 < s := by
    by_cases hp : 1 ≤ p
    · exact moving_horizon_path_index_lt hp hpath
    · have hp₀ : p = 0 := by omega
      subst p
      exact False.elim (by have := hpath.2.1; omega)
  obtain ⟨sp, Cp, q, _, hprev⟩ := moving_horizon_path_last_step hpath hstrict
  have hD : C' = D r := hstep.2.2.2.2.2.2.1
  have ha : D r + r = a r := Nat.sub_add_cancel (index_le_a r)
  exact ⟨hr, hC, hC', by omega,
    moving_horizon_large_old_event_three_predecessors hprev hstep (by omega) hr hC⟩

/-- A hypothetical large crossing requires the prefix from its canonical
origin to have accumulated more than one quarter of the previous record
in horizon growth. This constrains every common even multiple of the
actual earlier increments. -/
theorem canonical_large_old_crossing_prefix_multiple {M s C p r C' P : Nat}
    (hM : 25 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r)
    (hP : 0 < P) (hPeven : P % 2 = 0)
    (hdiv : ∀ j : Nat, M + 2 < j → j ≤ s → d j ∣ P) :
    3 * d r + 1 < 2 * M - 2 + P ∧ M + 21 < 4 * P := by
  have hshape := canonical_path_large_old_crossing hM hcanon hpath hstep hcap hbelow hcross hlarge
  have hstart := moving_horizon_path_index_le hpath
  have hgrowth := D_growth_lt_of_common_even_multiple (by omega : 2 ≤ M + 2)
    hstart hP hPeven hdiv
  have hDstart := (canonical_increment_coordinates (by omega : 5 < M) hcanon).2.1
  rw [hDstart, hstep.1.2.1, hshape.2.1] at hgrowth
  exact ⟨hgrowth, by omega⟩

/-- In the unverified range, a large old crossing needs an earlier old
increment of at least 9 somewhere in the prefix. -/
theorem canonical_large_old_crossing_prefix_has_nine {M s C p r C' : Nat}
    (hM : 968 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r) :
    ∃ j : Nat, M + 2 < j ∧ j ≤ s ∧ 9 ≤ d j := by
  by_cases hex : ∃ j : Nat, M + 2 < j ∧ j ≤ s ∧ 9 ≤ d j
  · exact hex
  · have hdiv (j : Nat) (hj : M + 2 < j) (hjs : j ≤ s) : d j ∣ 210 := by
      have hodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ j)
      have hsmall : d j ≤ 7 := by
        by_cases h : 9 ≤ d j
        · exact False.elim (hex ⟨j, hj, hjs, h⟩)
        · omega
      have hd := odd_dvd_recordHorizonBound hodd hsmall
      rwa [show recordHorizonBound 7 = 210 by decide] at hd
    have hmultiple := canonical_large_old_crossing_prefix_multiple (by omega)
      hcanon hpath hstep hcap hbelow hcross hlarge (by decide) (by decide) hdiv
    omega

end A166944Research
