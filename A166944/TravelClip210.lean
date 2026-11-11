import A166944.TravelExcess

/-! # Clipping a genuine first hit to the modulus 210 -/

namespace A166944Research

private def clippedIncrement210 (r c : Nat) : Nat :=
  if r % 2 = 0 then Nat.gcd (Nat.gcd r 210) (Nat.gcd (c + 209) 210)
  else Nat.gcd (Nat.gcd (r + 208) 210) (Nat.gcd (c + 1) 210)

private theorem gcd210_congr_mod {a b : Nat} (h : a % 210 = b % 210) :
    Nat.gcd a 210 = Nat.gcd b 210 := by
  rw [Nat.gcd_comm a 210, Nat.gcd_comm b 210, Nat.gcd_rec 210 a, Nat.gcd_rec 210 b, h]

private theorem gcd_pair_clip210 (a b : Nat) :
    Nat.gcd (Nat.gcd a 210) (Nat.gcd b 210) = Nat.gcd (Nat.gcd a b) 210 := by
  calc
    _ = Nat.gcd (Nat.gcd a b) (Nat.gcd 210 210) := by ac_rfl
    _ = _ := by rw [Nat.gcd_self]

private theorem clipped_increment210_matches {s C gap : Nat}
    (hr : 2 ≤ s + gap) (hD : D (s + gap - 1) = C) (hC : 1 ≤ C) :
    clippedIncrement210 (s % 210 + gap) (C % 210) = Nat.gcd (d (s + gap)) 210 := by
  rw [constant_D_event_map hr hD, clippedIncrement210]
  have hpar : (s % 210 + gap) % 2 = (s + gap) % 2 := by omega
  rw [hpar]
  split
  · rw [gcd210_congr_mod (by omega : (s % 210 + gap) % 210 = (s + gap) % 210),
      gcd210_congr_mod (by omega : (C % 210 + 209) % 210 = (C - 1) % 210)]
    exact gcd_pair_clip210 _ _
  · rw [gcd210_congr_mod (by omega : (s % 210 + gap + 208) % 210 = (s + gap - 2) % 210),
      gcd210_congr_mod (by omega : (C % 210 + 1) % 210 = (C + 1) % 210)]
    exact gcd_pair_clip210 _ _

private def scanClipped210 (s c start : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
      let e := clippedIncrement210 (s + start) c
      if 1 < e then some (start, e) else scanClipped210 s c (start + 1) fuel

def firstClippedHit210 (s c : Nat) : Option (Nat × Nat) :=
  scanClipped210 s c 1 14

private theorem scan_clipped210_of_first {s c start gap fuel : Nat}
    (hstart : start ≤ gap) (hstop : gap < start + fuel)
    (hgap : 1 < clippedIncrement210 (s + gap) c)
    (hunit : ∀ j : Nat, start ≤ j → j < gap → clippedIncrement210 (s + j) c ≤ 1) :
    scanClipped210 s c start fuel = some (gap, clippedIncrement210 (s + gap) c) := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases h : start = gap
    · subst start
      simp only [scanClipped210, if_pos hgap]
    · have hsmall := hunit start (Nat.le_refl _) (by omega)
      simp only [scanClipped210, if_neg (Nat.not_lt_of_ge hsmall)]
      exact ih (by omega) (by omega) (fun j hj hg => hunit j (by omega) hg)

set_option maxRecDepth 65536 in
private theorem supported_increment_has_small_factor210 :
    ∀ e : Fin 211, 1 < e.val → e.val ∣ 210 → ∃ f : Fin 8, 1 < f.val ∧ f.val ∣ e.val := by
  decide

private theorem moving_horizon_clipped_gap_le_fourteen {s C r C' e : Nat}
    (hstep : IsMovingHorizonStep s C r C') (he : 1 < e) (hdiv : e ∣ 210) (hincr : e ∣ d r) : r - s ≤ 14 := by
  have hle := Nat.le_of_dvd (by decide : 0 < 210) hdiv
  obtain ⟨f, hf, hfd⟩ := supported_increment_has_small_factor210 ⟨e, by omega⟩ he hdiv
  have hg := moving_horizon_step_gap_le_twice_increment_factor hstep hf (Nat.dvd_trans hfd hincr)
  have hf8 := f.isLt
  omega

theorem moving_horizon_supported_gap_le_fourteen {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) : r - s ≤ 14 :=
  moving_horizon_clipped_gap_le_fourteen hstep hstep.2.2.2.1 hdiv (Nat.dvd_refl _)

/-- A nonunit clipped increment occurs at the genuine first hit,
even when the full increment has an additional factor. -/
theorem first_clipped_hit210_of_nonunit {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hclip : 1 < Nat.gcd (d r) 210) :
    firstClippedHit210 (s % 210) (C % 210) = some (r - s, Nat.gcd (d r) 210) := by
  have hsr := hstep.2.1
  have hs := hstep.1.1
  have hC : 1 ≤ C := by have := hstep.1.2.2; omega
  have agree (i : Nat) (hi : 0 < i) (hir : i ≤ r - s) :
      clippedIncrement210 (s % 210 + i) (C % 210) = Nat.gcd (d (s + i)) 210 := by
    have hD := first_later_event_D_eq hs hstep.1.2.1 (by omega : s < s + i)
      (fun j hsj hji => hstep.2.2.2.2.1 j hsj (by omega))
    exact clipped_increment210_matches (by omega) hD hC
  have hAt := agree (r - s) (by omega) (Nat.le_refl _)
  rw [show s + (r - s) = r by omega] at hAt
  have hunit (j : Nat) (hj : 1 ≤ j) (hjr : j < r - s) :
      clippedIncrement210 (s % 210 + j) (C % 210) ≤ 1 := by
    rw [agree j (by omega) (by omega), hstep.2.2.2.2.1 (s + j) (by omega) (by omega), Nat.gcd_one_left]
    exact Nat.le_refl _
  have hgap := moving_horizon_clipped_gap_le_fourteen hstep hclip (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold firstClippedHit210
  rw [scan_clipped210_of_first (by omega : 1 ≤ r - s) (by omega : r - s < 1 + 14)
    (by rw [hAt]; exact hclip) hunit, hAt]

theorem first_clipped_hit210_of_supported {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    firstClippedHit210 (s % 210) (C % 210) = some (r - s, d r) := by
  have hd := Nat.gcd_eq_left_iff_dvd.mpr hdiv
  have hc : 1 < Nat.gcd (d r) 210 := hd.symm ▸ hstep.2.2.2.1
  simpa only [hd] using first_clipped_hit210_of_nonunit hstep hc

end A166944Research
