import A166944.RoomQuantum
import A166944.RoomLedger
import A166944.BandReentry
import A166944.BandExcursion

set_option maxRecDepth 100000

/-!
# Round-5 red team, part 2: the angle `RoomQuantum` leaves on the table

`RoomQuantum.moving_horizon_event_dvd_next_horizon` says the event of a step divides
the horizon that *follows* it: `d r | C'` (even) and `d r | C' + 2` (odd).

`Lemmas.moving_horizon_successive_event_gcd_eq_one_of_parity` is an **orphan** (its
name occurs nowhere else in the repository) and says two consecutive event values are
coprime under a parity condition.

Composing the two gives a constraint the repository does not state: **consecutive
event values share at most the factor `3`.**  Both values are odd, so the gcd is
exactly `1` or `3`.
-/

namespace A166944Research

/-! ## 1. The two carries, per branch -/

theorem carry_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) : d r ∣ C' :=
  moving_horizon_event_dvd_next_horizon_even hstep hr

theorem carry_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) : d r ∣ C' + 2 :=
  moving_horizon_event_dvd_next_horizon_odd hstep hr

/-- The next step's even hit divides `C' - 1`. -/
theorem next_event_dvd_horizon_even {r C' u C'' : Nat} (hnext : IsMovingHorizonStep r C' u C'')
    (hu : u % 2 = 0) : d u ∣ C' - 1 := by
  rcases moving_horizon_step_event_package hnext with h | h
  · exact h.2.1
  · exact absurd (h.1.symm.trans hu) (by decide)

/-- The next step's odd hit divides `C' + 1`. -/
theorem next_event_dvd_horizon_odd {r C' u C'' : Nat} (hnext : IsMovingHorizonStep r C' u C'')
    (hu : u % 2 = 1) : d u ∣ C' + 1 := by
  rcases moving_horizon_step_event_package hnext with h | h
  · exact absurd (h.1.symm.trans hu) (by decide)
  · exact h.2.1

/-! ## 2. The composition -/

/-- **Even then even.**  `d r | C'` and `d u | C' - 1`, and `C' - 1 < C'`, so the two
divisors are coprime. -/
theorem gcd_consecutive_even_even {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hr : r % 2 = 0) (hu : u % 2 = 0) : Nat.gcd (d r) (d u) = 1 := by
  have h1 : d r ∣ C' := carry_even hstep hr
  have h2 : d u ∣ C' - 1 := next_event_dvd_horizon_even hnext hu
  have hC1 : 1 ≤ C' := by
    have hlt := hnext.1.2.2
    have hr2 : 2 ≤ r := hnext.1.1
    omega
  have hg : Nat.gcd (d r) (d u) ∣ 1 := by
    have ha : Nat.gcd (d r) (d u) ∣ C' := Nat.dvd_trans (Nat.gcd_dvd_left _ _) h1
    have hb : Nat.gcd (d r) (d u) ∣ C' - 1 := Nat.dvd_trans (Nat.gcd_dvd_right _ _) h2
    have hsub := Nat.dvd_sub ha hb
    have hone : C' - (C' - 1) = 1 := by omega
    rwa [hone] at hsub
  exact Nat.eq_one_of_dvd_one hg

/-- **Even then odd.**  `d r | C'` and `d u | C' + 1`: the difference is `1`. -/
theorem gcd_consecutive_even_odd {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hr : r % 2 = 0) (hu : u % 2 = 1) : Nat.gcd (d r) (d u) = 1 := by
  have h1 : d r ∣ C' := carry_even hstep hr
  have h2 : d u ∣ C' + 1 := next_event_dvd_horizon_odd hnext hu
  have hg : Nat.gcd (d r) (d u) ∣ 1 := by
    have ha : Nat.gcd (d r) (d u) ∣ C' := Nat.dvd_trans (Nat.gcd_dvd_left _ _) h1
    have hb : Nat.gcd (d r) (d u) ∣ C' + 1 := Nat.dvd_trans (Nat.gcd_dvd_right _ _) h2
    have := Nat.dvd_sub hb ha
    simpa using this
  exact Nat.eq_one_of_dvd_one hg

/-- **Odd then even.**  `d r | C' + 2` and `d u | C' - 1`: the difference is `3`. -/
theorem gcd_consecutive_odd_even_dvd_three {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hr : r % 2 = 1) (hu : u % 2 = 0) : Nat.gcd (d r) (d u) ∣ 3 := by
  have h1 : d r ∣ C' + 2 := carry_odd hstep hr
  have h2 : d u ∣ C' - 1 := next_event_dvd_horizon_even hnext hu
  have hC1 : 1 ≤ C' := by
    have hlt := hnext.1.2.2
    have hr2 : 2 ≤ r := hnext.1.1
    omega
  have ha : Nat.gcd (d r) (d u) ∣ C' + 2 := Nat.dvd_trans (Nat.gcd_dvd_left _ _) h1
  have hb : Nat.gcd (d r) (d u) ∣ C' - 1 := Nat.dvd_trans (Nat.gcd_dvd_right _ _) h2
  have hsub : Nat.gcd (d r) (d u) ∣ (C' + 2) - (C' - 1) := Nat.dvd_sub ha hb
  have hthree : (C' + 2) - (C' - 1) = 3 := by omega
  rwa [hthree] at hsub

/-! ## 3. The uniform statement, and the orphan's role -/

/-- **Consecutive event values share at most one factor `3`.**  For `r` even no
parity condition on `u` is needed at all. -/
theorem gcd_consecutive_dvd_three_of_even {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hre : r % 2 = 0) : Nat.gcd (d r) (d u) ∣ 3 := by
  rcases Nat.mod_two_eq_zero_or_one u with hue | huo
  · rw [gcd_consecutive_even_even hstep hnext hre hue]
    exact ⟨3, by decide⟩
  · rw [gcd_consecutive_even_odd hstep hnext hre huo]
    exact ⟨3, by decide⟩

/-- For `r` odd and `u` even the bound is `3`; the difference is exactly `3` because
`C' + 2 - (C' - 1) = 3`. -/
theorem gcd_consecutive_dvd_three_of_odd_even {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hro : r % 2 = 1) (huo : u % 2 = 0) : Nat.gcd (d r) (d u) ∣ 3 :=
  gcd_consecutive_odd_even_dvd_three hstep hnext hro huo

/-- **Uniform.**  Writing the parity condition as the orphan's hypothesis (`r` even, or
both odd), consecutive events share a divisor of `3`. -/
theorem gcd_consecutive_dvd_three {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (h : r % 2 = 0 ∨ (r % 2 = 1 ∧ u % 2 = 1)) : Nat.gcd (d r) (d u) ∣ 3 := by
  rcases h with hre | ⟨hro, huo⟩
  · exact gcd_consecutive_dvd_three_of_even hstep hnext hre
  · have hone : Nat.gcd (d r) (d u) = 1 :=
      moving_horizon_successive_event_gcd_eq_one_of_parity hstep hnext (Or.inr ⟨hro, huo⟩)
    rw [hone]
    exact ⟨3, by decide⟩

/-! ## 4. Every event value is odd, so the gcd is `1` or `3` -/

theorem event_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    d r % 2 = 1 := by
  have hr3 : 3 ≤ r := by
    have := hstep.1.1
    have := hstep.2.1
    omega
  exact d_mod_two_eq_one_of_three_le hr3

/-- The gcd of two consecutive event values is `1` or `3`.  It divides `3` and is
positive, so `1` and `3` are the only options -- no parity of the values is needed. -/
theorem gcd_consecutive_eq_one_or_three {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (h : r % 2 = 0 ∨ (r % 2 = 1 ∧ u % 2 = 1)) :
    Nat.gcd (d r) (d u) = 1 ∨ Nat.gcd (d r) (d u) = 3 := by
  have hdvd : Nat.gcd (d r) (d u) ∣ 3 := gcd_consecutive_dvd_three hstep hnext h
  have hle : Nat.gcd (d r) (d u) ≤ 3 := Nat.le_of_dvd (by decide) hdvd
  have hpos : 0 < Nat.gcd (d r) (d u) := by
    apply Nat.gcd_pos_of_pos_left
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hne2 : Nat.gcd (d r) (d u) ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hdvd
    rw [h2] at hk
    omega
  omega

/-! ## 5. The prior-art status of the orphan's parity condition

The orphan `moving_horizon_successive_event_gcd_eq_one_of_parity` is used only in the
both-odd case.  The even case needs no parity hypothesis at all, so the orphan's
condition is *stricter than necessary* for the `| 3` conclusion: any event value can
be followed by any other and the gcd still divides `3`, except that the odd-odd case
is not reachable by the carry argument alone (both carries refer to `C'`, and
`gcd (C' + 2) (C' + 1) = 1` holds via the *next* step's odd carry, giving `| 1`).
-/

/-- **Odd then odd, by the carry argument.**  `d u | C' + 1` (odd hit at `u`) and
`d r | C' + 2`, and `C' + 1`, `C' + 2` are consecutive, so the gcd divides `1`.  This
re-proves the orphan's conclusion without its extra machinery. -/
theorem gcd_consecutive_odd_odd {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hr : r % 2 = 1) (hu : u % 2 = 1) : Nat.gcd (d r) (d u) = 1 := by
  have h1 : d r ∣ C' + 2 := carry_odd hstep hr
  have h2 : d u ∣ C' + 1 := next_event_dvd_horizon_odd hnext hu
  have hg : Nat.gcd (d r) (d u) ∣ 1 := by
    have ha : Nat.gcd (d r) (d u) ∣ C' + 2 := Nat.dvd_trans (Nat.gcd_dvd_left _ _) h1
    have hb : Nat.gcd (d r) (d u) ∣ C' + 1 := Nat.dvd_trans (Nat.gcd_dvd_right _ _) h2
    have hsub := Nat.dvd_sub ha hb
    have hone : (C' + 2) - (C' + 1) = 1 := by omega
    rwa [hone] at hsub
  exact Nat.eq_one_of_dvd_one hg

/-- **The uniform `| 3` with NO parity hypothesis whatsoever.**  All four parity cases
are covered, so the orphan's hypothesis is not needed for this conclusion. -/
theorem gcd_consecutive_dvd_three_unconditional {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'') :
    Nat.gcd (d r) (d u) ∣ 3 := by
  rcases Nat.mod_two_eq_zero_or_one r with hre | hro
  · exact gcd_consecutive_dvd_three_of_even hstep hnext hre
  · rcases Nat.mod_two_eq_zero_or_one u with hue | huo
    · exact gcd_consecutive_odd_even_dvd_three hstep hnext hro hue
    · rw [gcd_consecutive_odd_odd hstep hnext hro huo]
      exact ⟨3, by decide⟩

end A166944Research
