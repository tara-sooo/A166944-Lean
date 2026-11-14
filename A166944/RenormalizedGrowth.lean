import A166944.Lemmas

/-!
# Lane E — renormalized growth for A166944

Renormalized (deficit) coordinate:

    Λ n  :=  2 * n - D n          (`D n = a n - n`),

so `Λ n ≥ 0` is exactly `a n ≤ 3 n`.  Its exact one-step law, obtained from the
PROVED `moving_horizon_excess_transition`, is

    Λ r  =  Λ s + (2 * (r - s) + 1) - d r .

Main result: the state bound `C ≤ 2 * s` (that is `Λ s ≥ 0`) is **preserved by
one first-event step inside the abstract gcd map**, using only the proved parity
fact `D s % 2 = 0`.  Neither the horizon bound `r ≤ C`, nor the size bound
`3 * d r ≤ C ± 1`, nor the first-hit condition is needed.

The two branches are pure divisibility statements:

* `r` even: `d r ∣ r` and `d r ∣ C - 1`, so `d r ∣ 2 * r - (C - 1)`, and that
  integer is positive; hence `d r ≤ 2 * r - (C - 1)` and `D r ≤ 2 * r`.
* `r` odd: `d r ∣ C + 1` and `d r ∣ r - 2`.
  - If `2 * r ≤ C + 5`, the integer `Z := (C + 1) - 2 * (r - 2)` satisfies
    `0 ≤ Z ≤ 3`; it is odd because `C` is even, so `Z = 1` (forces `d r = 1`,
    contradicting `1 < d r`) or `Z = 3` (forces `d r ≤ 3`).
  - If `C + 5 < 2 * r`, write `C + 1 = d r * u`, `r - 2 = d r * v`; then
    `u < 2 * v`, so `u + 1 ≤ 2 * v` and `D r = d r * (u + 1) - 2 ≤ 2 * r`.
-/

namespace A166944Research

/-- The renormalized (deficit) coordinate `Λ n = 2 * n - D n`. -/
def Lam (n : Nat) : Nat := 2 * n - D n

theorem Lam_def (n : Nat) : Lam n = 2 * n - D n := rfl

/-- `D r ≤ 2 * r` for a state obtained from `D (r-1) = C` and `C ≤ 2 * s`,
`s < r`, in the abstract gcd map with `C` even.  This is the whole content of
the renormalized growth step, split into the two parity cases. -/
theorem event_step_state_bound {s C r : Nat}
    (hsr : s < r) (hC : D (r - 1) = C) (hr : 2 ≤ r)
    (hbound : C ≤ 2 * s) (hCeven : C % 2 = 0) (hdr : 1 < d r) :
    D r ≤ 2 * r := by
  have hr1 : 1 ≤ r := by omega
  have hrsub : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    rw [hrsub, hC] at h
    exact h
  have hmap := constant_D_event_map hr hC
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · -- ============ EVEN BRANCH ============
    rw [if_pos heven] at hmap
    have hdivC : d r ∣ C - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hdivr : d r ∣ r := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hC2r : C - 1 < 2 * r := by omega
    have hdiv : d r ∣ 2 * r - (C - 1) :=
      Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hdivr 2) hdivC
    have hpos : 0 < 2 * r - (C - 1) := Nat.sub_pos_of_lt hC2r
    have hle : d r ≤ 2 * r - (C - 1) := Nat.le_of_dvd hpos hdiv
    omega
  · -- ============ ODD BRANCH ============
    rw [if_neg (by omega : ¬ r % 2 = 0)] at hmap
    have hdivC : d r ∣ C + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hdivr : d r ∣ r - 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    by_cases hcase : 2 * r ≤ C + 5
    · -- Case A: the odd residue Z = (C + 1) - 2 * (r - 2) is 1 or 3.
      have hZle : 2 * (r - 2) ≤ C + 1 := by omega
      have hZdiv : d r ∣ (C + 1) - 2 * (r - 2) :=
        Nat.dvd_sub hdivC (Nat.dvd_mul_left_of_dvd hdivr 2)
      have hZle3 : (C + 1) - 2 * (r - 2) ≤ 3 := by omega
      have hZodd : ((C + 1) - 2 * (r - 2)) % 2 = 1 := by omega
      have hZ : (C + 1) - 2 * (r - 2) = 1 ∨ (C + 1) - 2 * (r - 2) = 3 := by omega
      rcases hZ with hZ1 | hZ3
      · have hone : d r ∣ 1 := hZ1 ▸ hZdiv
        have hd1 : d r = 1 := Nat.eq_one_of_dvd_one hone
        omega
      · have hthree : d r ∣ 3 := hZ3 ▸ hZdiv
        have hle3 : d r ≤ 3 := Nat.le_of_dvd (by decide) hthree
        omega
    · -- Case B: u := (C+1)/e, v := (r-2)/e, and u < 2*v.
      have hcase' : C + 5 < 2 * r := by omega
      obtain ⟨u, hu⟩ := hdivC
      obtain ⟨v, hv⟩ := hdivr
      have hlt : C + 1 < 2 * (r - 2) := by omega
      have hr' : r = d r * v + 2 := by omega
      have hW : 2 * (d r * v) = d r * (2 * v) := by
        rw [Nat.mul_left_comm]
      have hlt' : d r * u < d r * (2 * v) := by
        calc
          d r * u = C + 1 := hu.symm
          _ < 2 * (r - 2) := hlt
          _ = 2 * (d r * v) := by rw [hv]
          _ = d r * (2 * v) := hW
      have huv : u < 2 * v := by
        rcases Nat.lt_or_ge u (2 * v) with hlt2 | hge
        · exact hlt2
        · have hmono := Nat.mul_le_mul_left (d r) hge
          omega
      have huv1 : u + 1 ≤ 2 * v := by omega
      have hmul : d r * (u + 1) ≤ d r * (2 * v) := Nat.mul_le_mul_left _ huv1
      have hdist : d r * (u + 1) = d r * u + d r := by
        rw [Nat.mul_succ]
      have hDform : D r = d r * u + d r - 2 := by
        rw [hstep]
        omega
      have hr2eq : 2 * r = 2 * (d r * v) + 4 := by omega
      have h2r : 2 * r = d r * (2 * v) + 4 := by
        rw [hW] at hr2eq
        exact hr2eq
      omega

/-- **Renormalized growth step.**  One first-event step preserves the state
bound `C ≤ 2 * s` inside the abstract gcd map, using only `D s % 2 = 0`. -/
theorem moving_horizon_step_state_bound {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hbound : C ≤ 2 * s) :
    C' ≤ 2 * r := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩
  have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
  have hCeven : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hD := event_step_state_bound hsr hDr hr2 hbound hCeven hdr
  omega

/-- Two-step version (recorded separately: the natural place where one-step
bounds often fail while the iterated statement survives). -/
theorem moving_horizon_two_steps_state_bound {s C r C' r' C'' : Nat}
    (h1 : IsMovingHorizonStep s C r C') (h2 : IsMovingHorizonStep r C' r' C'')
    (hbound : C ≤ 2 * s) : C'' ≤ 2 * r' :=
  moving_horizon_step_state_bound h2 (moving_horizon_step_state_bound h1 hbound)

/-- **Global growth constraint.**  Every state reachable along a moving-horizon
path from a state with `C ≤ 2 * s` again satisfies `C ≤ 2 * s`: the deficit
coordinate `Λ x = 2 * x - D x` never becomes negative. -/
theorem moving_horizon_path_state_bound {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) (hbound : C ≤ 2 * s) :
    Cf ≤ 2 * sf := by
  induction q generalizing s C with
  | zero =>
      rcases hpath with ⟨hsf, hCf, _⟩
      omega
  | succ q ih =>
      rcases hpath with ⟨hstate, r, C', hstep, htail⟩
      exact ih htail (moving_horizon_step_state_bound hstep hbound)

/-- The same statement in slack coordinates: the slack `C - s` never exceeds the
index `s`.  (`state_bound_iff_slack` converts, using `s ≤ C`.) -/
theorem moving_horizon_path_slack_le_index {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) (hbound : C ≤ 2 * s) :
    Cf - sf ≤ sf := by
  have h := moving_horizon_path_state_bound hpath hbound
  omega

end A166944Research
