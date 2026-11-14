import A166944.Lemmas

/-!
# q = 2 unit tail: the witness dies, and where the general step is blocked

## 1. The concrete witness

`(M, delta, c, e) = (11, 15, 4, 13)` with state `(s, C, r) = (60, 90, 67)`,
`C' = D 67`.  The branch data is `r - 2 = 65 = 13 * 5`, `C + 1 = 91 = 13 * 7`,
`v - u = 2`; the unit tail of `moving_horizon_first_hit_map` fails at `j = 65`:

    gcd (65 - 2) (90 + 1) = gcd 63 91 = 7 != 1.

Because the tail predicate is a *necessary* condition for a step (theorem
`moving_horizon_first_hit_map` of the repository), this refutes the step for
**every** candidate endpoint `C'`, with no extra hypothesis.

## 2. The two general sufficient conditions

* e-family: `j = r - 2 * k * e` is odd, and `e` divides `j - 2 = e * (u - 2k)`
  as well as `C + 1`.  Hypothesis: `s < r - 2 * e`.
* cofactor family: `j = r - 2` gives
  `j - 2 = (C + 1) - 2 * (e + 1)`, hence
  `gcd (j - 2) (C + 1) = gcd (2 * (e + 1)) (C + 1)`;
  the tail fails exactly when that gcd exceeds `1` (on the witness it is `7`).

## 3. Why the e-family cannot be the general weapon

In the critical branch `d r = delta` and `r - s < delta`, so `e = delta` and
`r - s < e`; then `r - 2 * e < s`, i.e. **the whole e-family lies strictly
before the state**.  Only the cofactor family reaches into the tail, and it
needs the arithmetic accident `gcd (2 * (e + 1)) (C + 1) > 1`, which the branch
invariants (`gcd u v = 1`, `v - u = 2`) do not imply.
-/

namespace A166944Research

set_option maxRecDepth 100000

/-! ## 1. The concrete witness -/

theorem gcd_63_91 : Nat.gcd 63 (91 : Nat) = 7 := by decide

/-- The q = 2 survivor `(M, delta, c, e) = (11, 15, 4, 13)`, state
`(s, C, r) = (60, 90, 67)`, fails the odd unit tail. -/
theorem q2_survivor_tail_violation :
    ¬ (∀ j : Nat, 60 < j → j < 67 →
        (j % 2 = 1 → Nat.gcd (j - 2) (90 + 1) = 1)) := by
  intro h
  have h65 := h 65 (by decide) (by decide) (by decide)
  rw [gcd_63_91] at h65
  omega

/-- The same violation in the exact shape produced by
`moving_horizon_first_hit_map`. -/
theorem q2_survivor_not_first_hit_tail :
    ¬ (∀ j : Nat, 60 < j → j < 67 →
      (j % 2 = 0 → Nat.gcd j (90 - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (90 + 1) = 1)) := by
  intro h
  have h65 := (h 65 (by decide) (by decide)).2 (by decide)
  rw [gcd_63_91] at h65
  omega

/-- **The terminal kill.**  There is no moving-horizon step from `(60, 90)` to
`67` with any endpoint, because the unit tail -- a necessary condition by
`moving_horizon_first_hit_map` -- is violated at `j = 65`. -/
theorem no_step_60_90_67 {C' : Nat} : ¬ IsMovingHorizonStep 60 90 67 C' := by
  intro hstep
  rcases moving_horizon_first_hit_map hstep with ⟨_, _, _, htail⟩ | ⟨_, _, _, htail⟩
  · exact q2_survivor_not_first_hit_tail htail
  · exact q2_survivor_not_first_hit_tail htail

/-- The abstract schema behind the kill: one bad interior odd index suffices. -/
theorem no_step_of_tail_violation {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r)
    (hodd : j % 2 = 1) (hbad : Nat.gcd (j - 2) (C + 1) ≠ 1) : False := by
  rcases moving_horizon_first_hit_map hstep with ⟨_, _, _, htail⟩ | ⟨_, _, _, htail⟩
  · exact hbad ((htail j hsj hjr).2 hodd)
  · exact hbad ((htail j hsj hjr).2 hodd)

/-! ## 2. The e-family: sufficient, but vacuous in the critical branch -/

/-- `j = r - 2e` is a violation as soon as it lies in the tail and is odd. -/
theorem tail_violation_of_e_dvd_sub_two
    {s C r e u : Nat} (he3 : 3 ≤ e)
    (hu : r - 2 = e * u) (hdiv : e ∣ C + 1)
    (hleft : s < r - 2 * e) (hodd : (r - 2 * e) % 2 = 1) :
    ¬ (∀ j : Nat, s < j → j < r →
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1)) := by
  intro h
  have hsub : (r - 2) - e * 2 = (r - 2 * e) - 2 := by omega
  have hmul : (r - 2) - e * 2 = e * u - e * 2 := by rw [hu]
  have hkey : (r - 2 * e) - 2 = e * (u - 2) := by
    rw [← hsub, hmul]
    rw [Nat.mul_sub_left_distrib]
  have hdvdj : e ∣ (r - 2 * e) - 2 := ⟨u - 2, hkey⟩
  have hdvdg : e ∣ Nat.gcd ((r - 2 * e) - 2) (C + 1) := Nat.dvd_gcd hdvdj hdiv
  have hval := h (r - 2 * e) hleft (by omega) hodd
  rw [hval] at hdvdg
  have he1 : e = 1 := Nat.eq_one_of_dvd_one hdvdg
  omega

/-- **The obstruction.**  In the critical branch `r - s < delta = e`, the whole
e-family `r - 2 * e` lies strictly before the state, so it can never be used. -/
theorem e_family_candidate_not_in_tail {s r e : Nat} (he : 1 ≤ e)
    (hshort : r - s < e) : ¬ (s < r - 2 * e) := by
  omega

/-! ## 3. The cofactor family: this is what kills the witness -/

/-- `j = r - 2` is a violation whenever some common factor of `C + 1` and
`2 * (e + 1)` exceeds `1` (here `7`). -/
theorem tail_violation_at_r_sub_two
    {s C r e u v : Nat} (hgap : v = u + 2) (hu : r - 2 = e * u)
    (hv : C + 1 = e * v)
    (hcommon : 1 < Nat.gcd (2 * (e + 1)) (C + 1))
    (hleft : s < r - 2) (hodd : (r - 2) % 2 = 1) :
    ¬ (∀ j : Nat, s < j → j < r →
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1)) := by
  intro h
  have hv' : C + 1 = e * (u + 2) := by rw [hgap] at hv; exact hv
  have h1 : C + 1 = e * u + 2 * e := by
    rw [hv', Nat.mul_add, Nat.mul_comm e 2]
  have hkey : r - 2 - 2 = C + 1 - 2 * (e + 1) := by
    rw [h1]
    omega
  have hval : Nat.gcd (r - 2 - 2) (C + 1) = 1 := h (r - 2) hleft (by omega) hodd
  have hg1 : Nat.gcd (2 * (e + 1)) (C + 1) ∣ 2 * (e + 1) := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (2 * (e + 1)) (C + 1) ∣ C + 1 := Nat.gcd_dvd_right _ _
  have hg3 : Nat.gcd (2 * (e + 1)) (C + 1) ∣ (C + 1) - 2 * (e + 1) :=
    Nat.dvd_sub hg2 hg1
  have hg4 : Nat.gcd (2 * (e + 1)) (C + 1) ∣ Nat.gcd (r - 2 - 2) (C + 1) := by
    refine Nat.dvd_gcd ?_ hg2
    rw [hkey]
    exact hg3
  rw [hval] at hg4
  have hle : Nat.gcd (2 * (e + 1)) (C + 1) ≤ 1 := Nat.le_of_dvd (by decide) hg4
  omega

/-- The witness instantiation of the cofactor family: `r = 67`, `e = 13`,
`u = 5`, `v = 7`, `C + 1 = 91`, and `gcd (2 * 14) 91 = 7 > 1`. -/
theorem q2_survivor_cofactor_kill :
    ¬ (∀ j : Nat, 60 < j → j < 67 →
        (j % 2 = 1 → Nat.gcd (j - 2) (90 + 1) = 1)) := by
  refine tail_violation_at_r_sub_two (e := 13) (u := 5) (v := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms q2_survivor_tail_violation
#print axioms q2_survivor_not_first_hit_tail
#print axioms no_step_60_90_67
#print axioms no_step_of_tail_violation
#print axioms tail_violation_of_e_dvd_sub_two
#print axioms e_family_candidate_not_in_tail
#print axioms tail_violation_at_r_sub_two

end A166944Research
