import A166944.Lemmas

/-!
# The D-coordinate event-divisor nodes (Shevelev's first-hit ingredients)

Shevelev `arXiv:0911.5478` studies the *same* recurrence as A166944
(`c(1)=2`, even step `gcd(n, c(n-1))`, odd step `gcd(n-2, c(n-1))`).
His central object is the constant-`D` run: in the D-coordinate `D n = a n - n`
the value is invariant along a run of unit increments, and the next nontrivial
increment is governed by `C = D` at the run's start.

`constant_D_event_map` already gives the transition.  What the blueprint needs
is the *divisor direction* of that transition, which is what Shevelev uses in
every one of his first-hit arguments (his eqns (3.7)-(3.9)):

* odd branch  (Shevelev's "r = 3" side): `d r ∣ C + 1` and `d r ∣ r - 2`;
* even branch (Shevelev's "r = 2" side): `d r ∣ C - 1` and `d r ∣ r`.

Consequences recorded here:

* every event value divides `r - 2` (odd) or `r` (even), hence `d r + 2 ≤ r`
  whenever the event is nontrivial -- the index of a nontrivial increment is
  at least its value plus two;
* at an odd event, `d r ∣ D (r-1) + 1`, so a record value `R` occurring at an
  odd index satisfies `R ≤ D (r-1) + 1` (i.e. `D (r-1) ≡ -1 mod R`).

These are exactly the two inequalities Shevelev combines with the *minimality*
of `q = spf (C+1)` (odd case) or `spf (C-1)` (even case) to obtain his
first-hit formula `r = (C + q + 5)/2` (odd case) resp. `r = 2 * spf (C-1)`
(even case).  The minimality half -- "no event strictly between" -- is not
asserted here; it is the transplant obligation identified in the report.
-/

namespace A166944Research

/-- **Odd-branch divisor node.**  At an odd index `r` whose predecessor has
`D (r-1) = C`, the event value divides both `C + 1` and `r - 2`. -/
theorem odd_event_value_dvd {r C : Nat} (hr : 2 ≤ r) (hodd : r % 2 = 1)
    (hD : D (r - 1) = C) : d r ∣ C + 1 ∧ d r ∣ r - 2 := by
  have hmap := constant_D_event_map (r := r) (C := C) hr hD
  have hne : ¬ r % 2 = 0 := by rw [hodd]; exact Nat.one_ne_zero
  rw [hmap, if_neg hne]
  exact ⟨Nat.gcd_dvd_right _ _, Nat.gcd_dvd_left _ _⟩

/-- **Even-branch divisor node.**  At an even index `r` whose predecessor has
`D (r-1) = C`, the event value divides both `C - 1` and `r`. -/
theorem even_event_value_dvd {r C : Nat} (hr : 2 ≤ r) (heven : r % 2 = 0)
    (hD : D (r - 1) = C) : d r ∣ C - 1 ∧ d r ∣ r := by
  have hmap := constant_D_event_map (r := r) (C := C) hr hD
  rw [hmap, if_pos heven]
  exact ⟨Nat.gcd_dvd_right _ _, Nat.gcd_dvd_left _ _⟩

/-- **Index lower bound at an odd event.**  A nontrivial odd-branch event value
`d r` satisfies `d r + 2 ≤ r`: the value divides `r - 2`. -/
theorem odd_event_value_add_two_le_index {r C : Nat} (hr : 2 ≤ r)
    (hodd : r % 2 = 1) (hD : D (r - 1) = C) (h1 : 1 < d r) :
    d r + 2 ≤ r := by
  obtain ⟨k, hk⟩ := (odd_event_value_dvd hr hodd hD).2
  have hsub : r - 2 + 2 = r := Nat.sub_add_cancel hr
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk
      omega
    · exact h
  calc d r + 2 ≤ d r * k + 2 := by
        have : d r * 1 ≤ d r * k := Nat.mul_le_mul_left (d r) hk1
        omega
    _ = (r - 2) + 2 := by rw [← hk]
    _ = r := hsub

/-- **Record value bound at an odd occurrence.**  A nontrivial record `R > 5`
occurring at an odd index `r` satisfies `R ≤ D (r-1) + 1`; equivalently
`D (r-1) ≡ -1 (mod R)`.  This is the D-coordinate form of Shevelev's
`q ∣ (C + 1)` step. -/
theorem odd_record_value_le_D_add_one {R r : Nat} (hR : 5 < R) (hr : 2 ≤ r)
    (hodd : r % 2 = 1) (hd : d r = R) : R ≤ D (r - 1) + 1 := by
  have hdvd := (odd_event_value_dvd (C := D (r - 1)) hr hodd rfl).1
  rw [hd] at hdvd
  exact Nat.le_of_dvd (Nat.succ_pos _) hdvd

end A166944Research
