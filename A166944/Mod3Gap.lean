import A166944.Lemmas
import A166944.FirstHitForm

/-!
# A factor of 3 in the horizon forces a short gap

Measured over 362 steps at all certified records, ZERO exceptions:

    if `3` divides the term the step's own branch tests, then `gap <= 6`.

The mechanism is `FirstHitForm.step_is_first_gcd_hit`, which is exactly the MINIMALITY of the
event index: no `j` with `s < j < r` passes the gcd test.  So it suffices to exhibit one
admissible `j <= s + 6`, because then `r <= j <= s + 6`.

* Even branch (`3 | C - 1`): among any six consecutive integers there is an even multiple of
  `6`, hence an even `j` with `3 | j`, and then `gcd j (C-1) >= 3 > 1`.
* Odd branch (`3 | C + 1`): among any six consecutive integers there is `j ≡ 5 (mod 6)`, so
  `j` is odd and `3 | j - 2`, and then `gcd (j-2) (C+1) >= 3 > 1`.

This file proves the case extraction and the arithmetic; the container statements about six
consecutive integers are the two lemmas `exists_even_multiple_of_three` and
`exists_odd_two_less_multiple_of_three` below, which are pure `Nat` arithmetic.

Pure core: `omega` / `Nat.dvd_sub` / `Nat.dvd_add` / `decide`.
-/

namespace A166944Research

/-- **Six consecutive integers contain an even multiple of 3.**  Case analysis on
`s = 6k + c`; each witness is fully concrete so `omega` closes it. -/
theorem exists_even_multiple_of_three (s : Nat) :
    ∃ j : Nat, s < j ∧ j ≤ s + 6 ∧ j % 2 = 0 ∧ 3 ∣ j := by
  obtain ⟨k, c, hk, hc⟩ : ∃ k c, s = 6 * k + c ∧ c < 6 :=
    ⟨s / 6, s % 6, by omega, Nat.mod_lt _ (by decide : 0 < 6)⟩
  rw [hk]
  clear hk
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 by omega)
    with r | r | r | r | r | r
  · subst r; exact ⟨6 * k + 6, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩
  · subst r; exact ⟨6 * k + 1 + 5, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩
  · subst r; exact ⟨6 * k + 2 + 4, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩
  · subst r; exact ⟨6 * k + 3 + 3, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩
  · subst r; exact ⟨6 * k + 4 + 2, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩
  · subst r; exact ⟨6 * k + 5 + 1, by omega, by omega, by omega, ⟨2 * k + 2, by omega⟩⟩

/-- **Six consecutive integers contain an odd `j` with `3 | j - 2`.** -/
theorem exists_odd_two_less_multiple_of_three (s : Nat) :
    ∃ j : Nat, s < j ∧ j ≤ s + 6 ∧ j % 2 = 1 ∧ 3 ∣ j - 2 := by
  obtain ⟨k, c, hk, hc⟩ : ∃ k c, s = 6 * k + c ∧ c < 6 :=
    ⟨s / 6, s % 6, by omega, Nat.mod_lt _ (by decide : 0 < 6)⟩
  rw [hk]
  clear hk
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 by omega)
    with r | r | r | r | r | r
  · subst r; exact ⟨6 * k + 5, by omega, by omega, by omega, ⟨2 * k + 1, by omega⟩⟩
  · subst r; exact ⟨6 * k + 1 + 4, by omega, by omega, by omega, ⟨2 * k + 1, by omega⟩⟩
  · subst r; exact ⟨6 * k + 2 + 3, by omega, by omega, by omega, ⟨2 * k + 1, by omega⟩⟩
  · subst r; exact ⟨6 * k + 3 + 2, by omega, by omega, by omega, ⟨2 * k + 1, by omega⟩⟩
  · subst r; exact ⟨6 * k + 4 + 1, by omega, by omega, by omega, ⟨2 * k + 1, by omega⟩⟩
  · subst r; exact ⟨6 * k + 5 + 6, by omega, by omega, by omega, ⟨2 * k + 3, by omega⟩⟩

/-- **Even branch.**  If `3 | C - 1` then the gap is at most 6. -/
theorem gap_le_six_of_three_dvd_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 0) (h3 : 3 ∣ C - 1) : r - s ≤ 6 := by
  rcases Nat.lt_or_ge (r - s) 7 with hlt | hge
  · omega
  · exfalso
    obtain ⟨j, hsj, hjs, hje, hj3⟩ := exists_even_multiple_of_three s
    have hjr : j < r := by omega
    have hres := (step_is_first_gcd_hit hstep hDconst).2 j hsj hjr
    rw [if_pos (by omega : j % 2 = 0)] at hres
    have hd : 3 ∣ Nat.gcd j (C - 1) := Nat.dvd_gcd hj3 h3
    have hgpos : 0 < Nat.gcd j (C - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    obtain ⟨m, hm⟩ := hd
    omega

/-- **Odd branch.**  If `3 | C + 1` then the gap is at most 6. -/
theorem gap_le_six_of_three_dvd_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C)
    (hr : r % 2 = 1) (h3 : 3 ∣ C + 1) : r - s ≤ 6 := by
  rcases Nat.lt_or_ge (r - s) 7 with hlt | hge
  · omega
  · exfalso
    obtain ⟨j, hsj, hjs, hje, hj3⟩ := exists_odd_two_less_multiple_of_three s
    have hjr : j < r := by omega
    have hres := (step_is_first_gcd_hit hstep hDconst).2 j hsj hjr
    rw [if_neg (by omega : ¬ j % 2 = 0)] at hres
    have hd : 3 ∣ Nat.gcd (j - 2) (C + 1) := Nat.dvd_gcd hj3 h3
    have hgpos : 0 < Nat.gcd (j - 2) (C + 1) := by
      have : 0 < C + 1 := by omega
      exact Nat.gcd_pos_of_pos_right _ this
    obtain ⟨m, hm⟩ := hd
    omega

/-! ## Axiom audit -/

#print axioms exists_even_multiple_of_three
#print axioms exists_odd_two_less_multiple_of_three
#print axioms gap_le_six_of_three_dvd_even
#print axioms gap_le_six_of_three_dvd_odd

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build matching CI: exit 0, 0 errors, 0 warnings, no `sorry`/`admit`/`axiom`; all
four declarations audit to `[propext, Quot.sound]`.

Measured over 362 steps at all certified records with ZERO exceptions: whenever `3` divides the
term the step's own branch tests, the gap is at most 6 (343/343 on the even branch, 19/19 on
the odd). That is the statement proved here.

The proof is not the tree's `gap <= 2v` (which would need `3` to divide the EVENT VALUE, and
`3 | C -+ 1` does not force that). It is MINIMALITY of the event index
(`FirstHitForm.step_is_first_gcd_hit`): no `j` with `s < j < r` passes the gcd test, so it
suffices to exhibit one admissible `j <= s + 6`. On the even branch any even multiple of 3
works, and among six consecutive integers one always exists; on the odd branch take `j` odd
with `3 | j - 2`. Both are `Nat` arithmetic with concrete witnesses, no division.

What this does NOT give, stated so the next attempt does not mistake one for the other:
`gap <= 6` holds at 573/908 measured steps (63.1%), so short gaps are the MAJORITY, and yet
`travel <= M/2` still needs a proof. Bounding the small gaps does not bound the SUM, because
the large gaps dominate it: at `M = 22933441` the 137 short gaps contribute at most
`6*137 = 822` while `travel` is 14343, so over 94% of the travel sits in the 72 gaps above 6.
This file therefore supplies a clean composable per-step bound and NOT the frontier.
-/
