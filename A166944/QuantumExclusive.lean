import A166944.RoomQuantum
import A166944.RoomLedger
import A166944.BandReentry
import A166944.BandExcursion

set_option maxRecDepth 100000

/-!
# Round-5 red team on `RoomQuantum`

The module's claims are re-derived here from **pre-existing** September theorems, so
that "new structure" can be separated from "repackaging".  Every theorem below is
kernel-checked with `omega` / `simp` / `decide` / `rfl` only.
-/

namespace A166944Research

/-! ## 1. The quotient lower bound is NOT new

`RoomQuantum.lean`'s docstring and `ANALYSIS_WHY_STUCK.md` both assert that
"nothing in the library bounds that quotient [`(C +- 1) / e`] from below".  This is
false: `moving_horizon_step_event_package` (`Lemmas.lean:2848`, committed 2026-09-08)
already states `3 * d r <= C - 1` (even) / `3 * d r <= C + 1` (odd).  That *is* the
lower bound `3 <= (C +- 1) / d r`. -/

theorem quotient_ge_three_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) : 3 * d r ≤ C - 1 := by
  rcases moving_horizon_step_event_package hstep with h | h
  · exact h.2.2.2
  · exact absurd (h.1.symm.trans heven) (by decide)

theorem quotient_ge_three_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hodd : r % 2 = 1) : 3 * d r ≤ C + 1 := by
  rcases moving_horizon_step_event_package hstep with h | h
  · exact absurd (h.1.symm.trans hodd) (by decide)
  · exact h.2.2.2

/-- In quotient form: `(C - 1) / d r >= 3`, the exact statement the module says was
missing.  Proved from the September package theorem alone. -/
theorem quotient_div_ge_three_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) : 3 ≤ (C - 1) / d r := by
  have h3 : 3 * d r ≤ C - 1 := quotient_ge_three_even hstep heven
  have hpos : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  exact Nat.le_div_iff_mul_le hpos |>.2 (by simpa [Nat.mul_comm] using h3)

theorem quotient_div_ge_three_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hodd : r % 2 = 1) : 3 ≤ (C + 1) / d r := by
  have h3 : 3 * d r ≤ C + 1 := quotient_ge_three_odd hstep hodd
  have hpos : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  exact Nat.le_div_iff_mul_le hpos |>.2 (by simpa [Nat.mul_comm] using h3)

/-! ## 2. The even quantum is a two-line corollary of the September factor pair

`moving_horizon_even_factor_pair` (`Lemmas.lean:6547`, committed 2026-09-08) gives
`r = e * u`, `C - 1 = e * v`, `(v - u) % 2 = 1`, `1 <= v - u`, `C' = e * (v + 1)`.
Putting `d := v - u` (odd, `>= 1`) and `C' - r = e * (d + 1)`, the dichotomy
`room' = 2e  OR  4e <= room'` is immediate: `d = 1` gives `2e`, `d >= 3` gives `>= 4e`.
So the entire even-branch quantum was already available two months earlier. -/

theorem even_quantum_from_factor_pair {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) : C' - r = 2 * d r ∨ 4 * d r ≤ C' - r := by
  obtain ⟨u, v, hu, _hv, _hcop, hvupar, hvu1, hC'⟩ :=
    moving_horizon_even_factor_pair hstep rfl hr
  have hdr1 : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hle : u ≤ v := by omega
  have hsub : (v - u) + u = v := Nat.sub_add_cancel hle
  have hveq : v + 1 = u + ((v - u) + 1) := by omega
  have hsub1 : (v + 1) - u = (v - u) + 1 := by omega
  have hroom : C' - r = d r * ((v - u) + 1) := by
    have h1 : d r * (v + 1) = d r * u + d r * ((v - u) + 1) := by
      rw [← Nat.mul_add, ← hsub1, Nat.add_sub_of_le (by omega : u ≤ v + 1)]
    have h2 : C' - r = d r * (v + 1) - d r * u := by omega
    omega
  rcases Nat.eq_or_lt_of_le hvu1 with hone | hgt
  · left
    rw [hroom, ← hone]
    omega
  · right
    have h3 : 3 ≤ v - u := by omega
    have hmul : d r * 4 ≤ d r * ((v - u) + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The odd-branch quantum, likewise, from `moving_horizon_odd_factor_pair`
(`v - u` even and `>= 2`): `room' + 4 = e * (v + 1 - u)`, and `v + 1 - u` is odd and
`>= 3`, so it is `3` (giving `3e`) or `>= 5` (giving `>= 5e`). -/
theorem odd_quantum_from_factor_pair {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) : C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4 := by
  obtain ⟨u, v, hu, _hv, _hcop, hvupar, hvu2, hC'⟩ :=
    moving_horizon_odd_factor_pair hstep rfl hr
  have hdr1 : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hle : u ≤ v := by omega
  have hveq : v + 1 = u + ((v - u) + 1) := by omega
  have hsub1 : (v + 1) - u = (v - u) + 1 := by omega
  have hkey : C' + 2 - (r - 2) = d r * ((v - u) + 1) := by
    have h1 : d r * (v + 1) = d r * u + d r * ((v - u) + 1) := by
      rw [← Nat.mul_add, ← hsub1, Nat.add_sub_of_le (by omega : u ≤ v + 1)]
    have h2 : C' + 2 - (r - 2) = d r * (v + 1) - d r * u := by omega
    omega
  have hr2 : 2 ≤ r := by
    have := hstep.1.1
    have := hstep.2.1
    omega
  have hpost := hstep.2.2.2.2.2.2.2.2
  have hrC' : r < C' := hpost.2.2
  have hroom : C' - r + 4 = d r * ((v - u) + 1) := by omega
  rcases Nat.eq_or_lt_of_le hvu2 with htwo | hgt
  · left
    rw [hroom, ← htwo]
    omega
  · right
    have h4 : 4 ≤ v - u := by omega
    have hmul : d r * 5 ≤ d r * ((v - u) + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## 3. `e | room` is NOT unconditional

The module's §3 heading `moving_horizon_event_dvd_room_*` is accurate, but the
bundled reading "the event divides the room" is not: the odd branch divides
`room' + 4`, not `room'`.  The genuine `M = 13` first step is an explicit
counterexample to the unshifted form. -/

-- `d 17 = 5` already exists as `RoomLedger.d17_eq_five`.
theorem D17_eq_twentyeight : D 17 = 28 := by decide

/-- **`d 17` does not divide the room of the genuine step `15 24 17 28`.**
`room' = 28 - 17 = 11` and `5 ∤ 11`: an odd-branch step where `e | room'` fails. -/
theorem event_NOT_dvd_room_odd_counterexample : ¬ (d 17 ∣ (28 : Nat) - 17) := by
  rw [d17_eq_five]
  decide

/-- The odd branch forces `e | room' + 4` and `e` is odd, so `e | room'` would force
`e | 4`, hence `e = 1`, contradicting `3 <= e`.  So on every odd-branch step `e ∤
room'`: this is a *theorem*, not a coincidence. -/
theorem event_not_dvd_room_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hodd : r % 2 = 1) : ¬ (d r ∣ C' - r) := by
  intro hdiv
  have hshift : d r ∣ C' - r + 4 := moving_horizon_event_dvd_room_odd hstep hodd
  have h4 : d r ∣ 4 := by
    have := Nat.dvd_sub hshift hdiv
    simpa using this
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hle : d r ≤ 4 := Nat.le_of_dvd (by decide) h4
  have hodd' : d r % 2 = 1 := by
    have hr3 : 3 ≤ r := by
      have := hstep.1.1
      have := hstep.2.1
      omega
    exact d_mod_two_eq_one_of_three_le hr3
  have hdr3 : d r = 3 := by omega
  rw [hdr3] at h4
  exact absurd h4 (by decide)

/-! ## 4. `e | next horizon` has a shift of **two**, not one

The commit message for `a48f9e6` says the bundled lemma "gives `d r | C'' +- 1`".
The actual statement is `d r | C'` (even) and `d r | C' + 2` (odd): the shift is `0`
and `2`, never `1`.  The odd-branch shift of two is exactly the branch correction. -/

#check @moving_horizon_event_dvd_next_horizon

/-- On the odd branch the naive `d r | C'` is false: at the genuine step
`15 24 17 28` we have `d 17 = 5` and `5 ∤ 28`. -/
theorem event_not_dvd_next_horizon_odd_counterexample : ¬ (d 17 ∣ D 17) := by
  rw [d17_eq_five, D17_eq_twentyeight]
  decide

/-! ## 5. The dichotomy *is* exclusive on real steps -- but the theorem does not say so

Both even disjuncts hold exactly when `d r = 0`, which `3 <= d r` excludes; likewise
for the odd branch.  The exclusivity is therefore an extra input. -/

theorem even_branches_exclusive {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) : ¬ (C' - r = 2 * d r ∧ 4 * d r ≤ C' - r) := by
  intro h
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  omega

theorem odd_branches_exclusive {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) : ¬ (C' - r + 4 = 3 * d r ∧ 5 * d r ≤ C' - r + 4) := by
  intro h
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  omega

/-- The two branches are *not* the same quantum in unshifted coordinates: at the
smallest event value `e = 3` the odd branch permits `room' = 5*3 - 4 = 11` while the
even branch's off-pinned minimum is `4*3 = 12`. -/
theorem branches_have_different_thresholds : 5 * 3 - 4 = 11 ∧ 4 * 3 = 12 ∧ 11 < 12 := by
  decide

/-! ## 6. The consequence the module never states

Combining the dichotomy with the band condition `room' <= M` bounds the event value
by `M / 2` -- strictly better than the library's `d r <= M`.  This is the only place
the quantum has upward content, and `RoomQuantum.lean` does not record it. -/

theorem event_le_half_M_of_room_le {M s C r C' : Nat} (hM : 8 ≤ M)
    (hstep : IsMovingHorizonStep s C r C') (hband : C' - r ≤ M) : 2 * d r ≤ M := by
  rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
  · rcases moving_horizon_room_quantum_even hstep heven with h | h <;> omega
  · have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
    rcases moving_horizon_room_quantum_odd hstep hodd with h | h <;> omega

/-! ## 7. The pinned branch: exactly three steps in the whole range to `2 * 10 ^ 6` -/

theorem m13_step0_odd_pinned :
    (28 : Nat) - 17 + 4 = 3 * 5 ∧ ¬ (5 * 5 ≤ (28 : Nat) - 17 + 4) := by
  constructor <;> decide

theorem m13_step1_even_pinned :
    (36 : Nat) - 18 = 2 * 9 ∧ ¬ (4 * 9 ≤ (36 : Nat) - 18) := by
  constructor <;> decide

theorem m43_step4_even_pinned :
    (132 : Nat) - 66 = 2 * 33 ∧ ¬ (4 * 33 ≤ (132 : Nat) - 66) := by
  constructor <;> decide

/-- `M = 139` has no pinned step: both steps are strictly off the first branch. -/
theorem m139_no_pinned :
    ¬ ((150 : Nat) = 2 * 25) ∧ 4 * 25 ≤ (150 : Nat) ∧
      ¬ ((156 : Nat) = 2 * 13) ∧ 4 * 13 ≤ (156 : Nat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- A single pinned step at `M = 43` already exceeds the whole per-record budget
`(3 * 43 - 9) / 8 = 15`: `33 > 15`.  So the pinned branch is where the barrier lives. -/
theorem m43_pinned_event_beats_budget : (3 * 43 - 9) / 8 = 15 ∧ 15 < 33 := by
  constructor <;> decide

/-! ## 8. The pinned even branch is prior art (2026-09-07) -/

theorem pinned_even_is_prior_art {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hnew : P < d r) (hPodd : P % 2 = 1) :
    C' - r = 2 * d r :=
  (moving_horizon_normalized_new_max_even hstep hnorm hnew hPodd).2

end A166944Research
