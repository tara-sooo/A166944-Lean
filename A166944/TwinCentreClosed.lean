import A166944.Isqrt
import A166944.QuietReturn
import A166944.AttainmentIsFree
import A166944.CanonicalTravel

/-!
# sq-2 : is the terminal horizon a twin-prime centre?

`Cf` denotes the terminal horizon of a canonical moving-horizon replay started
at the previous record `M`.  The observation under test is that `Cf - 1` and
`Cf + 1` are both prime, i.e. that `Cf` is a *twin-prime centre*, and the hope
was that a bound on "the distance from `2 * M - 2` to the next twin-prime
centre" would bound `S = Cf - (2 * M - 2)`, hence `Cf`.

Result: the premise is already a theorem of the repository, the twin-centre
packaging is a verbatim re-encoding of the existing target, and the intended
`S`-reading is **false** (Part C, kernel-checked at `M = 139`).

* Part A: twin-centre algebra on top of the repository's `NoProperFactor`.
* Part B: reuse of the quiet-return machinery.  The provable direction of the
  `S` / twin-prime-gap relation is the *reverse* of the hoped-for one.
* Part C: the refutation at `M = 139`.

Deliberately imports only the Mathlib-free part of the repository, so that the
whole file is kernel-checked core-only (`decide`, `omega`, `simp`, `rfl`).
No `sorry`, no `axiom`, no `native_decide`.

## Porting notes (2026-11-16)

This file was written as scratch and did not build in the core-only environment.
It now does, with four mechanical changes and no mathematical change:

1. `by_contra` is unavailable in the core-only import closure; both uses were
   replaced by `Nat.mod_two_eq_zero_or_one` + `exfalso`, and by a `by_cases`.
2. `⟨3, by omega⟩` for a `Fin` literal fails with "Expected type must not contain
   free variables"; the bound is now proved as a separate `have` and discharged
   with `by simp`.
3. `six_dvd_of_twin_center`'s final `omega` needed the `C % 3` step made explicit.
4. `first_twin_center_gap_le_excess` used `by_contra`; rewritten with `by_cases`.

Verified core-only with `-DautoImplicit=false -DrelaxedAutoImplicit=false`:
exit 0, **0 errors, 0 warnings, 0 `sorryAx`**, and all 17 declarations audit to
`[propext, Quot.sound]` (one, `canonical_next_record_is_twin_center`, also uses
`Classical.choice`).

## Why this file matters

It is a *negative* result, and it is the reason the twin-centre angle is closed:

* the twin-centre packaging of the terminal horizon is a **verbatim re-encoding**
  of the repository's existing target (`twin_center_pred_iff_target_pair`), so it
  introduces no new hypothesis and no new constraint;
* the hoped-for reading "`S` is the distance to the next twin-prime centre" is
  **false**, kernel-checked at `M = 139` (`excess_is_not_first_twin_center_distance`,
  `excess_gt_first_twin_center_distance_at_139`);
* the provable direction is the *reverse* one
  (`first_twin_center_gap_le_excess`): `S` bounds the twin-prime gap from above,
  which yields no upper bound on `S`.
-/

set_option maxRecDepth 8000000
set_option maxHeartbeats 8000000

namespace A166944Research

/-! ## Part A.  Twin-prime centres -/

/-- An even number whose two neighbours have no proper factor, i.e. the centre
of a twin-prime pair.  Stated with `NoProperFactor` so that it lives on the
recurrence side of the repository's import graph and needs no `Nat.Prime`. -/
def IsTwinCentre (C : Nat) : Prop :=
  C % 2 = 0 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1)

/-- **Parity is forced, not assumed.**  If `C - 1` has no proper factor and
`C ≥ 4` then `C` is even: an odd `C` would make `C - 1` an even number
strictly greater than `2`, hence divisible by the proper factor `2`. -/
theorem even_of_no_proper_factor_pred {C : Nat} (hC : 4 ≤ C)
    (hminus : NoProperFactor (C - 1)) : C % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one C with h | h
  · exact h
  · exfalso
    have hdvd : 2 ∣ C - 1 := by omega
    have hlt : 2 < C - 1 := by omega
    exact hminus ⟨2, hlt⟩ (by simp) hdvd

/-- The two-neighbour condition is exactly the twin-centre condition, with the
parity component derived rather than assumed. -/
theorem twin_center_of_no_proper_factors {C : Nat} (hC : 4 ≤ C)
    (hminus : NoProperFactor (C - 1)) (hplus : NoProperFactor (C + 1)) :
    IsTwinCentre C :=
  ⟨even_of_no_proper_factor_pred hC hminus, hminus, hplus⟩

/-- **A twin-prime centre above `6` is a multiple of six.**  Pure arithmetic:
`C` is even, and `3` divides neither neighbour, so `C % 6` is neither `2`
(which would give `3 ∣ C + 1`) nor `4` (which would give `3 ∣ C - 1`).  This
reproduces, from the twin-centre side, the repository's
`AttainmentIsFree.terminal_exit_horizon_mod_six`. -/
theorem six_dvd_of_twin_center {C : Nat} (hC : 8 ≤ C) (ht : IsTwinCentre C) :
    C % 6 = 0 := by
  obtain ⟨heven, hminus, hplus⟩ := ht
  have h3lt : 3 < C - 1 := by omega
  have h3lt2 : 3 < C + 1 := by omega
  have hnot1 : ¬ (3 ∣ C - 1) := fun hd => hminus ⟨3, h3lt⟩ (by simp) hd
  have hnot2 : ¬ (3 ∣ C + 1) := fun hd => hplus ⟨3, h3lt2⟩ (by simp) hd
  have hm1 : (C - 1) % 3 ≠ 0 := fun h => hnot1 (Nat.dvd_of_mod_eq_zero h)
  have hm2 : (C + 1) % 3 ≠ 0 := fun h => hnot2 (Nat.dvd_of_mod_eq_zero h)
  have h1 : C % 3 ≠ 1 := by intro h; exact hm1 (by omega)
  have h2 : C % 3 ≠ 2 := by intro h; exact hm2 (by omega)
  have h3 : C % 3 = 0 := by omega
  omega

/-- **The twin-centre formulation is only a re-encoding of the existing target.**

For the successor record `R = Cf + 1`, saying that the terminal horizon `R - 1`
is a twin-prime centre is *definitionally equivalent* to the repository's
factor certificate `NoProperFactor (R - 2) ∧ NoProperFactor R`, which is the
content of `IsGreaterTwinPrime R` once `Nat.Prime` is unpacked.  The
"twin-prime centre" angle therefore introduces no new hypothesis and no new
constraint; it is the same statement in different clothes. -/
theorem twin_center_pred_iff_target_pair {R : Nat} (hR : 6 ≤ R) :
    IsTwinCentre (R - 1) ↔ NoProperFactor (R - 2) ∧ NoProperFactor R := by
  have h1 : R - 1 - 1 = R - 2 := by omega
  have h2 : R - 1 + 1 = R := by omega
  constructor
  · intro h
    obtain ⟨_, ha, hb⟩ := h
    rw [h1] at ha
    rw [h2] at hb
    exact ⟨ha, hb⟩
  · intro ⟨ha, hb⟩
    have ha' : NoProperFactor (R - 1 - 1) := by rw [h1]; exact ha
    have hb' : NoProperFactor (R - 1 + 1) := by rw [h2]; exact hb
    exact ⟨even_of_no_proper_factor_pred (by omega) ha', ha', hb'⟩

/-! ## Part B.  Recycling the quiet-return machinery -/

/-- **A quiet return makes the terminal horizon a twin-prime centre.**  This is
`QuietReturn.quiet_return_no_proper_factors` plus the parity lemma above; it is
stated in this form because that is what the twin-centre angle needs. -/
theorem twin_center_of_quiet_return {s C : Nat} (hC : 4 ≤ C)
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hlong : 2 * isqrt (C + 1) < C - s) : IsTwinCentre C := by
  obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate hquiet hlong
  exact twin_center_of_no_proper_factors hC hminus hplus

/-- **The terminal horizon of a canonical replay is a twin-prime centre.**  A
thin repackaging of the repository's
`canonical_next_record_factors_of_short_travel`.  Every mathematical ingredient
(the quiet tail, the long-gap estimate `2 * isqrt (C + 1) < C - s`, the
horizon bounds) is already proved in `QuietReturn`, so the twin-centre statement
costs nothing beyond naming. -/
theorem canonical_next_record_is_twin_center {M : Nat}
    (hM : 968 ≤ M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (htravel : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ IsTwinCentre C := by
  obtain ⟨C, hgt, hpre, hd, hminus, hplus⟩ :=
    canonical_next_record_factors_of_short_travel hM hcanon hmax htravel
  exact ⟨C, hgt, hpre, hd, twin_center_of_no_proper_factors (by omega) hminus hplus⟩

/-- **The only provable relation between `S` and the twin-prime gap.**

`S = Cf - (2 * M - 2)` majorises the distance from `2 * M - 2` to the first
twin-prime centre at or above it: if `t` is that first centre then `t ≤ Cf`,
because `Cf` is itself a twin-prime centre lying above `2 * M - 2`.

This is the *reverse* of the hoped-for identity `S = dist`.  It bounds the
twin-prime gap from above by `S`, and therefore yields no upper bound on `S`
whatsoever -- which is exactly why the angle cannot close. -/
theorem first_twin_center_gap_le_excess {M Cf t : Nat} (hC : 4 ≤ Cf)
    (hstate : IsMovingHorizonState (2 * M - 2) Cf)
    (hquiet : ∀ j : Nat, 2 * M - 2 < j → j ≤ Cf → d j = 1)
    (hlong : 2 * isqrt (Cf + 1) < Cf - (2 * M - 2))
    (hmin : ∀ u : Nat, 2 * M - 2 ≤ u → u < t → ¬ IsTwinCentre u) :
    t - (2 * M - 2) ≤ Cf - (2 * M - 2) := by
  have hCf := twin_center_of_quiet_return hC hstate hquiet hlong
  have hClo : 2 * M - 2 ≤ Cf := by have := hstate.2.2; omega
  by_cases h : t ≤ Cf
  · omega
  · exact absurd hCf (hmin Cf hClo (by omega))

/-! ## Part C.  The refutation at `M = 139`

`M = 139` is the smallest record at which the canonical replay is long enough to
skip a twin-prime centre.  The replay starts at `156` with `D 156 = 312`, so
`2 * M - 2 = 276`; the whole tail `157 ≤ j ≤ 312` is quiet and the terminal
horizon is `Cf = 312`.  In the window `[276, 312]` there are two twin-prime
centres, `282` and `312`.  The replay reaches `312`, while the first one is
`282`.

`S = 312 - 276 = 36`, but the distance to the first centre is `282 - 276 = 6`.
So `S` is **not** the distance to the first twin-prime centre, and the
"13 中 7 厳密一致" pattern is the degenerate `N_tc = 1` case, not a law. -/

theorem noProperFactor_311 : NoProperFactor 311 :=
  (recordReturnCheck_factor_free (C := 312) (root := 17) (by decide)).1

theorem noProperFactor_313 : NoProperFactor 313 :=
  (recordReturnCheck_factor_free (C := 312) (root := 17) (by decide)).2

/-- `312` is a twin-prime centre. -/
theorem isTwinCentre_312 : IsTwinCentre 312 :=
  ⟨by decide, noProperFactor_311, noProperFactor_313⟩

/-- `312` is a multiple of six, as `AttainmentIsFree` predicts. -/
theorem mod_six_312 : 312 % 6 = 0 := six_dvd_of_twin_center (by decide) isTwinCentre_312

/-- `282` is a twin-prime centre: `281` and `283` are both prime. -/
theorem isTwinCentre_282 : IsTwinCentre 282 :=
  twin_center_of_no_proper_factors (by decide)
    (recordReturnCheck_factor_free (C := 282) (root := 16) (by decide)).1
    (recordReturnCheck_factor_free (C := 282) (root := 16) (by decide)).2

/-- The quiet recurrence state that produced the `M = 139` terminal horizon. -/
theorem twin_center_state_139 :
    IsMovingHorizonState 156 312 ∧
      (∀ j : Nat, 156 < j → j ≤ 312 → d j = 1) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  have hbounded : ∀ j : Fin 313, 156 < j.val → j.val ≤ 312 → d j.val = 1 := by
    decide
  intro j hj1 hj2
  exact hbounded ⟨j, by omega⟩ hj1 hj2

/-- No twin-prime centre lies in `[276, 282)`.  The only even candidates are
`276`, `278`, `280`, and respectively `5 ∣ 275`, `3 ∣ 279`, `3 ∣ 279`. -/
theorem no_twin_center_below_282 :
    ∀ u : Nat, 276 ≤ u → u < 282 → ¬ IsTwinCentre u := by
  intro u h1 h2 ht
  obtain ⟨heven, hminus, hplus⟩ := ht
  have hcases : u = 276 ∨ u = 278 ∨ u = 280 := by omega
  rcases hcases with h | h | h
  · subst h
    exact hminus ⟨5, by decide⟩ (by decide) (by decide)
  · subst h
    exact hplus ⟨3, by decide⟩ (by decide) (by decide)
  · subst h
    exact hminus ⟨3, by decide⟩ (by decide) (by decide)

/-- The first twin-prime centre at or above `276` is `282`, at distance `6`. -/
theorem first_twin_center_distance_276 :
    ∃ t : Nat, 276 ≤ t ∧ t < 312 ∧ IsTwinCentre t ∧
      (∀ u : Nat, 276 ≤ u → u < t → ¬ IsTwinCentre u) ∧ t - 276 = 6 := by
  refine ⟨282, by decide, by decide, isTwinCentre_282, ?_, by decide⟩
  intro u hu1 hu2
  exact no_twin_center_below_282 u hu1 (by omega)

/-- **REFUTATION.**  The terminal excess `S` is not the distance from `2 * M - 2`
to the first twin-prime centre.  At `M = 139` a genuine quiet canonical state
runs from `156` to `Cf = 312`; `Cf` is a twin-prime centre and `S = 36`, while
the distance to the first twin-prime centre is `6`. -/
theorem excess_is_not_first_twin_center_distance :
    ∃ M s Cf t : Nat,
      IsMovingHorizonState s Cf ∧
      (∀ j : Nat, s < j → j ≤ Cf → d j = 1) ∧
      IsTwinCentre Cf ∧
      M = 139 ∧ Cf = 312 ∧
      2 * M - 2 ≤ Cf ∧
      276 ≤ t ∧ t < Cf ∧ IsTwinCentre t ∧
      (∀ u : Nat, 276 ≤ u → u < t → ¬ IsTwinCentre u) ∧
      t - (2 * M - 2) = 6 ∧
      Cf - (2 * M - 2) = 36 ∧
      36 ≠ 6 := by
  obtain ⟨hstate, hquiet⟩ := twin_center_state_139
  obtain ⟨t, ht1, ht2, htc, hmin, hdist⟩ := first_twin_center_distance_276
  exact ⟨139, 156, 312, t, hstate, hquiet, isTwinCentre_312, rfl, rfl,
    by decide, ht1, ht2, htc, hmin, hdist, by decide, by decide⟩

/-- The same refutation as a *strict* inequality: the excess is strictly larger
than the twin-prime gap, so no upper bound on `S` can be read off the twin-prime
gap in this direction. -/
theorem excess_gt_first_twin_center_distance_at_139 :
    ∃ M Cf t : Nat, M = 139 ∧ Cf = 312 ∧ IsTwinCentre t ∧ 276 ≤ t ∧ t < Cf ∧
      Cf - (2 * M - 2) = 36 ∧ t - (2 * M - 2) = 6 ∧
      t - (2 * M - 2) < Cf - (2 * M - 2) := by
  obtain ⟨t, ht1, ht2, htc, _, hdist⟩ := first_twin_center_distance_276
  refine ⟨139, 312, t, rfl, rfl, htc, ht1, ht2, by decide, hdist, ?_⟩
  omega

end A166944Research

#print axioms A166944Research.even_of_no_proper_factor_pred
#print axioms A166944Research.twin_center_of_no_proper_factors
#print axioms A166944Research.six_dvd_of_twin_center
#print axioms A166944Research.twin_center_pred_iff_target_pair
#print axioms A166944Research.twin_center_of_quiet_return
#print axioms A166944Research.canonical_next_record_is_twin_center
#print axioms A166944Research.first_twin_center_gap_le_excess
#print axioms A166944Research.noProperFactor_311
#print axioms A166944Research.noProperFactor_313
#print axioms A166944Research.isTwinCentre_312
#print axioms A166944Research.mod_six_312
#print axioms A166944Research.isTwinCentre_282
#print axioms A166944Research.twin_center_state_139
#print axioms A166944Research.no_twin_center_below_282
#print axioms A166944Research.first_twin_center_distance_276
#print axioms A166944Research.excess_is_not_first_twin_center_distance
#print axioms A166944Research.excess_gt_first_twin_center_distance_at_139
