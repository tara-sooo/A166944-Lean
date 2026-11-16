/-
# Route B — the six-cover count (Lemma B1)

Frozen statement of the frontier lemma plus the fragments that are genuinely
provable in this tree.

## Environment note (important, and pre-existing)

`A166944.TravelTarget` cannot be checked in this container: it imports
`A166944.TargetDefs`, which imports `Mathlib.Data.Nat.Prime.Defs`, and the local
Mathlib build is missing the `.olean.server` companion of essentially every
module (1 of 8322 present). The failure reproduces on the repository's own
`A166944/TravelTarget.lean`, so it is not caused by this file. A second,
narrower trap: `A166944.Isqrt` must be imported EXPLICITLY, because the
prebuilt `A166944/TravelResidues.olean` is older than `Isqrt.lean` and does not
re-export `isqrt`.

This file therefore imports the largest **core-only** module that carries the
material, `A166944.TravelResidues` (plus `A166944.Isqrt`), and states the frozen
hypothesis with the primality conjunct carried as a hypothesis instead of
through `IsGreaterTwinPrime`. That is logically the same proposition; the
verbatim form is recorded at the end of this file.

## Contents

* `six_dvd_D_iff_three_dvd_D` — `6 | D j <-> 3 | D j` for `2 <= j` (`D` even).
  This is what makes B1 a mod-3 statement, not a factorisation statement.
* `exists_six_cover_length_le_p` — **the main provable fragment.** There is a
  cover of length `<= p`.
* `budget_of_cover_le_p` / `exists_six_cover_of_p_bound` — the reduction of the
  consumer's budget to the scalar bound `(L)` on `p` alone.
* `cover_length_le_p_not_forced_by_containment` — why `cover <= p` does NOT
  follow from the consumer's hypothesis as stated.
-/
import A166944.Isqrt
import A166944.TravelResidues

namespace A166944Research

/-! ## 0. The frozen statement (do not weaken)

`Twin` abstracts the primality conjunct `IsGreaterTwinPrime` so the statement is
checkable on the core-only path; instantiating `Twin := IsGreaterTwinPrime`
recovers the verbatim frozen hypothesis exactly. Nothing else is abstracted. -/

/-- **Lemma B1, frozen.** The six-cover count bound, in the exact shape the
consumer needs. -/
def LemmaB1Frozen (Twin : Nat → Prop) : Prop :=
  ∀ {M sf Cf p : Nat}, 45895573 ≤ M → Twin M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    IsAttainedPreviousMaximum M sf →
    ∀ cover : List Nat,
      (∀ j : Nat, IsReplayEventStart (M + 2) sf j → 6 ∣ D j → j ∈ cover) →
      cover.length ≤ (M / 2 - 6 * p) / (isqrt (4 * (3 * M + 4)) - 6)

/-- The mod-3 form of the frozen statement: since `D` is even, the covered set is
`{j : IsReplayEventStart (M+2) sf j ∧ 3 ∣ D j}`. Same bound. -/
def LemmaB1FrozenModThree (Twin : Nat → Prop) : Prop :=
  ∀ {M sf Cf p : Nat}, 45895573 ≤ M → Twin M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    IsAttainedPreviousMaximum M sf →
    ∀ cover : List Nat,
      (∀ j : Nat, IsReplayEventStart (M + 2) sf j → 3 ∣ D j → j ∈ cover) →
      cover.length ≤ (M / 2 - 6 * p) / (isqrt (4 * (3 * M + 4)) - 6)

/-! ## 1. `6 | D j` is exactly `3 | D j` -/

/-- `D` is even at every index `>= 2`. -/
theorem six_cover_D_mod_two {j : Nat} (hj : 2 ≤ j) : D j % 2 = 0 :=
  D_mod_two_eq_zero_of_two_le hj

/-- **The bridge that makes B1 a mod-3 statement.** For `2 <= j`,
`6 | D j` iff `3 | D j`, because `D j` is even. Divisibility by six is
therefore not a new arithmetic condition on the recurrence: it is exactly
divisibility by three. -/
theorem six_dvd_D_iff_three_dvd_D {j : Nat} (hj : 2 ≤ j) :
    6 ∣ D j ↔ 3 ∣ D j := by
  have h2 : D j % 2 = 0 := D_mod_two_eq_zero_of_two_le hj
  constructor
  · intro h
    exact Nat.dvd_trans (by decide : 3 ∣ 6) h
  · intro h
    obtain ⟨k, hk⟩ := h
    have hk2 : k % 2 = 0 := by omega
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hk2
    exact ⟨m, by omega⟩

/-- The consumer's covered set is a mod-3 set, on any replay window that starts
at or after index `2`. -/
theorem cover_is_three_dvd_set {s sf j : Nat} (hs : 2 ≤ s)
    (hj : IsReplayEventStart s sf j) : (6 ∣ D j) ↔ (3 ∣ D j) :=
  six_dvd_D_iff_three_dvd_D (by have := hj.1; omega)

/-- **The two frozen forms are equivalent.** Because `D` is even at every index
`>= 2` and every replay start is `>= 2`, the six-divisibility cover hypothesis
and the three-divisibility cover hypothesis define exactly the same family of
admissible covers. -/
theorem lemmaB1Frozen_iff_modThree (Twin : Nat → Prop) :
    LemmaB1Frozen Twin ↔ LemmaB1FrozenModThree Twin := by
  constructor
  · intro h M sf Cf p hM ht hd hp hmax cover hcov
    exact h hM ht hd hp hmax cover
      (fun j hj h6 => hcov j hj
        ((six_dvd_D_iff_three_dvd_D
          (Nat.le_trans (by omega : 2 ≤ M + 2) hj.1)).mp h6))
  · intro h M sf Cf p hM ht hd hp hmax cover hcov
    exact h hM ht hd hp hmax cover
      (fun j hj h3 => hcov j hj
        ((six_dvd_D_iff_three_dvd_D
          (Nat.le_trans (by omega : 2 ≤ M + 2) hj.1)).mpr h3))

/-! ## 2. A cover of length at most `p` exists -/

/-- **The main provable fragment.** For any genuine path there is a cover of
length at most the step count `p` which contains every event start `j < sf`
with `6 | D j`.

Construction: at each step keep the state index `s` when `6 | D s`, and hand the
rest to the tail. The one substantive point is that an event start `j` with
`s < j` never lies strictly inside the searched window `(s, r)`, because every
index there has `d = 1`; hence `r <= j` and the tail's induction hypothesis
applies to `j`. -/
theorem exists_six_cover_length_le_p {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ cover : List Nat,
      cover.length ≤ p ∧
        ∀ j : Nat, IsReplayEventStart s sf j → 6 ∣ D j → j ∈ cover := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, _, _⟩ := hpath
      refine ⟨[], Nat.le_refl 0, ?_⟩
      intro j hj _
      obtain ⟨hjs, hjsf, _⟩ := hj
      omega
  | succ q ih =>
      obtain ⟨hstate, r, C', hstep, htail⟩ := hpath
      obtain ⟨cover', hlen', hmem'⟩ := ih htail
      have hDs : D s = C := hstate.2.1
      -- every index strictly inside the searched window has d = 1
      have hshift : ∀ j : Nat, s < j → j < r → d j = 1 := hstep.2.2.2.2.1
      by_cases hsix : 6 ∣ C
      · refine ⟨s :: cover', by simp only [List.length_cons]; omega, ?_⟩
        intro j hj hdiv
        obtain ⟨hjs, hjsf, hje | hje⟩ := hj
        · exact hje ▸ List.mem_cons_self
        · by_cases hjeq : j = s
          · exact hjeq ▸ List.mem_cons_self
          · have hslt : s < j := by omega
            have hrj : r ≤ j := by
              by_cases h : r ≤ j
              · exact h
              · have hone := hshift j hslt (by omega)
                omega
            exact List.mem_cons_of_mem s (hmem' j ⟨hrj, hjsf, Or.inr hje⟩ hdiv)
      · refine ⟨cover', by omega, ?_⟩
        intro j hj hdiv
        obtain ⟨hjs, hjsf, hje | hje⟩ := hj
        · exact absurd (hDs ▸ hje ▸ hdiv) hsix
        · by_cases hjeq : j = s
          · exact absurd (hDs ▸ hjeq ▸ hdiv) hsix
          · have hslt : s < j := by omega
            have hrj : r ≤ j := by
              by_cases h : r ≤ j
              · exact h
              · have hone := hshift j hslt (by omega)
                omega
            exact hmem' j ⟨hrj, hjsf, Or.inr hje⟩ hdiv

/-! ## 3. The budget reduction -/

/-- If the cover count is at most `p`, the consumer's budget follows from the
scalar bound `(L)` on `p` alone. -/
theorem budget_of_cover_le_p {M p covlen : Nat}
    (hL : 2 * (6 * p + p * (isqrt (4 * (3 * M + 4)) - 6)) ≤ M)
    (hle : covlen ≤ p) :
    2 * (6 * p + covlen * (isqrt (4 * (3 * M + 4)) - 6)) ≤ M := by
  have hmono : covlen * (isqrt (4 * (3 * M + 4)) - 6)
      ≤ p * (isqrt (4 * (3 * M + 4)) - 6) :=
    Nat.mul_le_mul_right _ hle
  omega

/-- **The honest reduction of Route B.** The scalar bound

    `(L)  2 * (6 * p + p * (isqrt (4 * (3 * M + 4)) - 6)) <= M`

implies the consumer's six-cover hypothesis at that record. So B1-as-consumed
follows from `(L)`, and the mod-3 dynamics are not needed for this step. -/
theorem exists_six_cover_of_p_bound {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hL : 2 * (6 * p + p * (isqrt (4 * (3 * M + 4)) - 6)) ≤ M) :
    ∃ cover : List Nat,
      (∀ j : Nat, IsReplayEventStart (M + 2) sf j → 6 ∣ D j → j ∈ cover) ∧
        2 * (6 * p + cover.length * (isqrt (4 * (3 * M + 4)) - 6)) ≤ M := by
  obtain ⟨cover, hlen, hmem⟩ := exists_six_cover_length_le_p hpath
  exact ⟨cover, hmem, budget_of_cover_le_p hL hlen⟩

/-! ## 3b. What IS provable about the mod-3 dynamics

The measured mod-3 dynamics are the object B1 would have to bound. Two things
are provable from the tree's step law, and they are recorded here because they
are the only local mod-3 facts available.

Measured transition table of `D % 3` at consecutive event starts
(the `0.43 / 0.90` split, from 921 transitions up to `M = 91793059`):

    P(D' % 3 = 0 | D % 3 = 0) = 0.4304        P(D' % 3 = 0 | D % 3 = 1) = 0.8997

so the process ANTI-persists: conditional on `3 | D` it is *less* likely to stay
divisible by three than to become so. The effect is real and survives a
scrambled control (see REPORT.md), but it is a *statistical* statement, not a
local one, and it is what makes a naive "once divisible, stays divisible"
density argument impossible. -/

/-- **Provable mod-3 step law.** Along a step, if both the horizon and the next
horizon are divisible by three then the increment satisfies `3 | (d r - 1)`;
equivalently, `3 | d r - 1` is forced whenever divisibility by three propagates.
This is immediate from the tree's step law `C' = C + (d r - 1)` and is the only
local mod-3 propagation fact available. -/
theorem three_dvd_increment_sub_one_of_propagates {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hC : 3 ∣ C) (hC' : 3 ∣ C') :
    3 ∣ (d r - 1) := by
  have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
  omega

/-- Contrapositive form, matching the measurement that `3 | C` and `3 | C'` are
NOT independent: divisibility by three and `d r ≡ 1 (mod 3)` travel together. -/
theorem not_three_dvd_increment_sub_one_of_not_propagates {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hC : 3 ∣ C)
    (hinc : ¬ 3 ∣ (d r - 1)) : ¬ 3 ∣ C' := by
  intro hC'
  exact hinc (three_dvd_increment_sub_one_of_propagates hstep hC hC')

/-! ## 4. Why `cover <= p` is not forced by containment -/

/-- The trivial cover `List.range sf` satisfies the containment. This is why
containment alone cannot bound `cover.length`: `hcover` is a LOWER bound on the
cover. -/
theorem range_is_a_cover {s sf : Nat} :
    ∀ j : Nat, IsReplayEventStart s sf j → 6 ∣ D j → j ∈ List.range sf := by
  intro j hj _
  exact List.mem_range.2 hj.2.1

/-- **The reduction cannot be read off the hypothesis.** There is a cover which
satisfies the consumer's containment and whose length exceeds any small `p`. The
hypothesis is an existential over covers and only says that `cover` CONTAINS the
covered set, so "cover is a subset of the event states" does not bound
`cover.length`. What is true is that *some* cover of length `<= p` exists
(`exists_six_cover_length_le_p`), which is what the existential consumer needs. -/
theorem cover_length_le_p_not_forced_by_containment :
    ∃ cover : List Nat,
      (∀ j : Nat, IsReplayEventStart 3 100 j → 6 ∣ D j → j ∈ cover) ∧
        ¬ cover.length ≤ 3 :=
  ⟨List.range 100, range_is_a_cover, by decide⟩

end A166944Research

#print axioms A166944Research.lemmaB1Frozen_iff_modThree
#print axioms A166944Research.six_cover_D_mod_two
#print axioms A166944Research.six_dvd_D_iff_three_dvd_D
#print axioms A166944Research.cover_is_three_dvd_set
#print axioms A166944Research.exists_six_cover_length_le_p
#print axioms A166944Research.budget_of_cover_le_p
#print axioms A166944Research.exists_six_cover_of_p_bound
#print axioms A166944Research.three_dvd_increment_sub_one_of_propagates
#print axioms A166944Research.not_three_dvd_increment_sub_one_of_not_propagates
#print axioms A166944Research.range_is_a_cover
#print axioms A166944Research.cover_length_le_p_not_forced_by_containment

/-
## The verbatim frozen statement (blocked by the broken Mathlib build)

The consumer `record_index_and_twin_prime_of_six_cover_from_45895573` takes

    hcover : forall {M sf Cf p}, 45895573 <= M -> IsGreaterTwinPrime M ->
      d (M+2) = M -> HasMovingHorizonPathTo (M+2) (2*M-2) sf Cf p ->
      IsAttainedPreviousMaximum M sf ->
      exists cover : List Nat,
        (forall j, IsReplayEventStart (M+2) sf j -> 6 | D j -> j in cover) /\
        2 * (6*p + cover.length * (isqrt (4*(3*M+4)) - 6)) <= M

Lemma B1 is the count bound which instantiates it:

    cover.length <= (M/2 - 6*p) / (isqrt (4*(3*M+4)) - 6)

`IsGreaterTwinPrime p := p.Prime /\ (p-2).Prime` is defined in
`A166944/TargetDefs.lean`; it needs `Mathlib.Data.Nat.Prime.Defs`, which is the
import this container cannot load. The statements above are the same
propositions with that conjunct carried as a hypothesis; nothing is weakened.
-/

/-!
## Verified status (2026-11-16)

Core-only build: exit 0, no `sorry`, no `admit`, no new `axiom`, every declaration
audits to `[propext, Quot.sound]`.

The frozen statement is `LemmaB1Frozen` (and its mod-3 equivalent).  It is NOT
proved.  What IS proved here is the reduction that makes the route need only the
scalar bound `(L)`: `exists_six_cover_length_le_p` shows a cover of length `<= p`
exists, and `exists_six_cover_of_p_bound` shows `(L)` implies the consumer's
hypothesis.  `range_is_a_cover` and `cover_length_le_p_not_forced_by_containment`
record that the containment hypothesis alone does NOT bound the cover length.
-/
