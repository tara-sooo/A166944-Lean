import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Basic sum bounds: a family of terms each `≤ X` sums to at most `X * length`

These are elementary, and they are the workhorse for bounding `Σ min_lpf` (the quantity `L` in
Route A) once a per-term bound is known. Obtained by searching Mathlib with `apply?`, which pointed
at `List.sum_le_max_mul_length_of_max?_eq_some_nat`; the general hypothesis form
`∀ x ∈ l, x ≤ X` is proved here because the `max?` form requires an exact maximum.

## Why this is the right shape for Route A

`RouteAMinFac.min_lpf_le_sqrt_of_composite` gives a per-step bound `min_lpf ≤ Nat.sqrt (C+1)`, and
`RouteAMinFac.minFac_sq_le` gives `minFac² ≤ n`. To turn either into a bound on `L = Σ min_lpf`
one needs exactly this lemma. Measured, `Σ min_lpf` is at most `p * sqrt (2M)`, and `4L ≤ M` then
requires `p ≤ 0.177 √M` -- three certified records violate that, which is where Route A currently
stops.

## Axiom note

BOTH declarations audit to `[propext, Classical.choice, Quot.sound]`. The `Classical.choice`
comes from `nlinarith` (used in the inductive steps), not from the statements; the List version was
expected to avoid it but does not, because `nlinarith` is imported by `Mathlib.Tactic`. For a
choice-free version, replace `nlinarith` with explicit `omega` on the stated product identity.
-/

theorem list_sum_le_mul_length (l : List ℕ) (X : ℕ) (h : ∀ x ∈ l, x ≤ X) :
    l.sum ≤ X * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a ≤ X := h a (by simp)
      have ht : ∀ x ∈ t, x ≤ X := fun x hx => h x (by simp [hx])
      have ih' := ih ht
      simp only [List.sum_cons, List.length_cons]
      nlinarith

theorem finset_sum_le_mul_card (s : Finset ℕ) (X : ℕ) (h : ∀ x ∈ s, x ≤ X) :
    s.sum id ≤ X * s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hat : ∀ x ∈ t, x ≤ X := fun x hx => h x (by simp [hx])
      have ha' : a ≤ X := h a (by simp)
      have ih' := ih hat
      have hsum : (insert a t).sum id = a + t.sum id := Finset.sum_insert ha
      have hcard : (insert a t).card = t.card + 1 := Finset.card_insert_of_notMem ha
      rw [hsum, hcard]
      nlinarith [ih', ha']

/-! ## Axiom audit -/

#print axioms list_sum_le_mul_length
#print axioms finset_sum_le_mul_card
