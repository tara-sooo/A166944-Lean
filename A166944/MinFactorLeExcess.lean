import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# `L ≤ S + p`: the least-factor sum is subordinate to the excess

Route A freezes `MinFactorSumBoundFrom` with `L` = the sum of `min (lpf (C-1)) (lpf (C+1))` over
the events, and needs `4*L ≤ M`. The campaign treated `L` as an independent quantity (round 18 even
called it "the one route whose hypothesis is independent of `S`"), then round 20 showed by
measurement that `L/S` stays in `[0.607, 1.1667]`. This module proves the underlying inequality:

    **`L ≤ S + p`**

## The derivation

At each step the horizon grows by `C_{i+1} - C_i = e_i - 1`, and the event value `e_i` is a multiple
of the least factor `q_i` of the term that fired, hence `e_i ≥ q_i`. So

    C_{i+1} - C_i  =  e_i - 1  ≥  q_i - 1,

and summing telescopes to `S = C_f - C_0 ≥ Σ (q_i - 1) = L - p`, i.e. `L ≤ S + p`.

## What this does and does not give

Measured, the inequality holds at every certified record and is **sharp** at three of them
(`M = 313, 5419, 177841` give equality). It confirms the collapse: `L` is not an independent
quantity.

It does NOT help the frontier, and the reason is arithmetic rather than a gap in the proof.
Combining `L ≤ S + p` with cap (B) `S + p ≤ 3M/8` yields `L ≤ 3M/8`, but Route A needs
`L ≤ M/4`, and `3/8 > 1/4` — the implication runs the wrong way. Conversely `4L ≤ M` gives only
`L ≤ M/4`, and since `(S+p)/L` is measured between `1.0` and `3.17`, no upper bound on `S+p`
follows. So the two routes really are independent as SUFFICIENT conditions, even though their
quantities are comparable.

Pure Mathlib; no `sorry`.
-/

namespace A166944Research

/-- **Pointwise-to-sum**: if every pair `p` of a list satisfies `p.1 ≤ p.2 + 1`, then the sum of
the first components is at most the sum of the second components plus the length. -/
theorem sum_fst_le_sum_snd_add_length (l : List (ℕ × ℕ))
    (h : ∀ p ∈ l, p.1 ≤ p.2 + 1) :
    (l.map Prod.fst).sum ≤ (l.map Prod.snd).sum + l.length := by
  induction l with
  | nil => simp
  | cons p t ih =>
      obtain ⟨a, b⟩ := p
      have ha : a ≤ b + 1 := h (a, b) (by simp)
      have ht : ∀ q ∈ t, q.1 ≤ q.2 + 1 := fun q hq => h q (by simp [hq])
      have ih' := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- **`L ≤ S + p` in telescoped form.**  Given the per-step pairs `(q_i, e_i - 1)` with
`q_i ≤ e_i - 1 + 1 = e_i`, and given that the increments `e_i - 1` sum to `S`, the least-factor sum
is at most `S + p`. -/
theorem min_factor_sum_le_excess_add_count (l : List (ℕ × ℕ)) (S : ℕ)
    (h : ∀ p ∈ l, p.1 ≤ p.2 + 1) (hsum : (l.map Prod.snd).sum = S) :
    (l.map Prod.fst).sum ≤ S + l.length := by
  have := sum_fst_le_sum_snd_add_length l h
  omega

/-! ## Axiom audit -/

#print axioms sum_fst_le_sum_snd_add_length
#print axioms min_factor_sum_le_excess_add_count

end A166944Research
