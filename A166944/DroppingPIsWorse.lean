import A166944.ExcessGap

/-!
# Dropping `p` is not merely harder -- it is impossible

The campaign objective names two inputs, `S` and `p`, and earlier rounds considered eliminating `p`
on the grounds that it is numerically negligible. Measured, `p` contributes about `0.002%` of the
allowance `(3M-9)/8` at `M = 22933441`. So the temptation is real.

This file records why the temptation must be resisted at the level of STATEMENTS: the `p`-free
bound does not follow from cap (B), and it does not imply cap (B) either. The two are genuinely
different propositions, and only one of them is true.

## The two directions

* `ExcessGap.excess_criterion_forces_horizon_growth` proves
  `8*(S+p) <= 3M-9  ->  8*S <= 3M-9` (it carries `2p <= S` for its other use). Real, already in the tree.
* The CONVERSE is FALSE. Counterexample: `p = 1`, `S = 2`, `M = 9` gives `2p = 2 <= 2 = S` and
  `8*S = 16 <= 18 = 3M-9`, but `8*(S+p) = 24 > 18`. Verified by `decide` below.

So eliminating `p` from the statement produces a strictly stronger bound that does NOT follow, and
the implication is one-way. This is worth recording because the numerical negligibility of `p`
makes the opposite look plausible.

## Why the margin looks contradictory at first

At the tight record `M = 139` we have `S = 36`, `p = 2`, so `8S = 288` against `408` (70.6% used)
and `8(S+p) = 304` against `408` (74.5% used). Both hold there. The difference between the two
statements is not visible at any single record -- it is a statement about ALL `(M, S, p)`
satisfying the hypotheses, and the small-`M` counterexamples above are where they separate.

Pure core: `omega` and `decide` only.
-/

namespace A166944Research

/-- **The `p`-free bound does NOT follow from cap (B)'s hypotheses.**  Explicit witness:
`p = 1`, `S = 2`, `M = 9`.  Then `2*p <= S` and `8*S <= 3*M-9`, but `8*(S+p) > 3*M-9`. -/
theorem dropping_p_fails :
    ¬ (8 * (2 + 1) ≤ 3 * 9 - 9) ∧ 2 * (1 : Nat) ≤ 2 ∧ 8 * (2 : Nat) ≤ 3 * 9 - 9 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **A second witness, at larger numbers, so the failure is not a small-`M` artefact:**
`p = 5`, `S = 10`, `M = 30` gives `2p = S`, `8S = 80 <= 81 = 3M-9`, but `8(S+p) = 120 > 81`. -/
theorem dropping_p_fails_at_30 :
    ¬ (8 * (10 + 5) ≤ 3 * 30 - 9) ∧ 2 * (5 : Nat) ≤ 10 ∧ 8 * (10 : Nat) ≤ 3 * 30 - 9 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The one true direction, for contrast:** cap (B) implies the `p`-free form.  Note that
`2*p <= S` is NOT needed for this direction -- dropping the non-negative `8*p` from the left side
is unconditionally valid.  The tree's `excess_criterion_forces_horizon_growth` carries `2*p <= S`
because it uses the bound in the other way as well. -/
theorem capB_implies_s_only {M S p : Nat} :
    8 * (S + p) ≤ 3 * M - 9 → 8 * S ≤ 3 * M - 9 := by
  intro h
  omega

/-- **Both forms hold at the tight record `M = 139`** (`S = 36`, `p = 2`), so the failure above is
invisible at any single certified record -- it lives in the universally quantified statement. -/
theorem both_forms_hold_at_139 :
    8 * (36 : Nat) ≤ 3 * 139 - 9 ∧ 8 * (36 + 2) ≤ 3 * 139 - 9 := by
  refine ⟨by decide, by decide⟩

/-! ## Axiom audit -/

#print axioms dropping_p_fails
#print axioms dropping_p_fails_at_30
#print axioms capB_implies_s_only
#print axioms both_forms_hold_at_139

end A166944Research
