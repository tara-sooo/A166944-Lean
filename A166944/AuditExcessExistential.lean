import A166944.ExcessCriterion

set_option maxRecDepth 100000

/-!
# R4: are the excess-criterion numbers at `M = 139, 313, 2659` correct?
-/

namespace A166944Research

/-- The three headline claims, restated so the report can check each conjunct. -/
theorem R4_at_139 : 8 * (36 + 2) ≤ 3 * 139 - 9 ∧ ¬ (48 * (2 * 2) + 1 < 139) :=
  excess_criterion_holds_at_139

theorem R4_at_313 : 8 * (36 + 6) ≤ 3 * 313 - 9 ∧ ¬ (48 * (6 * 6) + 1 < 313) :=
  excess_criterion_holds_at_313

theorem R4_at_2659 : 8 * (102 + 11) ≤ 3 * 2659 - 9 ∧ ¬ (48 * (11 * 11) + 1 < 2659) :=
  excess_criterion_holds_at_2659

/-! ### A. Re-derive each arithmetic claim independently -/

theorem R4_139_excess : 8 * (36 + 2) ≤ 3 * 139 - 9 := by decide
theorem R4_139_count : ¬ (48 * (2 * 2) + 1 < 139) := by decide
theorem R4_313_excess : 8 * (36 + 6) ≤ 3 * 313 - 9 := by decide
theorem R4_313_count : ¬ (48 * (6 * 6) + 1 < 313) := by decide
theorem R4_2659_excess : 8 * (102 + 11) ≤ 3 * 2659 - 9 := by decide
theorem R4_2659_count : ¬ (48 * (11 * 11) + 1 < 2659) := by decide
theorem R4_5419_both : 8 * (54 + 9) ≤ 3 * 5419 - 9 ∧ 48 * (9 * 9) + 1 < 5419 := by decide
theorem R4_43_excess_fails : ¬ (8 * (54 + 6) ≤ 3 * 43 - 9) := by decide

/-! ### B. THE (S, p) PAIRS ARE NOT PROVED -- they are free parameters

`excess_criterion_holds_at_139` is `8 * (36 + 2) ≤ 3 * 139 - 9 ∧ ...`, i.e. a
closed arithmetic fact in which `S = 36` and `p = 2` are *literal numerals*, not
existentially bound replay values.  The theorem therefore certifies the
*arithmetic*, not that the canonical replay at `M = 139` has `S = 36, p = 2`.

That the numerals match the real replay is an empirical claim, measured outside
Lean.  Below, the replay data is re-checked numerically against the tree's own
evaluable `d`: at `M = 139` the canonical start is `d 141 = 139` with `D 141`. -/

/-- The canonical start predicate at `M = 139` is decidable and TRUE. -/
theorem R4_start_139 : d (139 + 2) = 139 := by decide

/-- The event at index `150` has increment `25`, matching `EventCountFails`. -/
theorem R4_event_150 : d 150 = 25 := by decide

/-- The second event at index `156` has increment `13`. -/
theorem R4_event_156 : d 156 = 13 := by decide

/-- The horizons match: `D 149 = 276 = 2*139-2` and `D 155 = 300`. -/
theorem R4_horizons : D 149 = 276 ∧ D 155 = 300 := ⟨by decide, by decide⟩

/-! ### C. The separation claim, as the lead states it -/

theorem R4_separation_statement :
    ∃ M S p : Nat, 8 * (S + p) ≤ 3 * M - 9 ∧ ¬ (48 * (p * p) + 1 < M) :=
  excess_criterion_is_strictly_sharper

/-- **But the separation is an artefact of choosing a small `M`.**  The `∃` above
is satisfied by any `M` with `p` small enough, including `M = 139, S = 0, p = 0`:
the excess criterion is trivially satisfiable when no events occur, while the
count criterion is a *lower* bound on `M` in terms of `p`.  So
"strictly sharper" is not established by the existential alone -- it needs the
two criteria to be compared at the *same* replay, which the theorem does not do. -/
theorem R4_separation_is_weak :
    8 * (0 + 2) ≤ 3 * 139 - 9 ∧ ¬ (48 * (2 * 2) + 1 < 139) := by decide

/-- **The existential does not identify a replay.**  The same shape is satisfied
with `S = 0`, a value no canonical replay can have (the replay at `M = 139` has
`S = 36`).  So `excess_criterion_is_strictly_sharper` proves only that *some*
`(M,S,p)` triple exists, not that the two criteria are compared on one replay. -/
theorem R4_existential_admits_non_replay_data :
    ∃ M S p : Nat, 8 * (S + p) ≤ 3 * M - 9 ∧ ¬ (48 * (p * p) + 1 < M) ∧ S = 0 := by
  exact ⟨139, 0, 2, by decide, by decide, rfl⟩

end A166944Research

#print axioms A166944Research.R4_at_139
#print axioms A166944Research.R4_at_313
#print axioms A166944Research.R4_at_2659
#print axioms A166944Research.R4_5419_both
#print axioms A166944Research.R4_43_excess_fails
#print axioms A166944Research.R4_start_139
#print axioms A166944Research.R4_event_150
#print axioms A166944Research.R4_event_156
#print axioms A166944Research.R4_horizons
#print axioms A166944Research.R4_separation_statement
#print axioms A166944Research.R4_separation_is_weak
