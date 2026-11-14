import A166944.CanonicalTravel

/-!
# The count bounds do not bound the count

`moving_horizon_path_count_bounds` (`Lemmas.lean:3851` and `:7355`) gives, for a
moving-horizon path with `q` events and cap `M`,

    3 * q <= E  /\  E <= M * q  /\  2 * q <= T.

All three conjuncts are lower bounds on `q`'s companions, or an upper bound on `E`
in terms of `q`. None of them bounds `q` itself, and this file records that as a
theorem rather than as an observation, because "surely the proven count bounds
limit the count" is a natural thing to assume and it is false.

The witness is explicit: take `E = M * q` and `T = 2 * q`. Then all three
conjuncts hold for every `q`, so no function of `M`, `E`, `T` subject to those
hypotheses can bound `q`. The one side condition is `3 <= M`, which every
canonical start satisfies with room to spare (`M > 5`).

Consequence for the search: the missing input to the travel bound is an event
count bound, and it cannot be extracted from the existing count bounds. It has to
come from somewhere else -- the record hypothesis, `IsAttainedPreviousMaximum`, or
the first-hit arithmetic. `REACH.md` records the numerical margin (the observed
`p` is about 26x below what is needed at the verified certificates); this file
records why that margin cannot be closed from the count bounds alone.
-/

namespace A166944Research

/-- **The count bounds admit arbitrarily large counts.**  For every cap `M >= 3`
and every `q` there are `E` and `T` satisfying all three conjuncts.  So the
conjuncts impose no upper bound on `q`. -/
theorem count_bounds_admit_any_count {M q : Nat} (hM : 3 ≤ M) :
    ∃ E T : Nat, 3 * q ≤ E ∧ E ≤ M * q ∧ 2 * q ≤ T := by
  refine ⟨M * q, 2 * q, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul_right q hM
  · exact Nat.le_refl _
  · exact Nat.le_refl _

end A166944Research
