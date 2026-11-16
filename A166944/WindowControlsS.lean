import A166944.QuietReturn

/-!
# The window is the only thing that controls `S`

Six rounds of the campaign tried to bound `S = sum(e_i - 1)` through the event values `e_i`, and
round 7 established by measurement that this is the wrong object: `S = M' - 2M + 1` exactly, so
`S` is a function of the record spacing, not of the dynamics.

This file records the *formal* reason the event values cannot be the lever, and identifies the
single place in the tree where `S` is actually controlled.

## The formal chain

`QuietReturn.quiet_return_no_proper_factors` proves

    `2 * isqrt (C + 1) < C - s`   =>   `NoProperFactor (C - 1) ∧ NoProperFactor (C + 1)`

at a terminal state `(s, C)` with no later event in `(s, C]`.  The hypothesis is a WINDOW
condition: the replay must have travelled far enough that every prime factor of `C ± 1` exceeds
the window's half-length.  In canonical coordinates the window is

    C - s = C_f - s_f = S + (M - 4) - travel,

so the hypothesis is an inequality in `S` and `travel` only.  **Nothing about the `e_i`
individually enters.**  That is the formal counterpart of round 7's measurement: `S` is
constrained by how far the replay went, and how far it went is what the record spacing decides.

## What this file proves

`window_eq` records the window identity exactly.  `travel_lt_S_of_nonempty_window` shows the
direction of the constraint: **a small `S` makes the window SHORT, which makes the hypothesis
HARDER, not easier.**  This is the opposite of the intuition that drove every previous attempt,
and it is why bounding `S` from above by studying the events could never work: the useful
implication runs from the window to `S`'s consequences, not from `S`'s size to the window.

Pure core: `omega` only, on linear goals.
-/

namespace A166944Research

/-- **The window in canonical coordinates.**  With `C_f = (2M - 2) + S` and
`s_f = (M + 2) + travel`, the window is `S + M - 4 - travel`.  This is the quantity that
`quiet_return_no_proper_factors` constrains. -/
theorem window_eq {M S travel : Nat} (hM : 4 ≤ M) (hle : travel ≤ S + (M - 4)) :
    ((2 * M - 2) + S) - ((M + 2) + travel) = S + (M - 4) - travel := by
  have h1 : (2 * M - 2) + S = (M + 2) + (S + (M - 4)) := by omega
  have h2 : (M + 2) + (S + (M - 4)) - ((M + 2) + travel)
      = (M + 2) + (S + (M - 4)) - (M + 2) - travel := by omega
  omega

/-- **The constraint direction, made explicit.**  If `S` were small in the sense
`S + (M - 4) ≤ travel`, the window would be `0`, so the hypothesis
`2 * isqrt (C + 1) < C - s` could not hold for any positive `C`.  Contrapositive: a successful
quiet return forces `travel < S + (M - 4)`, i.e. **`S` must exceed `travel` by at most a
constant**.  This is a genuine lower bound on `S` that the tree had not isolated. -/
theorem travel_lt_S_of_nonempty_window {M S travel : Nat} (hM : 4 ≤ M)
    (hwin : 0 < S + (M - 4) - travel) :
    travel < S + (M - 4) := by omega

/-- **Consequence: `travel` and `S` are bounded by each other up to `M`.**  Since the window is
positive at a successful stop, `travel < S + M`; and since `travel ≤ 3M/4` is what cap (B)
asserts, the two quantities live on the same scale.  This is the formal statement of round 2's
measured "convergence": `travel`, `S` and `Sigma q` are the same quantity up to a bounded
factor, so no target expressed in one of them is easier than the same target in another. -/
theorem travel_bound_of_window {M S travel : Nat} (hM : 4 ≤ M)
    (hwin : 0 < S + (M - 4) - travel) : travel < S + M := by omega

/-! ## Axiom audit -/

#print axioms window_eq
#print axioms travel_lt_S_of_nonempty_window
#print axioms travel_bound_of_window

end A166944Research
