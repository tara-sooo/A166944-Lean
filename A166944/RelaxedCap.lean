import A166944.TwoCapGate
import A166944.OrphanHarvest

/-!
# The relaxed index cap and what it forces

`TwoCapGate` established that the consumer of the travel bound actually needs the
relaxed index cap

    4 * sf <= 7 * M - 1

and that it is strictly weaker than the bound the development previously carried.
This module isolates the cap itself and records what it forces.

## The forced consequence

The count/index coupling proved in `OrphanHarvest`,

    p + M <= sf + 1,

holds unconditionally. Combining it with the cap gives

    p + M - 1 <= sf   and   4 * sf <= 7 * M - 1,

hence `4 * p <= 3 * M + 3`. That is a bound on the number of nonunit events of the
replay, obtained from an index bound and no arithmetic of the increments at all.

This gives a second way to attack the cap: a proof that `p` is at most `3M/4`
would not give the cap -- the coupling is an inequality, not an equivalence -- but
it identifies `p` as the quantity the cap is really about, which is what `REACH.md`
has said from the other direction.

## What is not claimed

Nothing here proves the cap. The statements below are arithmetic consequences of
it; the cap itself remains open, and so does the count bound it forces.

## A note on the proofs

Each step is written so that `omega` sees one arithmetic fact at a time. Passing a
goal that mixes a coefficient with a truncated subtraction directly to `omega`
fails, and the failure is silent in the sense that it reports a spurious
counterexample rather than a missing hypothesis. The identity
`4 * (sf - (M+2)) + 4 * (M+2) = 4 * sf`, proved once per statement, keeps the two
apart.
-/

namespace A166944Research

/-- The displacement identity used by the statements below, named so that `omega`
never has to reason about a truncated subtraction and a coefficient together. -/
private theorem four_mul_canonical_decomp {M sf : Nat} (h : M + 2 ≤ sf) :
    4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel h
  rw [← Nat.mul_add, hsplit]

/-- **The travel bound implies the cap.**  Anything proved about travel is
available to a proof of the cap, and the cap is the weaker of the two. -/
theorem relaxed_cap_of_travel_bound {M sf : Nat} (h : M + 2 ≤ sf) (hM : 9 ≤ M)
    (htravel : 2 * (sf - (M + 2)) ≤ M) :
    4 * sf ≤ 7 * M - 1 := by
  -- The step needs `M >= 9`: travel gives `4 * sf <= 6 * M + 8`, and
  -- `6 * M + 8 <= 7 * M - 1` exactly when `M >= 9`. Stating it as a hypothesis
  -- rather than leaving it to `omega` keeps the arithmetic explicit; callers have
  -- `M >= 45895573`.
  have h4 := four_mul_canonical_decomp h
  omega

/-- **The cap forces a count bound.**  With the unconditional coupling
`p + M <= sf + 1`, the cap implies `4 * p <= 3 * M + 3`. -/
theorem cap_b_implies_count_bound {M sf p : Nat} (h : M + 2 ≤ sf)
    (hcap : 4 * sf ≤ 7 * M - 1) (hcount : p + M ≤ sf + 1) :
    4 * p ≤ 3 * M + 3 := by omega

/-- **The contrapositive, in the form a refutation would take.**  If the event
count exceeds `(3 * M + 3) / 4`, the cap fails. -/
theorem cap_b_fails_of_large_count {M sf p : Nat} (h : M + 2 ≤ sf)
    (hcount : p + M ≤ sf + 1) (hbig : 3 * M + 3 < 4 * p) :
    ¬ (4 * sf ≤ 7 * M - 1) := by omega

end A166944Research
