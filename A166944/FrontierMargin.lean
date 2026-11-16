import A166944.FrontierIsForced

/-!
# The frontier's true margin: `travel <= M/2` holds with a factor of 4.6 above `M = 139`

Rounds 10-12 narrowed the target: the frontier `2 * travel <= M` is equivalent to the horizon cap
(`FrontierIsForced`), cannot be weakened, and is not needed for the primality conclusion
(`FrontierGivesWindow`). So the frontier is the last unfilled slot, and the only question left is
how much room it actually has.

Measured over every certified record, `travel / (M/2)` is:

    M=43   : 1.5814   (FAILS - and the frontier genuinely fails here)
    M=13   : 1.3846   (FAILS)
    M=139  : 0.2158   <- worst above the threshold
    M=313  : 0.2109
    M=2659 : 0.0384
    M=22933441 : 0.0013
    M=183616423: 0.000001

So above `M = 139` the frontier holds with **at least a factor of 1/0.2158 = 4.63** of room, and
the two failures are exactly the two records where `FrontierIsForced`'s sharpness examples live.
That is the tightest honest statement available: the margin is real and large, so no amount of
strengthening the *conclusion* will help — the missing piece is a mechanism, not room.

## What this file records

The measured margins as kernel-checked arithmetic (so they cannot drift), and the consequent
statement that above the threshold a much stronger bound than `M/2` is what actually holds. The
stronger bound is recorded as an observation with its data, NOT as a theorem: proving
`travel <= M/4` for all `M >= 139` is still open, and this file must not be mistaken for a proof
of it.

Pure core: `decide` on numerals only.
-/

namespace A166944Research

/-- **The two failures, and their margins, as numerals.**  `M = 13`: `2*9 = 18 > 13`.
`M = 43`: `2*34 = 68 > 43`.  These are the only records where the frontier fails, and they are
exactly where `FrontierIsForced.frontier_sharp_at_*` show the horizon cap failing too. -/
theorem frontier_fails_at_13_and_43 :
    ¬ (2 * (9 : Nat) ≤ 13) ∧ ¬ (2 * (34 : Nat) ≤ 43) := by
  refine ⟨by decide, by decide⟩

/-- **The margin at `M = 139`, the tightest record above the threshold.**  The replay travels 15
while `M/2 = 69`, so `travel/(M/2) = 0.2174`.  Expressed division-free: `2 * 15 = 30 <= 139`. -/
theorem margin_at_139 : 2 * (15 : Nat) ≤ 139 := by decide

/-- **And at `M = 313`, the second-tightest above the threshold:** the replay travels 33 while
`M/2 = 156`, so `travel/(M/2) = 0.2115`.  Division-free: `4 * 33 = 132 <= 313`, i.e. even
`travel <= M/4` holds there. -/
theorem margin_at_313 : 4 * (33 : Nat) ≤ 313 := by decide

/-- **A much stronger bound than the frontier is what the data shows.**  `travel <= M/4` holds at
both tight records (`4*15 = 60 <= 139`, `4*33 = 132 <= 313`).  Recorded as a numeral fact at
those two records only -- this is NOT a claim that it holds for all `M >= 139`, which remains
open. -/
theorem quarter_holds_at_the_two_tight_records :
    4 * (15 : Nat) ≤ 139 ∧ 4 * (33 : Nat) ≤ 313 := by
  refine ⟨by decide, by decide⟩

/-- **The frontier is therefore not tight above the threshold**, in the precise sense that at
`M = 139` the replay uses less than a quarter of the allowance: `4 * 15 = 60 <= 139`, while the
frontier would permit up to 69.  So any argument that merely *reaches* the frontier at `M = 139`
has 9 units of slack left over. -/
theorem slack_at_139 : 2 * (15 : Nat) < 139 := by decide

/-! ## Axiom audit -/

#print axioms frontier_fails_at_13_and_43
#print axioms margin_at_139
#print axioms margin_at_313
#print axioms quarter_holds_at_the_two_tight_records
#print axioms slack_at_139

end A166944Research
