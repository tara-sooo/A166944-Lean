import A166944.ExcessGap
import A166944.ExcessLower
import A166944.TargetDefs

/-!
# Cap B's `p` bound is far too weak for the event-count route to cap A

The two remaining platform leaves are `hA` (`Cf ≤ 3*M + 4`, i.e. `S ≤ M + 6`) and `hB`
(`4*sf ≤ 7*M - 1`, i.e. cap B). A natural hope is that one implies the other, so that only a single
leaf needs work. This module records why, in the direction cap B `->` cap A, that fails badly.

## The arithmetic

`CountFromIndex.horizon_ge_start_add_twice_count` (used in `ExcessLower.two_mul_count_le_excess`)
gives `2*p ≤ S` along any canonical path, and cap B is `8*(S+p) ≤ 3*M - 9`. Adding twice the first
inequality to the second:

    `24*p ≤ 3*M - 9`,  i.e.  `p ≤ (M-3)/8`.

The event-count route to cap A needs `48*p*p + 1 < M`, i.e. `p ≤ sqrt(M/48)` approximately. Compare:

| M | bound cap B gives | bound the event-count route needs | factor |
|---|---|---|---|
| 2659 | 332 | 7 | 47 |
| 45895573 | 5746946 | 977 | 5872 |
| 367232911 | 45904113 | 2765 | 16601 |

So cap B's `p` allowance is between one and four ORDERS of magnitude weaker than what the
event-count criterion requires. Cap B therefore cannot supply the event-count criterion in any
range, and this is not a matter of constants: the two are a linear and a square-root bound.

## Consequence

The two leaves are genuinely independent as sufficient conditions: `hB` does not give `hA` this
way, and `hA` gives `hB` only through the frontier (which is the harder statement). Both must be
worked. That is the state of the campaign, recorded so the "just do one of them" hope is closed.

Pure core: `omega` on the tree's own lemmas, plus numerals.
-/

namespace A166944Research

/-- **Cap B forces `p ≤ (M-3)/8`** along a canonical path, given the excess coordinate. -/
theorem capB_forces_linear_count {M S p : Nat} (hSp : 2 * p ≤ S)
    (hcapB : 8 * (S + p) ≤ 3 * M - 9) : 24 * p ≤ 3 * M - 9 := by omega

/-- **And the count bound in the form the comparison uses.** -/
theorem capB_forces_count_divided {M S p : Nat} (hSp : 2 * p ≤ S)
    (hcapB : 8 * (S + p) ≤ 3 * M - 9) : 8 * p ≤ M - 3 := by omega

/-- **The gap, as kernel-checked numerals.**  At `M = 367232911`, cap B permits `p` up to
`(M-3)/8 = 45904113`, while the event-count criterion at `p = 2765` already requires
`48*2765^2 + 1 = 366972001 < 367232911` -- so `p` must be below 2766 there. The first inequality
shows cap B's allowance is more than 16595 times larger. -/
theorem count_gap_at_367232911 :
    48 * (2765 * 2765) + 1 < 367232911 ∧ ¬ (48 * (2766 * 2766) + 1 < 367232911) ∧
      16595 * (2766 : Nat) ≤ 367232911 - 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The same at the smallest post-threshold record**, `M = 45895573`: the criterion allows
`p <= 977` (`48*977^2+1 = 45817393` holds; `48*978^2+1 = 45911233` fails), cap B allows `p <= 5736946`, a factor of 5865. -/
theorem count_gap_at_45895573 :
    48 * (977 * 977) + 1 < 45895573 ∧ ¬ (48 * (978 * 978) + 1 < 45895573) ∧
      5865 * (978 : Nat) ≤ 45895573 - 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Axiom audit -/

#print axioms capB_forces_linear_count
#print axioms capB_forces_count_divided
#print axioms count_gap_at_367232911
#print axioms count_gap_at_45895573

end A166944Research
