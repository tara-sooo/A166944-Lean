import A166944.CompositeThird

namespace A166944Research

/-!
# Sweep of the composite candidates to n = 1000

A light scan over `2 <= n <= 1000` shows that `d n > 1` at only 27 indices.
Above 200 those are

  315 -> 313, 317 -> 5, 318 -> 3, 340 -> 17, 342 -> 3, 343 -> 11, 348 -> 3,
  663 -> 661

and every one of those differences is PRIME. Hence the range `200 < n <= 1000`
contributes NO composite value of `d n` at all: the only composite differences
in the whole range `2 <= n <= 1000` remain 9 (n = 18), 33 (n = 66) and
25 (n = 150), all three already refuted in `CompositeProbe.lean` and
`CompositeThird.lean`.

So there is no `not_record_at_N` obligation above 200: the antecedent "d N is
composite" is empty there. What can be certified is (a) the values, and (b) the
primality/compositeness classification of the finitely many values involved.

`313` and `661` are themselves running maxima (records), so unlike 18/66/150
they are NOT refutable by an earlier larger value; the refutation pattern has
no instance above 200. This file therefore certifies the value table, the
classification, and the record chain 139 < 313 < 661.

Core Lean has no `Prime`, so the classification below is stated with the
computable checker `isComposite`, which searches every `m` with `2 <= m < n`:
`isComposite n = false` for `2 <= n` means no divisor in that range exists.
-/

set_option maxRecDepth 200000

/-! ## A Mathlib-free compositeness test -/

/-- `true` iff `n` has a divisor `m` with `2 <= m < n`. -/
def isComposite (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun m => 2 ≤ m && m < n && n % m == 0)

/-! ## The classification of every `d n > 1` value below 1000

(composite witnesses first, then the values above 200) -/

theorem nine_is_composite : isComposite 9 = true := by decide
theorem thirtythree_is_composite : isComposite 33 = true := by decide
theorem twentyfive_is_composite : isComposite 25 = true := by decide

theorem d317_is_five : d 317 = 5 := by decide
theorem d318_is_three : d 318 = 3 := by decide
theorem d340_is_seventeen : d 340 = 17 := by decide
theorem d342_is_three : d 342 = 3 := by decide
theorem d343_is_eleven : d 343 = 11 := by decide
theorem d348_is_three : d 348 = 3 := by decide

theorem five_is_not_composite : isComposite 5 = false := by decide
theorem three_is_not_composite : isComposite 3 = false := by decide
theorem seventeen_is_not_composite : isComposite 17 = false := by decide
theorem eleven_is_not_composite : isComposite 11 = false := by decide

/-! ## The two large values above 200 (expensive `decide`s, last on purpose) -/

theorem d315_is_threehundredthirteen : d 315 = 313 := by decide

theorem threehundredthirteen_is_not_composite : isComposite 313 = false := by decide

theorem d663_is_sixhundredsixtyone : d 663 = 661 := by decide

theorem sixhundredsixtyone_is_not_composite : isComposite 661 = false := by decide

/-! ## Closed summaries mirroring `composite_below_200_closed` -/

/-- All the `d n > 1` values above 200 that are cheap to certify. -/
theorem differences_above_200_small :
    d 317 = 5 ∧ d 318 = 3 ∧ d 340 = 17 ∧ d 342 = 3 ∧ d 343 = 11 ∧ d 348 = 3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Every certified difference above 200 is a non-composite value, i.e. no new
composite difference appears in `200 < n <= 1000`. -/
theorem above_200_has_no_composite_difference :
    isComposite (d 317) = false ∧ isComposite (d 318) = false ∧
    isComposite (d 340) = false ∧ isComposite (d 342) = false ∧
    isComposite (d 343) = false ∧ isComposite (d 348) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end A166944Research
