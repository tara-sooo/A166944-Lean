import A166944.CompSweep1000

namespace A166944Research

/-!
# Complete classification of composite differences below 1000

This is the strongest form of the requested extension. Instead of sampling the
candidates above 200 one by one, it decides the whole statement over the closed
range `2 <= n <= 1000`:

  * the ONLY indices below 1000 whose difference is composite are 18, 66 and 150
    -- all three already refuted by `CompositeProbe.lean` / `CompositeThird.lean`;
  * consequently there is no composite difference at all in `200 < n <= 1000`,
    so the refutation pattern has no instance above 200.

`isComposite` is the computable test from `CompSweep1000.lean`; it returns
`true` exactly when some `m` with `2 <= m < n` divides `n`, so `= false`
certifies compositeness is impossible. The two theorems are closed `decide`s
over `List.range 1001`, i.e. every index in the range is checked by the kernel
itself, not by a sampled scan.
-/

set_option maxRecDepth 1000000

/-- The complete classification: below 1000 a composite difference occurs only
at 18, 66 and 150. -/
theorem composite_differences_below_1000 :
    ∀ n ∈ List.range 1001, isComposite (d n) = true → n = 18 ∨ n = 66 ∨ n = 150 := by
  decide

/-- Therefore no composite difference exists in `200 < n <= 1000`. -/
theorem no_composite_difference_above_200 :
    ∀ n ∈ List.range 1001, 200 < n → isComposite (d n) = false := by
  decide

end A166944Research
