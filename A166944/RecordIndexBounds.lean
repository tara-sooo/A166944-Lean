import A166944.Lemmas

namespace A166944Research

/-! Towards the general statement: a composite difference is never a record.

Strategy under test.  Suppose `IsDifferenceRecord R` with `R = a * b`, `2 <= a`,
`2 <= b`.  `record_index_structure` splits on the occurrence index `n`:

    n = R + 2   OR   (n even and 2R <= n)   OR   (n odd and 3R + 2 <= n).

In every case `R` divides `n` or `n - 2` and `n` is large relative to `R`.  The
question is which of these interact with `a * b` to contradict `d k < R` for
the earlier indices `k` forced by `record_*_occurrence_structure`.
-/

-- Step 1: the occurrence index is bounded below by the record value.
theorem record_index_lower_bound {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R) : R + 2 ≤ n := by
  rcases record_index_structure hR hrec hn hd with h | h | h
  · omega
  · omega
  · omega

-- Step 2: in the even late branch the record value divides the index and the
-- index is at least twice the record value.
theorem record_even_late_divisibility {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R)
    (heven : n % 2 = 0) (hlate : 2 * R ≤ n) :
    ∃ c : Nat, n = R * c ∧ 2 ≤ c := by
  obtain ⟨c, hc, _, hc2⟩ := record_even_occurrence_structure hR hrec hn hd heven
  exact ⟨c, hc, hc2⟩

end A166944Research
