import A166944.Lemmas

namespace A166944Research

/-! The general obstruction: a composite difference cannot be a record.

Reduction under test.  Let `R = a * b` with `2 <= a`, `2 <= b`, and suppose
`IsDifferenceRecord R`, realised at index `n` with `d n = R`.  Since `R` is a
record, `R` is odd (`record_value_mod_two_eq_one`), so `a` and `b` are odd.

`d n = R` and the gcd form `d n = gcd(n, a(n-1))` (n even) or
`gcd(n-2, a(n-1))` (n odd) give `R | n` or `R | n - 2`.  Combined with the
occurrence structure this pins `n` modulo `R`.

The missing ingredient is a reason for `a` or `b` to appear as an earlier
difference value.  We record what *is* available: the divisibility facts and
the index lower bound, both reusable.
-/

/-- A record `R` divides `n` (even occurrence) or `n - 2` (odd occurrence). -/
theorem record_divides_index_or_pred {R n : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hn : 2 ≤ n) (hd : d n = R) :
    (n % 2 = 0 ∧ R ∣ n) ∨ (n % 2 = 1 ∧ R ∣ n - 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · left
    refine ⟨h0, ?_⟩
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_pos h0]
    exact Nat.gcd_dvd_left _ _
  · right
    refine ⟨h1, ?_⟩
    have hne : n % 2 ≠ 0 := by omega
    rw [← hd, d_eq_if_gcd_of_two_le hn, if_neg hne]
    exact Nat.gcd_dvd_left _ _

/-- Every record value is odd, hence so is each factor of a composite record. -/
theorem record_odd_and_factor_odd {R a b : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) (hfab : R = a * b) (ha : 2 ≤ a) :
    R % 2 = 1 ∧ a % 2 = 1 := by
  have hRodd := record_value_mod_two_eq_one hR hrec
  refine ⟨hRodd, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
  · exfalso
    have h2a : 2 ∣ a := Nat.dvd_of_mod_eq_zero h0
    obtain ⟨c, hc⟩ := h2a
    have : R % 2 = 0 := by
      rw [hfab, hc]
      simp [Nat.mul_assoc]
    omega
  · exact h1

end A166944Research
