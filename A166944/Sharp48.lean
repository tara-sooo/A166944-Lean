import A166944.CanonicalTravel

/-!
# The constant 48 in the event-count criterion is optimal

`CanonicalTravel.previous_record_le_of_long_travel` proves

    M < 2 * (k * Nat.sqrt (4 * (3 * M + 4)))  ->  M <= 48 * (k * k) + 1,

and 48 is the only place that constant enters the development: everything
downstream -- `canonical_old_crossing_event_count`,
`canonical_horizon_bound_of_event_count`,
`canonical_travel_bound_of_event_count`, and so the event-count criterion
`48 * p * p + 1 < M` -- inherits it from here.

This module shows that 48 cannot be replaced by anything smaller in that
implication. The witness is `k = 2, M = 191`: the hypothesis holds
(`191 < 2 * (2 * sqrt 2308)`, since `48 * 48 = 2304 <= 2308`), while the
conclusion with coefficient `c` would require `191 <= 4 * c + 1`, i.e. `c >= 48`.

## Why it is not an accident

The hypothesis is `M * M < 4 * k^2 * (12 * M + 16)`, a quadratic in `M` whose
positive root is `24 * k^2 + 8 * k * sqrt (9 * k^2 + 1)` -- just below `48 * k^2`.
The family `M = 48 * k^2 - 1` sits on that root, so `M <= 48 * k^2 + 1` is the
tight form of a crossing estimate rather than a crude one, and no smaller
coefficient can hold on the family.

## What this closes

Tightening `48 * p * p + 1 < M` by arithmetic sharpening is not available. The
criterion is what it is, and a route that needs it has to establish it at that
strength. `REACH.md` records the criterion failing at four small records
(`M = 43, 139, 313, 2659`, the largest below the threshold by four orders of
magnitude) and holding with a margin of about 26 at the certified replays, so the
empirical picture is not in doubt; what is now fixed is that the constant is not
the obstacle.

## A missing sqrt direction

`sqrt_ge_of_sq_le` -- `m * m <= n` implies `m <= Nat.sqrt n` -- was not in the
tree. The converse direction `Nat.sqrt_le` was, and `decide` cannot evaluate
`Nat.sqrt`, so the lower estimate needed this lemma.

## A caution recorded from the attempt

An early numerical probe suggested the coefficient could be lowered to 25. It was
checking an inequality that is not the proof obligation. The obligation, checked
directly, gives 48. The lesson is the one this development keeps relearning:
a numerical law has to be verified against the actual statement, not against a
nearby inequality that happens to be easier to test.
-/

namespace A166944Research


/-! ## 1. The square-root direction the tree was missing -/

/-- **Lower square-root bound.**  A square below `n` bounds `Nat.sqrt n` from
*below*.  This is what makes a concrete `Nat.sqrt` value usable without `decide`. -/
theorem sqrt_ge_of_sq_le {n m : Nat} (h : m * m ≤ n) : m ≤ Nat.sqrt n := by
  by_cases hle : m ≤ Nat.sqrt n
  · exact hle
  · exfalso
    have h1 : Nat.sqrt n + 1 ≤ m := by omega
    have h2 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ m * m :=
      Nat.mul_self_le_mul_self h1
    have h3 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    omega

/-! ## 2. Two general helpers, kept free of `omega`-over-products -/

/-- Product monotonicity in the exact shape needed below. -/
theorem mul_ge_of_ge {c A : Nat} (h1 : 1 ≤ c) (h2 : 4 ≤ A) : 4 ≤ c * A := by
  have h : 1 * 4 ≤ c * A := Nat.mul_le_mul h1 h2
  simpa using h

/-- **The arithmetic core of the sharpness.**  With `c < 48` and `A >= 4` there is
no way for `(48 - c) * A` to be at most `2`. -/
theorem no_small_coeff {c A : Nat} (hc : c < 48) (hA : 4 ≤ A)
    (h : (48 - c) * A ≤ 2) : False := by
  have h1 : 1 ≤ 48 - c := by omega
  have h4 := mul_ge_of_ge h1 hA
  omega

/-- `48 * (k * k)` is positive for `k >= 1`; proved by explicit product
monotonicity so `omega` never sees the product. -/
theorem pos_48_mul_sq {k : Nat} (hk : 1 ≤ k) : 0 < 48 * (k * k) := by
  have h : 1 ≤ k * k := by
    have h1 : 1 * 1 ≤ k * k := Nat.mul_le_mul hk hk
    simpa using h1
  have hm : 1 * 1 ≤ 48 * (k * k) := Nat.mul_le_mul (by decide : 1 ≤ 48) h
  omega

/-- The contradiction at the family, with the truncated subtraction removed by a
named identity and the product `k * k` generalised to an atom. -/
theorem family_contradiction {c k : Nat} (hc : c < 48) (hk : 2 ≤ k)
    (hcon : 48 * (k * k) - 1 ≤ c * (k * k) + 1) : False := by
  have hA : 4 ≤ k * k := Nat.mul_le_mul hk hk
  generalize hAdef : k * k = A at hA hcon ⊢
  have hcan : 48 * A - 1 + 1 = 48 * A := Nat.sub_add_cancel (by omega : 1 ≤ 48 * A)
  have hstep : 48 * A ≤ c * A + 2 := by
    have h2 := Nat.add_le_add_right hcon 1
    rw [hcan] at h2
    omega
  have hsub : 48 * A - c * A ≤ 2 := by omega
  have heq : 48 * A - c * A = (48 - c) * A := (Nat.sub_mul 48 c A).symm
  rw [heq] at hsub
  exact no_small_coeff hc hA hsub

/-! ## 3. The witness at `k = 2` -/

/-- The radicand at the witness, evaluated once so `omega` never has to combine a
coefficient with a product. -/
theorem radicand_at_witness : 4 * (3 * 191 + 4) = 2308 := by decide

/-- `48^2 <= 2308`. -/
theorem sq_le_radicand_at_witness : 48 * 48 ≤ 2308 := by decide

/-- `48 <= Nat.sqrt 2308`. -/
theorem sqrt_radicand_at_witness : 48 ≤ Nat.sqrt 2308 :=
  sqrt_ge_of_sq_le sq_le_radicand_at_witness

/-- **The witness satisfies the hypothesis** of the long-travel bound:
`191 < 2 * (2 * Nat.sqrt (4 * (3 * 191 + 4)))`. -/
theorem witness_191_satisfies_long_travel :
    (191 : Nat) < 2 * (2 * Nat.sqrt (4 * (3 * 191 + 4))) := by
  rw [radicand_at_witness]
  have hmul : 4 * 48 ≤ 4 * Nat.sqrt 2308 := Nat.mul_le_mul_left 4 sqrt_radicand_at_witness
  have hform : 2 * (2 * Nat.sqrt 2308) = 4 * Nat.sqrt 2308 := by omega
  rw [hform]
  omega

/-- **The coefficient 48 is optimal.**  Any `c` for which the long-travel bound
holds at every `(M, k)` satisfies `48 ≤ c`. -/
theorem coefficient_forty_eight_is_optimal (c : Nat)
    (h : ∀ M k : Nat, M < 2 * (k * Nat.sqrt (4 * (3 * M + 4))) → M ≤ c * (k * k) + 1) :
    48 ≤ c := by
  have hc := h 191 2 witness_191_satisfies_long_travel
  have h4 : (2 : Nat) * 2 = 4 := by decide
  rw [h4] at hc
  omega

/-- **No smaller coefficient works**, as a negative existential so that the
optimality cannot be misread as a failure of one estimate. -/
theorem no_smaller_coefficient_works :
    ¬ (∃ c : Nat, c < 48 ∧ ∀ M k : Nat,
        M < 2 * (k * Nat.sqrt (4 * (3 * M + 4))) → M ≤ c * (k * k) + 1) := by
  rintro ⟨c, _, h⟩
  have := coefficient_forty_eight_is_optimal c h
  omega

/-! ## 4. The infinite family `M = 48 * k * k - 1` -/

/-- The radicand at the family, with the truncated subtraction eliminated once by
name. -/
private theorem family_radicand {k : Nat} (hk : 1 ≤ k) :
    4 * (3 * (48 * (k * k) - 1) + 4) = 576 * (k * k) + 4 := by
  have ht : 1 ≤ k * k := by
    have h := Nat.mul_le_mul hk hk
    simpa using h
  omega

/-- **Every member of the family satisfies the hypothesis.**  The key step is
`24 * k <= Nat.sqrt (576 * k * k + 4)`, from `sqrt_ge_of_sq_le` at the square
`(24 * k)^2 = 576 * (k * k)`. -/
theorem family_satisfies_long_travel (k : Nat) (hk : 1 ≤ k) :
    48 * (k * k) - 1 < 2 * (k * Nat.sqrt (4 * (3 * (48 * (k * k) - 1) + 4))) := by
  rw [family_radicand hk]
  have h24 : (24 * k) * (24 * k) = 576 * (k * k) := by
    rw [show (24 * k) * (24 * k) = (24 * 24) * (k * k) by ac_rfl]
  have hsq : (24 * k) * (24 * k) ≤ 576 * (k * k) + 4 := by omega
  have hge : 24 * k ≤ Nat.sqrt (576 * (k * k) + 4) := sqrt_ge_of_sq_le hsq
  have hstep : k * (24 * k) ≤ k * Nat.sqrt (576 * (k * k) + 4) :=
    Nat.mul_le_mul_left k hge
  have hstep2 : 2 * (k * (24 * k)) ≤ 2 * (k * Nat.sqrt (576 * (k * k) + 4)) :=
    Nat.mul_le_mul_left 2 hstep
  have hid : 2 * (k * (24 * k)) = 48 * (k * k) := by
    rw [show k * (24 * k) = 24 * (k * k) by ac_rfl]
    rw [← Nat.mul_assoc]
  rw [hid] at hstep2
  exact Nat.lt_of_lt_of_le (Nat.sub_lt (pos_48_mul_sq hk) (by decide : 0 < 1)) hstep2

/-- **The family refutes every smaller coefficient, uniformly in `k`.** -/
theorem smaller_coefficient_fails_on_family (c k : Nat) (hc : c < 48) (hk : 2 ≤ k) :
    (48 * (k * k) - 1 < 2 * (k * Nat.sqrt (4 * (3 * (48 * (k * k) - 1) + 4)))) ∧
      ¬ (48 * (k * k) - 1 ≤ c * (k * k) + 1) :=
  ⟨family_satisfies_long_travel k (by omega),
    fun hcon => family_contradiction hc hk hcon⟩

/-- **Packaged form.**  For every `c < 48` there is a witness pair `(M, k)`
satisfying the hypothesis and failing the coefficient-`c` conclusion. -/
theorem every_smaller_coefficient_has_witness (c : Nat) (hc : c < 48) :
    ∃ M k : Nat, M < 2 * (k * Nat.sqrt (4 * (3 * M + 4))) ∧
      ¬ (M ≤ c * (k * k) + 1) := by
  refine ⟨48 * (2 * 2) - 1, 2, ?_, ?_⟩
  · have hfam := family_satisfies_long_travel 2 (by decide)
    have hnum : 48 * (2 * 2) - 1 = (191 : Nat) := by decide
    have hrad : 4 * (3 * (48 * (2 * 2) - 1) + 4) = 4 * (3 * 191 + 4) := by omega
    rw [hnum, hrad] at hfam
    exact hfam
  · intro hcon
    have hnum : 48 * (2 * 2) - 1 = (191 : Nat) := by decide
    rw [hnum] at hcon
    have h4 : (2 : Nat) * 2 = 4 := by decide
    rw [h4] at hcon
    omega

/-! ## 5. Summary -/

/-- **Summary.**  A family satisfying the hypothesis for every `k >= 1`, and the
non-existence of a uniform coefficient below 48.  With
`previous_record_le_of_long_travel` this pins the constant at exactly 48. -/
theorem forty_eight_sharp :
    (∀ k : Nat, 1 ≤ k → 48 * (k * k) - 1 <
        2 * (k * Nat.sqrt (4 * (3 * (48 * (k * k) - 1) + 4)))) ∧
      ¬ (∃ c : Nat, c < 48 ∧ ∀ M k : Nat,
        M < 2 * (k * Nat.sqrt (4 * (3 * M + 4))) → M ≤ c * (k * k) + 1) :=
  ⟨family_satisfies_long_travel, no_smaller_coefficient_works⟩

/-- **The frontier hypothesis has no slack in its coefficient.**  The statement
consumed by `canonical_travel_bound_of_event_count` is the coefficient-48 form, and
by the theorems above the coefficient cannot be reduced while keeping the same proof
shape.  So `48 * p * p + 1 < M` is the exact strength of this route. -/
theorem frontier_coefficient_is_sharp (c : Nat)
    (h : ∀ M k : Nat, M < 2 * (k * Nat.sqrt (4 * (3 * M + 4))) → M ≤ c * (k * k) + 1) :
    48 ≤ c :=
  coefficient_forty_eight_is_optimal c h

#print axioms sqrt_ge_of_sq_le
#print axioms no_small_coeff
#print axioms pos_48_mul_sq
#print axioms family_contradiction
#print axioms witness_191_satisfies_long_travel
#print axioms coefficient_forty_eight_is_optimal
#print axioms no_smaller_coefficient_works
#print axioms family_satisfies_long_travel
#print axioms smaller_coefficient_fails_on_family
#print axioms every_smaller_coefficient_has_witness
#print axioms forty_eight_sharp
#print axioms frontier_coefficient_is_sharp

end A166944Research
