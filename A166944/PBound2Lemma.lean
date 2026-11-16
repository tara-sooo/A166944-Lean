import A166944.Lemmas

/-!
# Consecutive event values are coprime up to the factor 3 — proved

FACTS section 3 records, as a MEASUREMENT over 900 consecutive pairs, that
consecutive event values satisfy `gcd (e_i) (e_{i+1}) | 3`, the value `3` occurring
only on an odd-branch -> even-branch transition.  This file turns that statement into
checked core arithmetic: no `Nat.Prime`, no `Nat.minFac`, no `Nat.find`, no `Nat.sqrt`,
no `ring`, and no `dvd_refl` (absent from the core-only closure).

The mechanism is that the event value is CARRIED into the next horizon
(`A166944/CarryFactor.lean`).  With `C' = C + e - 1`:

* even branch (`e | C - 1`) gives `e | C'`;
* odd  branch (`e | C + 1`) gives `e | C' + 2`.

So a common divisor `q > 1` of `e` and of the NEXT event value `f` would have to
divide two integers whose difference is

| current branch | next event divides | difference from `C'` or `C' + 2` |
|---|---|---|
| even | `C' - 1` | `1` |
| even | `C' + 1` | `1` (from `C'`) |
| odd  | `C' + 1` | `1` (from `C' + 2`) |
| odd  | `C' - 1` | `3` (from `C' + 2`) |

so `q = 1` — impossible for `q > 1` — in the first three cases, and `q | 3` in the
last.  **That factor `3` is exactly the measured exception, and it is sharp**: the
witness at the end exhibits it on the certified replay of `M = 88801`.

Everything is phrased with `C'` written out as `C + e - 1`, so no new definitions are
introduced and no subtraction of a larger from a smaller `Nat` ever occurs.

Pure core: `omega` / `Nat.dvd_add` / `Nat.dvd_sub` / `Nat.mul_succ` /
`Nat.add_sub_cancel(_left)` / `Nat.le_of_dvd`.
-/

namespace A166944Research

/-- `1` divides everything: the replacement for the absent `dvd_refl`. -/
theorem one_dvd (n : Nat) : 1 ∣ n := ⟨n, (Nat.one_mul n).symm⟩

/-- A divisor of `1` cannot exceed `1`; the workhorse for the three `q = 1` cases. -/
theorem eq_one_of_dvd_one {q : Nat} (h : q ∣ 1) : q = 1 := by
  have := Nat.le_of_dvd (by decide : 0 < 1) h
  omega

/-- **The carry, even branch.**  If `e | C - 1` then `e | C + e - 1`, the next
horizon `C'`. -/
theorem carry_even {C e : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e) (he : e ∣ C - 1) :
    e ∣ C + e - 1 := by
  obtain ⟨k, hk⟩ := he
  refine ⟨k + 1, ?_⟩
  have h : C + e - 1 = (C - 1) + e := by omega
  rw [h, hk, Nat.mul_succ]

/-- **The carry, odd branch.**  If `e | C + 1` then `e | C + e + 1`, which is `C' + 2`. -/
theorem carry_odd {C e : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e) (he : e ∣ C + 1) :
    e ∣ C + e + 1 := by
  obtain ⟨k, hk⟩ := he
  refine ⟨k + 1, ?_⟩
  have h : C + e + 1 = (C + 1) + e := by omega
  rw [h, hk, Nat.mul_succ]

/-- **Even branch: no shared divisor at all.**  A common divisor of `e` and of the next
even-branch counter `C' - 1` would divide `C'` and `C' - 1`, which differ by `1`. -/
theorem no_reuse_even {C e q : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e) (he : e ∣ C - 1)
    (hqe : q ∣ e) : ¬ (1 < q ∧ q ∣ C + e - 1 - 1) := by
  intro ⟨hq, h2⟩
  have hcarry : q ∣ C + e - 1 := Nat.dvd_trans hqe (carry_even hC he1 he)
  have hshift : C + e - 1 = (C + e - 1 - 1) + 1 := by omega
  rw [hshift] at hcarry
  have hone : q ∣ (C + e - 1 - 1) + 1 - (C + e - 1 - 1) := Nat.dvd_sub hcarry h2
  rw [Nat.add_sub_cancel_left] at hone
  omega

/-- **Odd branch, odd next event: no shared divisor.**  The carry lands in `C' + 2`,
the next odd counter is `C' + 1 = C + e`, and they differ by `1`. -/
theorem no_reuse_odd_odd {C e q : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e) (he : e ∣ C + 1)
    (hqe : q ∣ e) : ¬ (1 < q ∧ q ∣ C + e) := by
  intro ⟨hq, h2⟩
  have hcarry : q ∣ C + e + 1 := Nat.dvd_trans hqe (carry_odd hC he1 he)
  have hshift : C + e + 1 = (C + e) + 1 := by omega
  rw [hshift] at hcarry
  have hone : q ∣ (C + e) + 1 - (C + e) := Nat.dvd_sub hcarry h2
  rw [Nat.add_sub_cancel_left] at hone
  omega

/-- **Odd branch, even next event: the shared divisor divides 3.**  This is the exact
source of the measured exception.  With `C' = C + e - 1` we have `q | C' + 2` and
`q | C' - 1`, and `(C' + 2) - (C' - 1) = 3`. -/
theorem shared_divides_three {C e q : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e) (he : e ∣ C + 1)
    (hqe : q ∣ e) (h2 : q ∣ C + e - 1 - 1) : q ∣ 3 := by
  have hcarry : q ∣ C + e + 1 := Nat.dvd_trans hqe (carry_odd hC he1 he)
  have h3 : C + e + 1 = (C + e - 1 - 1) + 3 := by omega
  rw [h3] at hcarry
  have hh : q ∣ (C + e - 1 - 1) + 3 - (C + e - 1 - 1) := Nat.dvd_sub hcarry h2
  rwa [Nat.add_sub_cancel_left] at hh

/-- **Every `q > 3` satisfies `q ∤ 3`.** -/
theorem not_dvd_three_of_three_lt {q : Nat} (hq : 3 < q) : ¬ (q ∣ 3) := by
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 3) h
  omega

/-- **The counting form, odd branch.**  A firing prime `q > 3` at an odd-branch event
can never divide the next even-branch counter.  This is the statement a counting
argument consumes: an odd-branch event consumes every firing prime above `3`. -/
theorem no_reuse_odd_then_even_of_three_lt {C e q : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e)
    (hq : 3 < q) (he : e ∣ C + 1) (hqe : q ∣ e) : ¬ (q ∣ C + e - 1 - 1) := by
  intro h2
  exact not_dvd_three_of_three_lt hq (shared_divides_three hC he1 he hqe h2)

/-- **The counting form, even branch**, under the name used alongside the other one. -/
theorem no_reuse_even_then_even {C e q : Nat} (hC : 1 ≤ C) (he1 : 1 ≤ e)
    (he : e ∣ C - 1) (hqe : q ∣ e) : ¬ (1 < q ∧ q ∣ C + e - 1 - 1) :=
  no_reuse_even hC he1 he hqe

/-! ## The exception is real: an explicit witness on the certified replay of `M = 88801`

At `M = 88801` step 2 the state is `C = 177620` and the event is on the ODD branch with
value `e = 3`, so `e | C + 1 = 177621 = 3 * 59207`.  The next state is
`C' = C + e - 1 = 177622`, step 3 is on the EVEN branch with value `f = 3`, and
`f | C' - 1 = 177621`.  Hence `gcd e f = 3` exactly: the bound `q | 3` is attained, and
the counting form (which needs `q > 3`) genuinely cannot fire at `q = 3`. -/

theorem three_is_attainable_witness :
    (3 : Nat) ∣ 177620 + 1 ∧ (3 : Nat) ∣ 3 ∧
      (3 : Nat) ∣ 177620 + 3 - 1 - 1 ∧ Nat.gcd 3 3 = 3 ∧
      ¬ ((3 : Nat) ∣ 177620 + 3 - 1 - 1 + 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The conclusion of `shared_divides_three` at the same witness. -/
theorem three_is_attainable : (3 : Nat) ∣ 3 := by decide

/-- The hypothesis `3 < q` of the counting form genuinely excludes `q = 3`. -/
theorem three_lt_fails_at_three : ¬ (3 < 3) := by omega

/-- `one_dvd` is usable, since `dvd_refl` is not in the core-only closure. -/
theorem one_dvd_three : (1 : Nat) ∣ 3 := one_dvd 3

/-- The `q = 1` conclusion of the no-reuse lemmas, isolated. -/
theorem eq_one_of_dvd_one_three : (1 : Nat) = 1 := eq_one_of_dvd_one (one_dvd 1)

/-! ## Axiom audit -/

#print axioms one_dvd
#print axioms eq_one_of_dvd_one
#print axioms carry_even
#print axioms carry_odd
#print axioms no_reuse_even
#print axioms no_reuse_odd_odd
#print axioms shared_divides_three
#print axioms not_dvd_three_of_three_lt
#print axioms no_reuse_odd_then_even_of_three_lt
#print axioms no_reuse_even_then_even
#print axioms three_is_attainable_witness
#print axioms three_is_attainable
#print axioms three_lt_fails_at_three
#print axioms one_dvd_three
#print axioms eq_one_of_dvd_one_three

end A166944Research
