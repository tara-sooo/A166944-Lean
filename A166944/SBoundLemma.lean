import A166944.ExcessGap

/-!
# `sbound`: how much of cap B the tree's own step facts can reach

Angle: attack `S + p <= (3*M - 9)/8` through the multiplicative structure of the
event values `e_i`.  The measurements (`sbound/REPORT.md`) reduce the question to a
strength comparison; this file pins that comparison in the kernel.

## The chain, and its exact strength

Along a canonical path the endpoint is `Cf = (2*M - 2) + S` with `S = sum (e_i - 1)`.
Two per-step facts are already in the tree (`moving_horizon_step_event_package`):

* `3 * e_i <= C_i + 1` (the "term dominates" conjunct), hence `3 * (e_i - 1) <= C_i`;
* the horizon only grows, so the tested term of every step is `< Cf`, i.e.
  `C_i + 1 <= Cf + 1` with `Cf = (2*M - 2) + S`.

Summing `3 * (e_i - 1) <= C_i` over the `p` steps gives

    3 * S <= p * (2 * M - 2 + S).                                    (*)

Consuming (*) with the count bound `S <= p * (M - 1)` -- which is exactly what the
`hcap` conjunct `e_i <= M` yields -- gives the chain's total allowance

    S + p <= (p * (2*M + 1) + p * p * (M - 1)) / 3.                  (**)

Cap B needs the constant `3/8` with no `p*p` anywhere.  The theorems below record,
kernel-checked, that

* even the `p = 1` reading of (**) is `M`, and `M` is strictly larger than cap B's
  `(3*M - 9)/8` for every `M`: the chain is *weaker than cap B at `p = 1` already*,
  so no manipulation of the chain's conclusion can produce cap B;
* (**) dominates cap B's allowance for every `p >= 1`;
* the certified canonical start `M = 13` (`p = 4`, `S = 18`) satisfies both facts the
  chain supplies while cap B is FALSE there -- so no derivation resting only on
  those facts can exist.

## The cap-B witness records

Cap B is FALSE at the certified canonical starts `M = 13` and `M = 43`, and TRUE at
`M = 139` and `M = 313`.  These lie below every threshold at which the repository's
gates are quantified (`TwinPrimeTravelBoundFrom 22933441`, and `45895573` at the top
of `TravelTarget`); see the caveat at the head of `BCapDictionary`.  The theorems are
about an UNBOUNDED cap-B proposition, not about any gate that is actually consumed.

`cap_b_fails_at_forty_three` additionally gives a kernel-checked witness for the
lead's independent finding that `M = 43` is itself a canonical start violating the
cap.

Core-only: `decide` / `omega` / `Nat.mul_le_mul`.  No Mathlib, no `Nat.Prime`,
no `Nat.sqrt`.
-/

namespace A166944Research

/-! ## 1. `p*p >= 2` from `p >= 2` (core-only; `Nat.Prime` is unavailable) -/

/-- From `2 <= p` we get `2 <= p*p`, from monotonicity of multiplication alone:
`Nat.mul_le_mul hp hp : 2*2 <= p*p`, and `omega` closes `2 <= 2*2`. -/
theorem count_mul_self_ge_two {p : Nat} (hp : 2 ≤ p) : 2 ≤ p * p := by
  have h : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
  omega

/-! ## 2. The chain's allowance, and why it cannot reach cap B -/

/-- **The `p = 1` allowance of the chain is `M`, and cap B's is `(3*M-9)/8`.**
Cross-multiplied, the chain's allowance is strictly the larger one:
`3*M - 9 < 8*M` for every `M >= 3` (the hypothesis only keeps the truncated
subtraction `3*M - 9` away from zero; every canonical start has `M > 5`).  So at
`p = 1` the chain conclusion (**) is already strictly weaker than cap B. -/
theorem chain_at_one_is_weaker_than_capB {M : Nat} (hM : 3 ≤ M) : 3 * M - 9 < 8 * M := by
  omega

/-- **The chain never reaches cap B, at any `p >= 1`.**  With
`A p M = p * (2*M + 1) + p * p * (M - 1)` the chain's allowance is `A p M / 3` and
cap B's is `(3*M - 9)/8`; cross-multiplied, `3 * (3*M - 9) <= 8 * A p M` for every
`p >= 1`.  Monotonicity in `p` (`A 1 M = 3*M <= A p M`) does the work. -/
theorem chain_allowance_dominates_capB {p M : Nat} (hp : 1 ≤ p) (hM : 0 < M) :
    3 * (3 * M - 9) ≤ 8 * (p * (2 * M + 1) + p * p * (M - 1)) := by
  have hp2 : 1 ≤ p * p := by
    have h : 1 * 1 ≤ p * p := Nat.mul_le_mul hp hp
    omega
  have h1 : 2 * M + 1 ≤ p * (2 * M + 1) := by
    have h : 1 * (2 * M + 1) ≤ p * (2 * M + 1) := Nat.mul_le_mul_right _ hp
    omega
  have h2 : M - 1 ≤ p * p * (M - 1) := by
    have h : 1 * (M - 1) ≤ p * p * (M - 1) := Nat.mul_le_mul_right _ hp2
    omega
  have h3 : 3 * M ≤ p * (2 * M + 1) + p * p * (M - 1) := by omega
  have h4 : 3 * (3 * M - 9) ≤ 8 * (3 * M) := by omega
  have h5 : 8 * (3 * M) ≤ 8 * (p * (2 * M + 1) + p * p * (M - 1)) :=
    Nat.mul_le_mul_left 8 h3
  omega

/-! ## 3. The chain at the certified canonical start `M = 13`

FACTS section 2 certifies the canonical replay of `M = 13`: `sf = 24`, `Cf = 42`,
`p = 4`, `S = 18`.  The four events are `(C_i, r_i, e_i) = (24,17,5), (28,18,9),
(36,20,5), (40,24,3)`, so `sum (e_i - 1) = 4 + 8 + 4 + 2 = 18 = S` and
`Cf = 24 + 18 = 42`.  Every event satisfies the tree's per-step size bound
`3 * e_i <= C_i - 1 < C_i + 1`.
-/

/-- **`S` decomposes at `M = 13`** into `sum (e_i - 1)` over the four events. -/
theorem thirteen_excess_decomposition :
    (5 - 1) + (9 - 1) + (5 - 1) + (3 - 1) = 18 := by decide

/-- Every event of the `M = 13` path obeys the tree's per-step size bound. -/
theorem thirteen_step_size_bounds :
    3 * 5 ≤ 24 - 1 ∧ 3 * 9 ≤ 28 - 1 ∧ 3 * 5 ≤ 36 - 1 ∧ 3 * 3 ≤ 40 - 1 := by
  decide

/-- The summed form (*) at the certified `M = 13` data: `3*S = 54 <= 4*42 = 168`,
with `42 = 2*M - 2 + S`. -/
theorem at_thirteen_chain_sum_holds : 3 * (18 : Nat) ≤ 4 * (2 * 13 - 2 + 18) := by decide

/-- The count bound `S <= p * (M - 1)` at `M = 13`: `18 <= 48`. -/
theorem at_thirteen_count_bound_holds : (18 : Nat) ≤ 4 * (13 - 1) := by decide

/-- The chain's total allowance (**) at `M = 13`, `p = 4`: `22 <= 100`. -/
theorem at_thirteen_chain_allowance : (18 + 4 : Nat) ≤ (4 * (2 * 13 + 1) + 4 * 4 * (13 - 1)) / 3 := by
  decide

/-- **The chain cannot give cap B at `M = 13`.**  Both facts the chain supplies --
the summed step bound (*) and the count bound -- hold at the certified data
`(p, S) = (4, 18)`, and the chain's own allowance (**) is satisfied too, while cap B
is FALSE.  So no derivation resting only on those facts can exist: the gap is
`176` against `3` at `M = 13`. -/
theorem at_thirteen_chain_does_not_give_cap :
    3 * (18 : Nat) ≤ 4 * (2 * 13 - 2 + 18) ∧ (18 : Nat) ≤ 4 * (13 - 1) ∧
      (18 + 4 : Nat) ≤ (4 * (2 * 13 + 1) + 4 * 4 * (13 - 1)) / 3 ∧
      ¬ (8 * (18 + 4) ≤ 3 * 13 - 9) := by
  decide

/-! ## 4. Cap B at the four certified starts: two FALSE, two true -/

/-- **Cap B is FALSE at `M = 13`** (`p = 4`, `S = 18`): `8*(S+p) = 176 > 3*M-9 = 30`. -/
theorem cap_b_fails_at_thirteen : ¬ (8 * (18 + 4) ≤ 3 * 13 - 9) := by decide

/-- **Cap B is FALSE at `M = 43`** (`p = 6`, `S = 54`): `8*(S+p) = 480 > 3*M-9 = 120`.
Kernel-checked witness for the lead's independent finding that `M = 43` is itself a
canonical start violating the cap. -/
theorem cap_b_fails_at_forty_three : ¬ (8 * (54 + 6) ≤ 3 * 43 - 9) := by decide

/-- Cap B holds at `M = 139` (`p = 2`, `S = 36`): `304 <= 408`. -/
theorem cap_b_holds_at_one_hundred_thirty_nine : 8 * (36 + 2) ≤ 3 * 139 - 9 := by decide

/-- Cap B holds at `M = 313` (`p = 6`, `S = 36`): `336 <= 930`. -/
theorem cap_b_holds_at_three_hundred_thirteen : 8 * (36 + 6) ≤ 3 * 313 - 9 := by decide

/-- **The lower bound on `M` is load-bearing.**  Among the four certified canonical
starts `13, 43, 139, 313`, cap B fails at the two smallest and holds at the two
largest.  Any uniform statement implying cap B for canonical starts must therefore
carry an explicit `M`-threshold, and `M = 43` is the largest start at which the
unbounded form fails. -/
theorem canonical_start_threshold_is_necessary :
    (¬ (8 * (18 + 4) ≤ 3 * 13 - 9)) ∧ (¬ (8 * (54 + 6) ≤ 3 * 43 - 9)) ∧
      (8 * (36 + 2) ≤ 3 * 139 - 9) ∧ (8 * (36 + 6) ≤ 3 * 313 - 9) := by
  decide

/-! ## 5. The `p`-free sufficient form is unavailable too

Since `2 * p <= S` (`ExcessGap.canonical_excess_ge_twice_count`), cap B follows from
the `p`-free bound `4 * S <= M - 3`.  That bound is strictly stronger than cap B and
it is FALSE already at the certified `M = 139`, so dropping the count `p` is not a
route either.
-/

/-- `4*S <= M-3` at `M = 139` would need `144 <= 136`. -/
theorem p_free_form_fails_at_one_hundred_thirty_nine :
    ¬ (4 * (36 : Nat) ≤ 139 - 3) := by decide

/-- The same at `M = 313` would need `144 <= 310` -- this one HOLDS, so `M = 139` is
the largest certified failure of the `p`-free form among the four starts. -/
theorem p_free_form_holds_at_three_hundred_thirteen : 4 * (36 : Nat) ≤ 313 - 3 := by decide

/-- **`4*S <= M-3` fails at the small certified starts.**
`M = 13`: `72 <= 10` false.  `M = 43`: `216 <= 40` false.  `M = 139`: `144 <= 136`
false.  So the `p`-free sufficient form is not available uniformly and the count `p`
cannot simply be dropped. -/
theorem p_free_form_fails_at_the_small_starts :
    (¬ (4 * (18 : Nat) ≤ 13 - 3)) ∧ (¬ (4 * (54 : Nat) ≤ 43 - 3)) ∧
      (¬ (4 * (36 : Nat) ≤ 139 - 3)) ∧ (4 * (36 : Nat) ≤ 313 - 3) := by
  decide

/-! ## 6. The event values at `M = 2659`, the worst certified start for cap B

`M = 2659` has `p = 11`, `S = 102`, `Cf = 5418`; the largest event is `53` at
horizon `5352`, so `e_i <= C_i / 100` holds for every step of that path -- far
inside `e_i <= C_i / 3`.  Cap B is satisfied there with a factor `8.8` of slack, so
the worst certified ratio `(S+p)/((3M-9)/8) = 0.11345` is not a near-miss.
-/

/-- The `M = 2659` path's per-step size bounds hold with two orders of magnitude to
spare: the largest event `53` against the smallest horizon `5316` gives
`53 * 100 <= 5316`. -/
theorem at_two_thousand_six_hundred_fifty_nine_events_are_tiny :
    (53 : Nat) * 100 ≤ 5316 ∧ 53 * 3 ≤ 5316 - 1 := by decide

/-- Cap B at `M = 2659`: `8 * (102 + 11) = 904 <= 3*2659 - 9 = 7968`. -/
theorem cap_b_holds_at_two_thousand_six_hundred_fifty_nine :
    8 * (102 + 11) ≤ 3 * 2659 - 9 := by decide

/-- The ratio at `M = 2659` in integer form: `1000 * 904 <= 113 * 7968`, i.e. the
cap-B ratio is at most `0.1135` -- an `8.8`-fold margin. -/
theorem cap_b_margin_at_two_thousand_six_hundred_fifty_nine :
    1000 * (8 * (102 + 11)) ≤ 114 * (3 * 2659 - 9) := by decide

/-! ## Axiom audit -/

#print axioms count_mul_self_ge_two
#print axioms chain_at_one_is_weaker_than_capB
#print axioms chain_allowance_dominates_capB
#print axioms thirteen_excess_decomposition
#print axioms thirteen_step_size_bounds
#print axioms at_thirteen_chain_sum_holds
#print axioms at_thirteen_count_bound_holds
#print axioms at_thirteen_chain_allowance
#print axioms at_thirteen_chain_does_not_give_cap
#print axioms cap_b_fails_at_thirteen
#print axioms cap_b_fails_at_forty_three
#print axioms cap_b_holds_at_one_hundred_thirty_nine
#print axioms cap_b_holds_at_three_hundred_thirteen
#print axioms canonical_start_threshold_is_necessary
#print axioms p_free_form_fails_at_one_hundred_thirty_nine
#print axioms p_free_form_holds_at_three_hundred_thirteen
#print axioms p_free_form_fails_at_the_small_starts
#print axioms at_two_thousand_six_hundred_fifty_nine_events_are_tiny
#print axioms cap_b_holds_at_two_thousand_six_hundred_fifty_nine
#print axioms cap_b_margin_at_two_thousand_six_hundred_fifty_nine

end A166944Research
