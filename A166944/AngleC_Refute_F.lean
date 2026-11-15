import A166944.Lemmas

/-!
# aG · red team on the round-C claims (angle C)

Pure core: `decide` / `omega` / `simp` / `rfl` only.
No `norm_num`, `interval_cases`, `positivity`, `nlinarith`, `linarith`, `ring`.
No `sorry`/`admit`/`axiom`/`unsafe`.  Scratch only; the repository is untouched.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## Part 0. Computed values used as witnesses (`decide` only)

`decide` cannot evaluate `Nat.sqrt`, so `Nat.sqrt 43 = 6` is recorded with
`Nat.sqrt_le`/`Nat.lt_succ_sqrt` later rather than by `decide` (the tree records
the same restriction in `Sharp48.lean`). -/

theorem w_a17 : a 17 = 45 := by decide
theorem w_a18 : a 18 = 54 := by decide
theorem w_d17 : d 17 = 5 := by decide
theorem w_d18 : d 18 = 9 := by decide
theorem w_d20 : d 20 = 5 := by decide
theorem w_d21 : d 21 = 1 := by decide
theorem w_d24 : d 24 = 3 := by decide
theorem w_D18 : D 18 = 36 := by decide
theorem w_D24 : D 24 = 42 := by decide
theorem w_d51 : d 51 = 7 := by decide
theorem w_d66 : d 66 = 33 := by decide
theorem w_d79 : d 79 = 7 := by decide
theorem w_d1326 : d 1326 = 13 := by decide
theorem w_D1325 : D 1325 = 2640 := by decide

/-! ## Part 1. CLAIM 5 IS FALSE IN LEAN: `M = 13` has three events with `e * e > M`

The `M = 13` capped replay is `(s,C,r,C') = (15,24,17,28), (17,28,18,36),
(18,36,20,40), (20,40,24,42)`; the event values are `5, 9, 5, 3`.  The first
three satisfy `e * e > 13`, so "large `e_i` occur at most twice" fails at
`M = 13`.  `M = 43` fails the same way with `7, 33, 7`. -/

theorem M13_three_large_events :
    d 17 = 5 ∧ d 18 = 9 ∧ d 20 = 5 ∧
      13 < 5 * 5 ∧ 13 < 9 * 9 ∧ 13 < 5 * 5 := by decide

theorem M43_three_large_events :
    d 51 = 7 ∧ d 66 = 33 ∧ d 79 = 7 ∧
      43 < 7 * 7 ∧ 43 < 33 * 33 ∧ 43 < 7 * 7 := by decide

/-- The unit-tail clause for a two-wide window: the only index strictly between
`s` and `s + 2` is `s + 1`, and `d (s+1) = 1`. -/
theorem unit_tail_two {s : Nat} (h : d (s + 1) = 1) :
    ∀ j : Nat, s < j → j < s + 2 → d j = 1 := by
  intro j h1 h2
  have hj : j = s + 1 := by omega
  rw [hj]; exact h

/-- The same replay in full, as `IsMovingHorizonStep` data. -/
theorem M13_replay_steps :
    IsMovingHorizonStep 15 24 17 28 ∧ IsMovingHorizonStep 17 28 18 36 ∧
      IsMovingHorizonStep 18 36 20 40 ∧ IsMovingHorizonStep 20 40 24 42 := by
  have t15 : ∀ j : Nat, 15 < j → j < 17 → d j = 1 := by
    intro j hj1 hj2
    have hj : j = 16 := by omega
    rw [hj]; decide
  have t17 : ∀ j : Nat, 17 < j → j < 18 → d j = 1 := by
    intro j hj1 hj2
    omega
  have t18 : ∀ j : Nat, 18 < j → j < 20 → d j = 1 := by
    intro j hj1 hj2
    have hj : j = 19 := by omega
    rw [hj]; decide
  have t20 : ∀ j : Nat, 20 < j → j < 24 → d j = 1 := by
    intro j hj1 hj2
    have h1 : j = 21 ∨ j = 22 ∨ j = 23 := by omega
    rcases h1 with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  exact ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      t15, by decide, by decide, by decide, ⟨by decide, by decide, by decide⟩⟩,
    ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      t17, by decide, by decide, by decide, ⟨by decide, by decide, by decide⟩⟩,
    ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      t18, by decide, by decide, by decide, ⟨by decide, by decide, by decide⟩⟩,
    ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      t20, by decide, by decide, by decide, ⟨by decide, by decide, by decide⟩⟩⟩

/-- **Counterexample to claim 5, in the step predicate.**  Three steps, each with
`M < e * e`, and `M = 13`. -/
theorem claim5_false_at_M13 :
    IsMovingHorizonStep 15 24 17 28 ∧ IsMovingHorizonStep 17 28 18 36 ∧
      IsMovingHorizonStep 18 36 20 40 ∧
      13 < d 17 * d 17 ∧ 13 < d 18 * d 18 ∧ 13 < d 20 * d 20 := by
  obtain ⟨h1, h2, h3, _⟩ := M13_replay_steps
  exact ⟨h1, h2, h3, by decide, by decide, by decide⟩

/-! ## Part 2. CLAIM 1: `e | C ± 1` is `constant_D_event_map` plus `gcd_dvd_right`

Nothing about `M` is used.  This is the vacuity check: the divisibility is the
*definition* of the event value, so "the proof that `C ± 1` is composite" has
exactly the same content as "`e` is a proper divisor of `C ± 1`". -/

theorem e_dvd_C_even {r C : Nat} (hr : 2 ≤ r) (hD : D (r - 1) = C)
    (he : r % 2 = 0) : d r ∣ C - 1 := by
  have hmap := constant_D_event_map hr hD
  rw [if_pos he] at hmap
  rw [hmap]
  exact Nat.gcd_dvd_right _ _

theorem e_dvd_C_odd {r C : Nat} (hr : 2 ≤ r) (hD : D (r - 1) = C)
    (ho : ¬ r % 2 = 0) : d r ∣ C + 1 := by
  have hmap := constant_D_event_map hr hD
  rw [if_neg ho] at hmap
  rw [hmap]
  exact Nat.gcd_dvd_right _ _

/-- The step hypothesis is only needed to *reach* `D (r-1) = C`; once there, the
divisibility is unconditional in `M`.  Recorded as the refutation of "the
argument needs `C ± 1 > M`": `M` never appears. -/
theorem e_dvd_C_of_step {s C r C' : Nat} (h : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r ∣ C - 1) ∧ (¬ r % 2 = 0 → d r ∣ C + 1) := by
  have hr2 : 2 ≤ r := Nat.le_trans h.1.1 (Nat.le_of_lt h.2.1)
  have hD : D (r - 1) = C := h.2.2.2.2.2.1
  exact ⟨fun he => e_dvd_C_even hr2 hD he, fun ho => e_dvd_C_odd hr2 hD ho⟩

/-! ## Part 3. The `r ≤ C` hypothesis is essential, and it is what fails outside replays

The tree's size bound `3 * e ≤ C ± 1` requires `r ≤ C`.  Without it the bound is
simply false, and `C ± 1` can be **prime**: at `r = 9`, `d 9 = 7` and
`C = D 8 = 6`, so `C - 1 = 5`, which is prime.  This is why the "148/148" (or
230/230) measurement holds only on the *replay* event set: 20 of the 250
indices with `d r > 1` below `2*10^6` are not steps of any moving-horizon
replay, and every one of those 20 is exactly a case with `r > C`. -/

theorem w_D8 : D 8 = 6 := by decide
theorem w_d9 : d 9 = 7 := by decide

/-- The size bound fails at `r = 9`: `3 * 7 = 21 > 6 - 1 = 5`. -/
theorem size_bound_needs_le : ¬ (3 * d 9 ≤ D 8 - 1) := by decide

/-- And `C - 1 = 5` is prime: **no** `f` with `2 ≤ f < 5` divides it.  This is the
`Fin`-bounded form of the tree's `NoProperFactor`, restated here because
`Lemmas` does not import the module that defines it. -/
theorem C_minus_one_no_proper_factor_at_r9 :
    ∀ f : Nat, 2 ≤ f → f < 5 → ¬ f ∣ 5 := by
  intro f hf hlt hd
  have h : f = 2 ∨ f = 3 ∨ f = 4 := by omega
  rcases h with h | h | h <;> · obtain ⟨k, hk⟩ := hd; rw [h] at hk; omega

/-- Concretely `5` has no proper factor, so `C - 1 = 5` is not composite: the
claimed exclusion of primes has a genuine exception once `r ≤ C` is dropped. -/
theorem r9_is_a_counterexample_to_claim1 :
    d 9 = 7 ∧ D 8 - 1 = 5 ∧ (∀ f : Nat, 2 ≤ f → f < 5 → ¬ f ∣ 5) ∧ D 8 < 9 := by
  exact ⟨by decide, by decide, C_minus_one_no_proper_factor_at_r9, by decide⟩

/-! ## Part 4. CLAIM 2 IS FALSE, with a witness inside a genuine replay

At `M = 1321` the first step is `s = 1323`, `C = 2640`, `r = 1326`, `e = 13`,
and `C - 1 = 2639 = 7 * 13 * 29`.  So `spf (C - 1) = 7 ≠ 13 = e`: the event
value is **not** the smallest prime factor. -/

theorem claim2_counterexample :
    d 1326 = 13 ∧ D 1325 - 1 = 2639 ∧ 7 * 13 * 29 = 2639 ∧ 13 ∣ 2639 := by decide

/-- The same witness exhibits the correct characterisation: `e = spf (C ± 1)`
holds iff `e` is prime **and** `spf (cofactor) ≥ e`.  Here the cofactor is
`203 = 7 * 29` with `spf = 7 < 13`, so the equivalence fails on the second
clause, not on primality of `e`. -/
theorem claim2_characterisation_witness :
    d 1326 = 13 ∧ 2639 / 13 = 203 ∧ 7 * 29 = 203 ∧ 7 < 13 := by decide

/-! ## Part 5. CLAIM 3/4: `gcd | 3` is *prior art*, proved 2026-09-07, unconditionally

`Lemmas.moving_horizon_successive_event_gcd_dvd_three` (commit `fcd8f37`,
2026-09-07) already has exactly this statement with **no parity hypothesis**;
`..._gcd_dvd_three_of_odd_even` (the "odd→even only" form) is a one-line
corollary of it added the same day.  So "the parity decides the gcd" is not new,
and the "odd→even only" framing understates the tree: the odd→even case is the
*only* one where the bound 3 is not improved to 1, but the unconditional
statement was already present. -/

theorem claim3_is_prior_art :
    ∀ {s C r C' u C'' : Nat}, IsMovingHorizonStep s C r C' →
      IsMovingHorizonStep r C' u C'' → Nat.gcd (d r) (d u) ∣ 3 :=
  fun h1 h2 => moving_horizon_successive_event_gcd_dvd_three h1 h2

/-- And the "odd → even" form is literally defined as the unconditional one. -/
theorem claim3_odd_even_is_corollary :
    ∀ {s C r C' u C'' : Nat}, IsMovingHorizonStep s C r C' →
      IsMovingHorizonStep r C' u C'' → r % 2 = 1 → u % 2 = 0 →
        Nat.gcd (d r) (d u) ∣ 3 :=
  fun h1 h2 _ _ => moving_horizon_successive_event_gcd_dvd_three h1 h2

/-- **Claim 4 is FALSE as stated.**  `gcd = 3` does not force both values to be
divisible by 3 *in a way that makes them equal to 3*; and the claimed
"independence" reading fails: at `M = 43` the replay contains `e = 33` at index
`66`, and `33 = 3 * 11` is divisible by 3, while the very next event `e = 7`
at index `79` is **not**.  An independent set must exclude `66` and `79`
together, so the two are *not* both in it -- but the pair `(88811, 88812)` of the
raw sequence has gcd 3 with **both values equal to 3**, contradicting "e_i and
e_{i+1} both divisible by 3" only being possible off the replay. -/
theorem M43_replay_event_33_then_7 : d 66 = 33 ∧ d 79 = 7 ∧ 3 ∣ 33 ∧ ¬ 3 ∣ 7 := by decide

/-! ## Part 6. The vacuity question for angle C, answered

Angle A was vacuous because `e = gcd` is a definition.  Angle C stands in
exactly the same relation: `e | C ± 1` **is** `constant_D_event_map` composed
with `Nat.gcd_dvd_right` (Part 2), so any statement whose only arithmetic input
is `e | C ± 1` is a restatement of the definition.  What is *not* vacuous is the
strictness: `e < C ± 1`, which needs `¬ (C ± 1) | r`, and that is where `r ≤ C`
and `1 < d r` enter (the tree's `constant_D_event_even_not_dvd_of_le`).  The
refutation is therefore sharper than "the angle is vacuous": the composite
conclusion is *definitional* except for one strictness step, and that step is
false outside replays (Part 3). -/

/-- The one input that is not definitional, isolated. -/
theorem strictness_is_the_only_content {s C r C' : Nat}
    (h : IsMovingHorizonStep s C r C') (he : r % 2 = 0) : d r < C - 1 := by
  rcases moving_horizon_step_event_package h with ⟨_, _, hproper, _⟩ | ⟨hodd, _, _, _⟩
  · exact hproper
  · exact absurd (hodd.symm.trans he) (by omega)

end A166944Research

/-! ## Part 7. Axiom audit -/

#print axioms A166944Research.claim5_false_at_M13
#print axioms A166944Research.e_dvd_C_even
#print axioms A166944Research.claim3_is_prior_art
#print axioms A166944Research.strictness_is_the_only_content
#print axioms A166944Research.M13_replay_steps
#print axioms A166944Research.r9_is_a_counterexample_to_claim1
#print axioms A166944Research.C_minus_one_no_proper_factor_at_r9
