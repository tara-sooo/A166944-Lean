import A166944.Lemmas

/-!
# aG · red team, part 4: does the `sqrt`-route counterexample generalise?

Pure core only (`decide`/`omega`/`simp`/`rfl`); no `sorry`/`admit`/`axiom`/`unsafe`.
Scratch only; the repository is untouched.
-/

set_option maxRecDepth 1000000

namespace A166944Research

/-! ## 1. The generalisation is not "another accident": it is exactly `q = 3`

The tree bound `3 * d r ≤ C ± 1` (`moving_horizon_step_event_package`) says the
cofactor `q = (C ± 1) / (d r)` satisfies `q ≥ 3`.  Write `e = d r`.  Then

    e * e ≤ C ± 1   ⟺   e ≤ q.

So a counterexample to the `sqrt` route needs `e > q`, and since `q ≥ 3` the
*minimal* way this can happen is `q = 3` together with `e > 3`.  Below: `q = 3`
is attained, so the counterexample is not a boundary artefact of a loose
inequality -- it is the extreme point of the only inequality the tree supplies. -/

/-- **The exact algebraic reduction.**  With `e * q = n` and `0 < e`, the
statement `e * e ≤ n` is `e ≤ q`.  This is the isomorphism that makes the
generalisation question answerable. -/
theorem sq_le_iff_le_cofactor {e q : Nat} (he : 0 < e) :
    e * e ≤ e * q ↔ e ≤ q := by
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h he
  · intro h
    exact Nat.mul_le_mul_left e h

/-- Contrapositive: the route fails exactly when the event value exceeds its own
cofactor.  Proved with the axiom-free direction of `Nat.le_of_mul_le_mul_left`. -/
theorem not_sq_le_iff_cofactor_lt {e q : Nat} (he : 0 < e) :
    ¬ (e * e ≤ e * q) ↔ q < e := by
  constructor
  · intro h
    by_cases hq : q < e
    · exact hq
    · exfalso
      apply h
      exact Nat.mul_le_mul_left e (by omega)
  · intro h hle
    have := Nat.le_of_mul_le_mul_left hle he
    omega

/-! ## 2. `q = 3` is attained, so the minimal counterexample is realised

`M = 13`, step `(17, 28) --[9]--> (18, 36)`: `e = 9`, `C - 1 = 27 = 9 * 3`, so
`q = 3 = e / 3 < e`.  `M = 43`, step `(60, 100) --[33]--> (66, 132)`:
`e = 33`, `C - 1 = 99 = 33 * 3`, `q = 3`.  Both are `q = 3` with `e > 3`. -/

theorem w_d18 : d 18 = 9 := by decide
theorem w_D17 : D 17 = 28 := by decide
theorem w_d66 : d 66 = 33 := by decide
theorem w_D65 : D 65 = 100 := by decide

theorem minimal_counterexample_at_M13 :
    d 18 = 9 ∧ D 17 - 1 = 27 ∧ 27 = 9 * 3 ∧ 9 * 9 > D 17 - 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem minimal_counterexample_at_M43 :
    d 66 = 33 ∧ D 65 - 1 = 99 ∧ 99 = 33 * 3 ∧ 33 * 33 > D 65 - 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## 3. A third configuration, with `q = 11 > 3`: `M = 139`

`e = 25`, `C - 1 = 275 = 25 * 11`, so `e * e = 625 > 275` even though `q = 11` is
well above the tree's minimum.  This is what makes the failure a *range* rather
than a single boundary point: any `q` with `3 ≤ q < e` fails. -/

theorem w_d150 : d 150 = 25 := by decide
theorem w_D149 : D 149 = 276 := by decide

theorem counterexample_at_M139 :
    d 150 = 25 ∧ D 149 - 1 = 275 ∧ 275 = 25 * 11 ∧ 25 * 25 > D 149 - 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The generalisation, proved.**  For *any* `e` and `q` with `3 ≤ q < e`, the
`sqrt` inequality fails.  So the counterexample generalises: it is not tied to
`M = 13`, `43` or `139`, only to the cofactor being smaller than the event. -/
theorem sqrt_route_fails_for_every_small_cofactor {e q : Nat}
    (hq : 3 ≤ q) (hlt : q < e) : ¬ (e * e ≤ e * q) := by
  intro h
  have he : 0 < e := by omega
  have hle : e ≤ q := Nat.le_of_mul_le_mul_left h he
  omega

/-- The same statement in the form the route consumes: if the step's event
satisfies `e * q = C ± 1` with `q < e`, then `e * e ≤ C ± 1` is false. -/
theorem sqrt_route_fails_from_step_data {e q n : Nat} (hq : q < e)
    (hn : e * q = n) : ¬ (e * e ≤ n) := by
  intro h
  rw [← hn] at h
  have he : 0 < e := by omega
  have hle : e ≤ q := Nat.le_of_mul_le_mul_left h he
  omega

/-! ## 4. What the failure is *not*: it is not a small-`M` artefact in the algebra

The reduction in Part 1 uses no hypothesis on `M` at all, so the failure mode
survives at any scale where a step has `q < e`.  What the sweep shows (and this
file does not prove) is that in the *real* recurrence the achieving steps are
concentrated at `M = 13, 43, 139`; the algebra above is scale-free. -/

/-- Sanity check on the spelling used in `aE2`: the same refutation, restated
with the `aE2` witness so the two agree. -/
theorem agrees_with_aE2 : ¬ (d 18 * d 18 ≤ D 17 - 1) := by decide

end A166944Research

#print axioms A166944Research.sq_le_iff_le_cofactor
#print axioms A166944Research.sqrt_route_fails_for_every_small_cofactor
#print axioms A166944Research.sqrt_route_fails_from_step_data
#print axioms A166944Research.counterexample_at_M139
