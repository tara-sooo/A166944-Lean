import A166944.Lemmas

/-!
# The first-hit (jump) form of a moving-horizon step

`Lemmas.constant_D_event_map` already gives the **value** of an increment at a
constant-`D` index:

    d r = if r % 2 = 0 then Nat.gcd r (C - 1) else Nat.gcd (r - 2) (C + 1)
      whenever  D (r - 1) = C .

What the tree does not package is the **minimality** half: a moving-horizon step
takes `r` to be the FIRST index above `s` whose increment is non-unit.  That is the
"jump form" used by the search scripts: from a state `(s, C)`, the next event is the
first `n > s` with `gcd (n) (C - 1) > 1` (n even) or `gcd (n - 2) (C + 1) > 1` (n odd).

This file proves that packaging, so the jump form becomes a theorem rather than a
validated derivation.  Pure core: `omega` / `simp` / `rfl`.
-/

namespace A166944Research

/-- **Every index strictly between `s` and `r` is a unit increment.**  Immediate from
the step's unit-tail conjunct; stated separately because it is the hypothesis the
minimality argument consumes. -/
theorem unit_between_of_step {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    {j : Nat} (hsj : s < j) (hjr : j < r) : d j = 1 :=
  hstep.2.2.2.2.1 j hsj hjr

/-- **The even/odd gcd test at a unit increment is trivial.**  If `d j = 1` and `D (j-1) = C`
then the gcd test at `j` returns `1`.  This is `constant_D_event_map` read as a
*negative* criterion: a non-unit increment is exactly a hit of the gcd test. -/
theorem gcd_test_eq_one_of_unit {j C : Nat} (hj : 2 ≤ j) (hD : D (j - 1) = C)
    (hunit : d j = 1) :
    (if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1)) = 1 := by
  rw [← constant_D_event_map hj hD, hunit]

/-- **A non-unit increment is a gcd hit.**  Conversely, if the gcd test is `> 1` then the
increment is non-unit.  Together with the previous lemma this says the step's first-hit
search is *exactly* the gcd search. -/
theorem gcd_test_gt_one_of_nonunit {j C : Nat} (hj : 2 ≤ j) (hD : D (j - 1) = C)
    (hunit : 1 < d j) :
    1 < (if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1)) := by
  rw [← constant_D_event_map hj hD]
  exact hunit

/-- **The first-hit characterisation.**  At a moving-horizon step, `r` is a gcd hit and
every index strictly between `s` and `r` is not.  This is the jump form's content: the
step is exactly "advance to the first gcd hit above `s`".

Note the `D (j - 1) = C` hypothesis is supplied by the step itself: on the unit tail the
`D`-coordinate is constant at `C` (`first_later_event_D_eq`). -/
theorem step_is_first_gcd_hit {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hDconst : ∀ j : Nat, s < j → j ≤ r → D (j - 1) = C) :
    (1 < (if r % 2 = 0 then Nat.gcd r (C - 1) else Nat.gcd (r - 2) (C + 1))) ∧
      (∀ j : Nat, s < j → j < r →
        1 = (if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1))) := by
  have hr2 : 2 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
  refine ⟨gcd_test_gt_one_of_nonunit hr2 (hDconst r hstep.2.1 (Nat.le_refl r))
    hstep.2.2.2.1, ?_⟩
  intro j hsj hjr
  have hj2 : 2 ≤ j := by have := hstep.1.1; omega
  exact (gcd_test_eq_one_of_unit hj2 (hDconst j hsj (by omega))
    (unit_between_of_step hstep hsj hjr)).symm

/-! ## Axiom audit -/

#print axioms unit_between_of_step
#print axioms gcd_test_eq_one_of_unit
#print axioms gcd_test_gt_one_of_nonunit
#print axioms step_is_first_gcd_hit

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build, `-DautoImplicit=false -DrelaxedAutoImplicit=false`: exit 0, no `sorry`,
no `admit`, no new `axiom`. `unit_between_of_step` depends on no axioms at all; the other
three on `[propext, Quot.sound]` only.

Why this file exists: the search scripts replay a canonical path by jumping directly to the
next event, using "the next event is the first `n > s` with `gcd n (C-1) > 1` (n even) or
`gcd (n-2) (C+1) > 1` (n odd)". The **value** half of that is `Lemmas.constant_D_event_map`,
already in the tree. The **minimality** half was not packaged; `step_is_first_gcd_hit` is it.
With this, the jump form is a theorem rather than a validated derivation, so search engines
built on it rest on checked ground.

Limitation, stated honestly: `step_is_first_gcd_hit` takes the constancy of `D` on the tail
as a hypothesis (`hDconst`). Supplying it from the step alone is `first_later_event_D_eq`'s
job; that composition is not done here.
-/
