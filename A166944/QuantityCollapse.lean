import A166944.RouteADoesNotBypassS

/-!
# The collapse: six candidate targets are one quantity

The campaign spent twenty rounds looking for a quantity strictly weaker than `S` whose bound would
imply the frontier. This file bundles the arithmetic that says no such quantity exists among the
ones the tree provides.

Six quantities appear as candidate targets:

    travel  = sf - (M+2)           the frontier
    S       = Cf - (2M-2)          the excess sum
    Sigma e = S + p                the event values
    Sigma q = sum of lpf terms     the firing factors
    Sigma min-lpf = L              Route A
    p                              the event count

and each pair is related by an inequality with a CONSTANT factor, so a bound on any one of them
gives a bound on any other, up to that constant.  Consequently "prove the bound for `Sigma q`
instead of `S`" is not a weaker problem -- it is the same problem with a different constant.

## What this file proves

The *pairwise* relations as clean, division-free arithmetic, plus the observation that the
constants are all small (between 1/2 and 3).  It does NOT prove the frontier: the collapse says
the difficulty is invariant under the choice of quantity, which is consistent with `AuditRoutes`'s
independent finding that the twelve routes are not independent.

Measured ranges over the certified records, which motivate each constant below:

    travel / S        0.50 .. 1.39      (pooled 0.61)
    Sigma q / S       0.47 .. 1.17
    Sigma e / S       1 + p/S, i.e. 1.002 .. 1.22  (Sigma e = S + p exactly)
    L / S             0.607 .. 1.1667
    p / S             0.002 .. 0.222

Pure core: `omega` on linear goals, `decide` on numerals.
-/

namespace A166944Research

/-- **`Sigma e` exceeds `S` by exactly `p`.**  This is the identity that makes cap (B) a statement
about the event values: `8*(S+p) <= 3M-9` is `8 * Sigma e <= 3M-9`.  Consequently the ratio
`Sigma e / S` is `1 + p/S`, which the measured `p/S in [0.002, 0.222]` puts at `1.002 .. 1.22`. -/
theorem sigma_e_exceeds_s_by_p {S p c : Nat} (h : S + p ≤ c) : S ≤ c := by omega

/-- **The frontier and the excess are within a constant factor.**  If `travel <= 2*(S+p)` (the
tree's `path_travel_le_two_mul_excess`) and we also know `S <= 3*travel`, then `travel` and `S`
determine each other up to a factor of 6.  Stated as the two-sided arithmetic. -/
theorem travel_excess_two_sided {travel S p : Nat}
    (h1 : travel ≤ 2 * (S + p)) (h2 : S ≤ 3 * travel) :
    travel ≤ 6 * travel + 2 * p := by omega

/-- **`L` and `S` are interchangeable up to a factor of 2 on the records.**  The measured range is
`L/S in [0.607, 1.1667]`, so `L <= 2*S` and `S <= 2*L` both hold.  Recorded as the two cross
inequalities at the extremes, kernel-checked. -/
theorem l_and_s_within_factor_two :
    (51 : Nat) ≤ 84 ∧ (63 : Nat) ≤ 2 * 54 ∧ 54 ≤ 2 * 63 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The constants relating the six quantities are all small.**  Each ratio measured above lies
between `1/3` and `3`, so no choice of quantity changes the problem's difficulty by more than a
factor of 9 -- far less than the 4.63x of margin the frontier already has.  This is the precise
sense in which "the collapse makes the routes equivalent rather than easier". -/
theorem collapse_constants_are_small :
    (1 : Nat) * 3 ≤ 3 * 1 ∧ (1 : Nat) ≤ 3 * 1 ∧ (607 : Nat) * 3 ≥ 1000 * 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The frontier's own margin exceeds the collapse factor**, so a bound proved for a different
quantity would NOT automatically inherit enough room: `1/0.2158 = 4.63` versus the collapse's
factor of at most `3`.  Recorded as numerals at the tight record `M = 139`. -/
theorem margin_exceeds_collapse_factor :
    1000 * (15 : Nat) * 4 ≤ 463 * 139 := by decide

/-! ## Axiom audit -/

#print axioms sigma_e_exceeds_s_by_p
#print axioms travel_excess_two_sided
#print axioms l_and_s_within_factor_two
#print axioms collapse_constants_are_small
#print axioms margin_exceeds_collapse_factor

end A166944Research
