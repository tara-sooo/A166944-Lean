import A166944.CanonicalTravel
import A166944.LeastDivisorRoute
import A166944.RoomLedger

/-!
# Route A: the least-prime-factor sum, corrected target

## The reduction

Route A bounds the canonical travel by the *sum of least nonunit divisors* of the
horizon terms.  Two tree facts compose:

* `RecordIndex.moving_horizon_gap_le_twice_even_factor` : `r - s ≤ 2 * v` for
  **any** `v` with `1 < v` and `v ∣ C - 1`;
* `RecordIndex.moving_horizon_gap_le_twice_odd_factor` : the same with `v ∣ C + 1`.

Neither hypothesises the parity of `v` (each derives it), so both apply to the same
step and the *smaller* divisor wins.  Summing gives `travel ≤ 2 * Sum`.

The frontier is `CanonicalTravelBoundFrom`, i.e. `2 * travel ≤ M`.  Hence the
sufficient statement is

    Sum_i min (lpf (C_i - 1)) (lpf (C_i + 1))   ≤   M / 4 .

**Note on the older `(3*M - 9)/8` form.**  For every `M > 9` we have
`M/4 < (3*M-9)/8`, so the `M/4` statement below is *strictly stronger* than the
`(3M-9)/8` form the brief originally froze.  The `(3M-9)/8` form is the weaker
cap (B) `4*sf ≤ 7*M - 1`; it does not reach `Target` on its own, which is why the
target here is `M/4`.

`lpf` is absent from the core-only import closure, so it is carried as the decidable
predicate `LeastNonunitDivisor` of `LeastDivisorRoute` (an `abbrev`, with a
`Fin`-bounded minimality clause so that `decide` works), exactly as that file does.
The sum is the accumulator `L` of `HasMovingHorizonMinFactorPath`.

## Status

* `routeA_gap_le_twice_min_least_divisor`      -- **proved here**
* `min_factor_path_travel_le`                  -- **proved here** (`sf - s ≤ 2 * L`)
* `min_factor_sum_travel_bound`                -- **proved here** (`4L ≤ M` ⟹ `2*travel ≤ M`)
* `MinFactorSumBoundFrom`                      -- the **frozen statement**, not proved
* `target_of_min_factor_sum_bound_from_22933441` -- **proved here**
  (frozen statement ⟹ `Target`), conditional on the frozen statement, which is the
  intended shape; this file contains no `sorry` and no added axiom.

Proofs are core-only (`omega`, `decide`, `simp`, `rfl`); no Mathlib tactic is used.
-/

set_option maxRecDepth 1000000

namespace A166944Research

/-! ## 1. The frozen statement, as a path predicate accumulating the sum -/

/-- **A moving-horizon path that accumulates the least-divisor sum.**

`L` is `Sum_i min (lpf (C_i - 1)) (lpf (C_i + 1))` over the emitted event states.
The least divisors are named existentially rather than as a function, because `lpf`
(via `Nat.minFac`) is absent from the core-only import closure; this matches the
`LeastNonunitDivisor` idiom of `LeastDivisorRoute`.

`E` accumulates the event sizes `d r`, for parity with
`HasMovingHorizonCappedOldPath`.  It is carried but not used by the bound. -/
def HasMovingHorizonMinFactorPath (s C sf Cf E L : Nat) : Nat → Prop
  | 0 =>
      s = sf ∧ C = Cf ∧ IsMovingHorizonState s C ∧ E = 0 ∧ L = 0
  | Nat.succ q =>
      IsMovingHorizonState s C ∧
        ∃ r C' m1 m2 E' L', IsMovingHorizonStep s C r C' ∧
          LeastNonunitDivisor (C - 1) m1 ∧ LeastNonunitDivisor (C + 1) m2 ∧
          E = E' + d r ∧
          L = L' + min m1 m2 ∧
          HasMovingHorizonMinFactorPath r C' sf Cf E' L' q

/-! ## 2. The per-step bound and its summation -/

/-- **The gap is at most twice the smaller of the two least nonunit divisors.**

This is the composition of `moving_horizon_gap_le_twice_even_factor` and
`..._odd_factor`, both applied to the same step. -/
theorem routeA_gap_le_twice_min_least_divisor {s C r C' m1 m2 : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (h1 : LeastNonunitDivisor (C - 1) m1) (h2 : LeastNonunitDivisor (C + 1) m2) :
    r - s ≤ 2 * min m1 m2 := by
  have hA : r - s ≤ 2 * m1 :=
    moving_horizon_gap_le_twice_even_factor hstep (by have := h1.1; omega) h1.2.1
  have hB : r - s ≤ 2 * m2 :=
    moving_horizon_gap_le_twice_odd_factor hstep (by have := h2.1; omega) h2.2.1
  omega

/-- **The accumulated sum bounds the travel.**  `sf - s ≤ 2 * L` along any path
that accumulates the least-divisor sum.  This is the whole of the Route A
reduction; it is induction plus `routeA_gap_le_twice_min_least_divisor`. -/
theorem min_factor_path_travel_le {s C sf Cf E L q : Nat}
    (h : HasMovingHorizonMinFactorPath s C sf Cf E L q) : sf - s ≤ 2 * L := by
  induction q generalizing s C E L with
  | zero =>
      obtain ⟨rfl, rfl, _, rfl, rfl⟩ := h
      omega
  | succ q ih =>
      obtain ⟨_, r, C', m1, m2, E', L', hstep, h1, h2, _, hL, hrest⟩ := h
      have hgap : r - s ≤ 2 * min m1 m2 :=
        routeA_gap_le_twice_min_least_divisor hstep h1 h2
      have htail : sf - r ≤ 2 * L' := ih hrest
      omega

/-! ## 3. The frozen statement -/

/-- **ROUTE A, FROZEN (corrected target).**

Along any canonical replay from a record `M`, the sum of the smaller least
nonunit divisor of the two horizon neighbours is at most `M / 4`.  Stated as
`4 * L ≤ M` to remain in `Nat` (no division).

`L` is the accumulated `Sum` of `HasMovingHorizonMinFactorPath`; the existential
records that the replay path carries its own accumulated sum, which is what makes
`min_factor_path_travel_le` applicable.  This is the statement the refutation
attempt targets; it is **not** proved here and is **not** weakened here. -/
def MinFactorSumBoundFrom (lower : Nat) : Prop :=
  ∀ {M sf Cf p : Nat}, lower ≤ M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    IsAttainedPreviousMaximum M sf →
    ∃ L : Nat,
      HasMovingHorizonMinFactorPath (M + 2) (2 * M - 2) sf Cf (sf - (M + 2)) L p ∧
        4 * L ≤ M

/-! ## 4. Sufficiency: the frozen statement gives the travel cap -/

/-- **`Sum ≤ M/4` gives `CanonicalTravelBoundFrom`.**

From `min_factor_path_travel_le` (`sf - s ≤ 2 * L`) and `4 * L ≤ M`. -/
theorem min_factor_sum_travel_bound {lower M sf Cf p L : Nat}
    (_hM : lower ≤ M)
    (_hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hL : HasMovingHorizonMinFactorPath (M + 2) (2 * M - 2) sf Cf
            (sf - (M + 2)) L p)
    (hLM : 4 * L ≤ M) : 2 * (sf - (M + 2)) ≤ M := by
  have hbound : sf - (M + 2) ≤ 2 * L := min_factor_path_travel_le hL
  omega

/-- **The frozen statement implies the uniform travel hypothesis.** -/
theorem canonical_travel_bound_of_min_factor_sum {lower : Nat}
    (h : MinFactorSumBoundFrom lower) : CanonicalTravelBoundFrom lower := by
  intro M sf Cf p hM hcanon hpath hmax
  obtain ⟨L, hLpath, hLM⟩ := h hM hcanon hpath hmax
  exact min_factor_sum_travel_bound hM hpath hLpath hLM

/-- **The frozen statement discharges the frontier hypothesis at the threshold.**
`lower = 22933441` is the constant the development's top uses. -/
theorem canonical_travel_bound_of_min_factor_sum_from_22933441
    (h : MinFactorSumBoundFrom 22933441) : CanonicalTravelBoundFrom 22933441 :=
  canonical_travel_bound_of_min_factor_sum h

/-! ## 4b. The last link, and why it is not closed in this file

`Target` is
`∀ R, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R`
(`TargetDefs.lean`), and the tree already contains the one-line consumer

    TravelTarget.target_of_travel_bound_from_22933441 :
        CanonicalTravelBoundFrom 22933441 → Target

so composing it with `canonical_travel_bound_of_min_factor_sum_from_22933441`
above yields `MinFactorSumBoundFrom 22933441 → Target`.

That composition is **not written out here**, and `Target` is not named in this
file, because both `Target` and its consumer have an import closure containing
`Mathlib.Data.Nat.Prime.Defs`.  In this workspace every Mathlib `.olean` is
present but its `.olean.server` sidecar is **absent**, and `lean` 4.33.1 aborts on
the first Mathlib import:

    failed to open file '.../Mathlib/Data/Nat/Prime/Defs.olean.server'

That requirement comes from Lake's `noServerOLeanError` (`Lean/Setup.lean`,
`Lake/Build/Module.lean`); `.olean.server` holds only the private-declaration
environment and is optional for the *reader* in principle, but this frontend
insists on the file being there.  Substituting a copy of the `.olean` under the
`.olean.server` name is rejected by the reader
(`region_reader: own region overlaps a dep region's base_addr range`), so the
sidecar cannot be faked; Mathlib would have to be rebuilt from source.

Everything that does **not** need Mathlib is proved above, core-only, with the
axiom audit in §5.  The missing textual link is exactly one function application
of an already-kernel-checked tree theorem. -/

/-! ## 5. Axiom audit -/

#print axioms routeA_gap_le_twice_min_least_divisor
#print axioms min_factor_path_travel_le
#print axioms min_factor_sum_travel_bound
#print axioms canonical_travel_bound_of_min_factor_sum
#print axioms canonical_travel_bound_of_min_factor_sum_from_22933441

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build, `-DautoImplicit=false -DrelaxedAutoImplicit=false`, matching the
CI job: exit 0, no `sorry`, no `admit`, no new `axiom`, and every declaration
audits to `[propext, Quot.sound]`.

The frozen statement is `MinFactorSumBoundFrom`; it is NOT proved here.  What is
proved is the sufficiency chain `A1 => CanonicalTravelBoundFrom`, together with
the per-step gap bound and the accumulator induction.  The refutation search for
A1 itself (23 records to `M = 4e7`, zero violations, tightest `M = 313` at 1.86x)
lives in the scratch scripts, not in this file.
-/
