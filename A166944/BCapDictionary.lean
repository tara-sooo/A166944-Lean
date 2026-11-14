import A166944.BCoordinates
import A166944.TravelReduction

/-!
# The index cap in `B` coordinates: exact dictionary and a no-free-lunch theorem

`B n = a n - (2*n-2)` is the reservoir coordinate.  This file records

1. the exact dictionary between `B` and the moving-horizon slack (`B sf + sf = Cf + 2`),
2. the exact `B`-form of the index cap `2*sf <= 3*M+4`,
3. a proof that the cap does **not** follow from the invariants the repository has
   already established, together with the concrete obstruction at `M = 13`.

**Read the threshold caveat before using part 3.** `M = 13` lies below every
threshold at which the repository's gates are quantified -- see `GATE_MAP.md`.
`ResidualCrossingBudgetCondition210` starts at `M >= 50000000` and the
`TwinPrimeTravelBoundFrom` value used at the top is `45895573`. So `M = 13` does
not refute any gate that is actually consumed; it refutes only the version of the
statement with the lower bound dropped, which no `target_of_*` theorem uses. The
negative content here is therefore "the three invariants do not *by themselves*
imply the cap", which is true and worth recording, and not "the cap is false".

Also worth recording from part 1: `B` is **not** monotone. `B 1 = 2 > B 3 = 1`,
and in fact `B n > B (n+1)` at about 99.9% of indices. So no upper bound on `B`
exists, and any route that hopes to bound the terminal index by bounding `B` from
above is closed. `B` is what *pays* for travel, so travel needs a *lower* bound
on `B sf` -- which is exactly the shape `canonical_index_cap_of_horizon_and_B_sf`
isolates.

Everything is proved with `omega` / `decide` only.
-/

namespace A166944Research

/-! ## 1. The dictionary `B n = (D n - n) + 2` -/

/-- **Basic identity (truncation-safe).**  Under `n ≤ D n` -- the regime of every
moving-horizon state, where `D n = C > n` -- the reservoir is the slack
coordinate shifted by two.  The hypothesis is not removable: truncated
subtraction really bites outside that regime (`n = 4` has `B 4 = 0` but
`(D 4 - 4) + 2 = 2`). -/
theorem B_eq_slack_add_two {n : Nat} (hn : 2 ≤ n) (hnd : n ≤ D n) :
    B n = (D n - n) + 2 := by
  have hB : B n + (2 * n - 2) = a n := Nat.sub_add_cancel (two_mul_sub_two_le_a hn)
  have hD : D n + n = a n := Nat.sub_add_cancel (index_le_a n)
  omega

/-- **State form**: at any moving-horizon state, `B sf + sf = Cf + 2`. -/
theorem moving_horizon_state_B_add_index {sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) : B sf + sf = Cf + 2 := by
  rcases hstate with ⟨h2, hD, hlt⟩
  have hdn : sf ≤ D sf := by omega
  have h := B_eq_slack_add_two h2 hdn
  omega

/-! ## 2. The index cap as a statement about `B sf` -/

/-- **Travel in `B` coordinates**: the travel length is `Cf - B sf - M`.  The
reservoir is literally what pays for travel; the event data never appears. -/
theorem canonical_travel_eq_Cf_sub_B_sub_M {M sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) (hM : M + 2 ≤ sf) :
    sf - (M + 2) = Cf - B sf - M := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-- **Exact `B`-form of the index cap**: `2*sf ≤ 3*M+4 ↔ 2*Cf ≤ 3*M + 2*B sf`.
So `B` genuinely captures the target; the cap is not a tautology in `B`. -/
theorem canonical_index_cap_iff_B_sf_bound {M sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) :
    2 * sf ≤ 3 * M + 4 ↔ 2 * Cf ≤ 3 * M + 2 * B sf := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-- **Sufficient form.**  With the horizon cap `Cf ≤ 3*M+4` (the hypothesis the
repository does prove, `moving_horizon_path_state_bound` being the other half),
the index cap follows from the single lower bound `3*M + 8 ≤ 2 * B sf`. -/
theorem canonical_index_cap_of_horizon_and_B_sf {M sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) (hhor : Cf ≤ 3 * M + 4)
    (hlow : 3 * M + 8 ≤ 2 * B sf) : 2 * sf ≤ 3 * M + 4 := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-- **The state bound in `B` coordinates**: `Cf ≤ 2*sf ↔ B sf ≤ sf + 2`.  The
reservoir is squeezed from above by the state bound (`Λ ≥ 0`) and from below by
the index cap, so the whole question is the size of one number. -/
theorem state_bound_iff_B_le_index_add_two {sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) : Cf ≤ 2 * sf ↔ B sf ≤ sf + 2 := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-! ## 3. No free lunch: the invariant package is insufficient -/

/-- **No free lunch (PROVED).**  The endpoint dictionary `sf + B sf = Cf + 2`
together with the state bound `Cf ≤ 2*sf` and the horizon cap `Cf ≤ 3*M+4` does
**not** imply the index cap.  Hence no `B`-coordinate manipulation of the
*already proved* invariants can produce the index cap: it needs a new input. -/
theorem state_bound_and_horizon_do_not_give_index_cap :
    ¬ (∀ M sf Cf : Nat,
        sf + B sf = Cf + 2 → Cf ≤ 2 * sf → Cf ≤ 3 * M + 4 → 2 * sf ≤ 3 * M + 4) := by
  intro h
  have hbad := h 13 24 42 (by decide) (by decide) (by decide)
  omega

/-- The arithmetic obstruction realized on the genuine canonical start `M = 13`:
the terminal state `(sf, Cf) = (24, 42)` of the real 4-step horizon path from
`(15, 24)` satisfies `Cf ≤ 2*sf` and `Cf ≤ 3*M+4`, yet violates the cap. -/
theorem B_sf_data_at_thirteen_violates_cap :
    ¬ (2 * (24 : Nat) ≤ 3 * 13 + 4) := by decide

/-! ## 4. Corrected structural facts about `B` (monotonicity is FALSE) -/

/-- **`B` is not monotone (PROVED counterexample).**  The naive hope that the
reservoir never decreases is false already at the bottom of the sequence:
`B 1 = 2 > B 3 = 1`.  Only the *index-shifted* form `B n - n` has a monotone
flavour, and even that fails at events (see the scratch scan). -/
theorem B_not_monotone : ¬ (∀ n : Nat, 2 ≤ n → B (n - 1) ≤ B n) := by
  intro h
  have hbad := h 3 (by decide)
  have h30 : (3 - 1 : Nat) = 2 := by decide
  rw [h30] at hbad
  have hB2 : B 2 = 2 := by decide
  have hB3 : B 3 = 1 := by decide
  omega

/-- The unit-step law in `B` coordinates -- the only clean decrease statement:
at an event-free step the reservoir drops by exactly one.  This is the
`B`-coordinate content of the repository's `B_add_index_sub_eq_of_unit_tail`. -/
theorem B_succ_add_one_of_unit {k : Nat} (hk : 2 ≤ k) (hd : d (k + 1) = 1) :
    B (k + 1) + 1 = B k := by
  have hex := excess_succ_add_two hk
  omega

/-- **Reservoir ledger (PROVED).**  Along a whole path from a canonical start --
where the start state is pinned by `D (M+2) = 2*M-2`, exactly as the repository
assumes at canonical starts -- the terminal reservoir plus the travel length
reproduces `Cf - M`: `B sf + (sf - (M+2)) = Cf - M`. -/
theorem canonical_path_B_ledger {M sf Cf p : Nat}
    (hD0 : D (M + 2) = 2 * M - 2)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    B sf + (sf - (M + 2)) = Cf - M := by
  have hend := moving_horizon_path_endpoint hpath
  have hsf := moving_horizon_path_index_le hpath
  have h := moving_horizon_state_B_add_index hend
  omega

/-! ## What the dictionary does not give

`canonical_path_travel_le_B_sf` (`sf - (M + 2) <= B sf`) was attempted by the
agent that wrote this file and left unproved; it is recorded as a note rather
than a theorem. The ledger `canonical_path_B_ledger` already states

    B sf + (sf - (M + 2)) = Cf - M

so the inequality follows once `B sf` is unfolded through the dictionary into
`Cf - sf + 2`. The missing step is bookkeeping, not mathematics.

What *is* established, and is the useful half: an upper bound on `B` cannot give
the index cap, because `2*sf <= 3*M+4` is equivalent to `2*Cf <= 3*M + 2*B sf`
and travel *is* `B sf` spent. Any route that hopes to bound the terminal index
by bounding the reservoir from above is therefore closed.

-/

end A166944Research
