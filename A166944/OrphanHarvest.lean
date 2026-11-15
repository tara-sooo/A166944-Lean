/-
  Harvest from an orphan scan of the whole library.
  Every theorem below is kernel-checked; no sorry / admit / axiom / unsafe.
-/
import A166944.CanonicalTravel
import A166944.CountFromIndex
import A166944.TravelReduction
import A166944.BCapDictionary

namespace A166944Research

/-! ## 1. The unconditional `B sf` upper bound (was available, never used) -/

/-- `TravelReduction.canonical_path_state_bound` needs no side hypothesis, so
`Cf ≤ 2*sf` holds at EVERY canonical replay.  With the dictionary
`B sf + sf = Cf + 2` this caps the reservoir by the index. -/
theorem canonical_B_sf_le_index_add_two {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    B sf ≤ sf + 2 := by
  have hsb := canonical_path_state_bound hpath
  have hstate := moving_horizon_path_endpoint hpath
  have hB := moving_horizon_state_B_add_index hstate
  omega

/-! ## 2. The unconditional event-count / index coupling -/

/-- The event count is pinned to the terminal index: `p + M ≤ sf + 1`, i.e.
`p ≤ sf - M + 1`.  Uses only the count bound plus the unconditional state bound --
neither `ExitBand`'s `sf ≤ 2*M - 4` nor the event-count criterion. -/
theorem canonical_count_add_M_le_index_succ {M sf Cf p : Nat}
    (hstate : IsMovingHorizonState sf Cf)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    p + M ≤ sf + 1 := by
  have hres := canonical_count_le_reservoir hstate hpath
  have hB := moving_horizon_state_B_add_index hstate
  have hge := horizon_ge_start_add_twice_count hpath
  have hCf : B sf + sf - 2 = Cf := by omega
  rw [hCf] at hres
  have h2M : 2 * M - 2 ≤ Cf := by omega
  have hexp : 2 * p + (2 * M - 2) ≤ Cf := by omega
  have hsb := canonical_path_state_bound hpath
  omega

/-! ## 3. The existing `B`-lower-bound route is a reformulation, not a reduction -/

/-- `BCapDictionary.canonical_index_cap_of_horizon_and_B_sf` reduces the index cap
to `3*M + 8 ≤ 2 * B sf`.  That hypothesis, with the unconditional state bound and
the dictionary, already forces the cap to be an EQUALITY, `2*sf = 3*M+4` -- which
is strictly stronger than the conclusion `2*sf ≤ 3*M+4`.  So the route cannot
weaken the target. -/
theorem B_lower_bound_route_forces_equality {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hhor : Cf ≤ 3 * M + 4) (hlow : 3 * M + 8 ≤ 2 * B sf) :
    2 * sf = 3 * M + 4 := by
  have hstate := moving_horizon_path_endpoint hpath
  have hcap := canonical_index_cap_of_horizon_and_B_sf hstate hhor hlow
  have hsb := canonical_path_state_bound hpath
  have hB := moving_horizon_state_B_add_index hstate
  omega

/-! ## 4. The count-from-index route is vacuous -/

/-- Since `p` is only pinned to `sf` (result 2) and never pinned small
independently, the travel bound `sf - s ≤ p * sqrt(4(U+1))` absorbs any `sf`:
whenever the count bound is *feasible* (`M ≤ sf + 1`), there is a pair `(Cf, p)`
satisfying BOTH it and the travel bound.  Route 2 of `REACH.md` therefore does not
close: `p` and `sf` must be bounded jointly, not in sequence.

Note the shape this exposes: with `q := sf - M` the count bound reads `p ≤ q + 1`
and travel reads `q ≤ p * sqrt(4(3M+4))`.  Chaining gives `q ≤ (q+1)*sqrt(...)`,
which holds for every `q >= 0` because `sqrt(...) >= 1`.  So the two bounds are
jointly satisfiable for *every* travel distance -- the route has no content until
`p` is bounded independently of `sf`. -/
theorem count_index_route_is_vacuous (M sf : Nat) (hfeas : M ≤ sf + 1) :
    ∃ _Cf p : Nat,
      p + M ≤ sf + 1 ∧
        sf - (M + 2) ≤ p * isqrt (4 * (3 * M + 4 + 1)) := by
  refine ⟨2 * sf, sf + 1 - M, ?_, ?_⟩
  · show sf + 1 - M + M ≤ sf + 1
    rw [Nat.sub_add_cancel hfeas]
    exact Nat.le_refl _
  have hroot : 1 ≤ isqrt (4 * (3 * M + 4 + 1)) := by
    rcases Nat.eq_zero_or_pos (isqrt (4 * (3 * M + 4 + 1))) with h0 | hpos
    · exfalso
      have hlt := lt_succ_isqrt (4 * (3 * M + 4 + 1))
      rw [h0] at hlt
      omega
    · exact hpos
  have hq : sf - (M + 2) ≤ sf + 1 - M := by omega
  calc sf - (M + 2) ≤ sf + 1 - M := hq
    _ = (sf + 1 - M) * 1 := (Nat.mul_one _).symm
    _ ≤ (sf + 1 - M) * isqrt (4 * (3 * M + 4 + 1)) :=
        Nat.mul_le_mul_left _ hroot

/-- The companion: the `B sf` form of the count bound is also unconditional. -/
theorem canonical_count_le_B_sf {M sf Cf p : Nat}
    (hstate : IsMovingHorizonState sf Cf)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    2 * p ≤ B sf + sf - 2 * M := by
  have hres := canonical_count_le_reservoir hstate hpath
  have hB := moving_horizon_state_B_add_index hstate
  have hge := horizon_ge_start_add_twice_count hpath
  have hCf : B sf + sf - 2 = Cf := by omega
  rw [hCf] at hres
  have h2M : 2 * M - 2 ≤ Cf := by omega
  have hexp : 2 * p + (2 * M - 2) ≤ Cf := by omega
  omega

#print axioms canonical_B_sf_le_index_add_two
#print axioms canonical_count_add_M_le_index_succ
#print axioms B_lower_bound_route_forces_equality
#print axioms count_index_route_is_vacuous
#print axioms canonical_count_le_B_sf

end A166944Research
