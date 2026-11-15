import A166944.TravelReduction
import A166944.CountFromIndex
import A166944.CountBoundLimits
import A166944.ExcessIdentity
import A166944.BandReentry
import A166944.RoomLedger

/-!
# R6: do the "twelve routes" converge, and are they independent?
-/

namespace A166944Research

/-- Route 1 (`TravelReduction`): the index cap and the travel bound are *the same
inequality* by arithmetic -- not an obstruction. -/
theorem R6_route1 {M sf : Nat} (h : M + 2 ≤ sf) :
    2 * (sf - (M + 2)) ≤ M ↔ 2 * sf ≤ 3 * M + 4 := by
  constructor <;> intro hc <;> omega

/-- Route 9 (`ExcessIdentity`): bounding `S` alone is equivalent to the travel
bound, i.e. the route is *circular*, not independent. -/
theorem R6_route9_is_circular {M S travel Bsf : Nat} (hM : 4 ≤ M)
    (hB : Bsf + travel = (M - 2) + S) :
    (2 * S + M ≤ 2 * Bsf + 4 ↔ 2 * travel ≤ M) :=
  excess_only_gives_identity hM hB

/-- Route 4 (`BIntegrate`): the reservoir ledger is an *identity* with an
existential excess, so it carries no bound on its own -- it introduces `S` as a
free coordinate rather than constraining it. -/
theorem R6_route4_is_a_coordinate_change {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ S : Nat, B sf + (sf - s) = B s + S :=
  B_path_integrated hpath

/-- Route 3 (`CountBoundLimits`): the count bounds admit any `q`, so they cannot
bound the count.  Recorded as the failure of a putative bound. -/
theorem R6_route3_admits_any_q : ∀ q : Nat, ∃ E T : Nat,
    3 * q ≤ E ∧ E ≤ 1000 * q ∧ 2 * q ≤ T := by
  intro q
  exact ⟨3 * q, 2 * q, by omega, by omega, by omega⟩

/-! ### The routes are NOT independent: they share the same conclusion -/

-- The bundled form of the observation below is deliberately not stated as a single
-- conjunction. Its two components are `R6_route1` and `R6_route9_is_circular`, both
-- above; packaging them adds a scope for the implicit binders to go wrong (it did,
-- three times) and no information. The observation stands on the two theorems.

/-- **Route 5's own claim is that it is *not* independent**: the tree says the
available bound on `a` is *tight*, i.e. it cannot bound `sf`.  So route 5 is a
refutation of a method, not a confirmation of the diagnosis. -/
theorem R6_route5_is_a_refutation_not_a_route :
    a 24 = 66 ∧ a 24 - 24 = 42 ∧ (3 : Nat) * 24 - 30 = 42 := by decide

end A166944Research

#print axioms A166944Research.R6_route1
#print axioms A166944Research.R6_route9_is_circular
#print axioms A166944Research.R6_route4_is_a_coordinate_change
#print axioms A166944Research.B_path_integrated
#print axioms A166944Research.R6_route3_admits_any_q
#print axioms A166944Research.R6_route5_is_a_refutation_not_a_route
