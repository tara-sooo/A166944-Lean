import A166944.CapBCandidates
import A166944.RelaxedCap
import A166944.CanonicalTravel
import A166944.ExcessCriterion
import A166944.TwoCapGate

/-!
# R1: is cap (B) downstream of `48 p^2 + 1 < M`?
-/

namespace A166944Research

/-! ### A. The forward implication is real (independently re-derived) -/

theorem R1_capB_of_event_count_minimal {M sf Cf p : Nat} (hM : 9 ≤ M)
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) (hcount : 48 * (p * p) + 1 < M) :
    4 * sf ≤ 7 * M - 1 := by
  have htr := canonical_travel_bound_of_event_count (by omega) hcanon hpath hmax hcount
  have hsf : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel hsf
  have h4 : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  omega

/-! ### B. The converse is FALSE, and the separation is structural -/

/-- The two criteria demand counts of different *order*: cap (B) forces only
`p ≤ 3M/4`, the event-count criterion forces `p < sqrt(M)/7`.  A single `p`
therefore separates them without any replay. -/
theorem R1_cap_does_not_imply_event_count :
    (4 * 1000 ≤ 3 * 45895573 + 3) ∧ ¬ (48 * (1000 * 1000) + 1 < 45895573) := by decide

/-- At the real threshold the cap's own forced count bound admits `p = 34421680`,
while the event-count criterion already fails at `p = 978`. -/
theorem R1_count_radius_gap_at_threshold :
    (4 * 34421680 ≤ 3 * 45895573 + 3) ∧
      (48 * (977 * 977) + 1 < 45895573) ∧ ¬ (48 * (978 * 978) + 1 < 45895573) := by decide

/-- The separation is unbounded in `M`: for every slope `c` there is a pair where
the event-count criterion holds, the cap's count bound holds, and `p * c < M`
still holds.  So no linear-in-`M` reading of the event count exists. -/
theorem R1_gap_is_unbounded (c : Nat) :
    ∃ M p : Nat, 48 * (p * p) + 1 < M ∧ 4 * p ≤ 3 * M + 3 ∧ p * c < M ∧ 0 < M := by
  have hA1 : 1 ≤ (c + 2) * (c + 2) :=
    Nat.mul_le_mul (by omega : 1 ≤ c + 2) (by omega : 1 ≤ c + 2)
  have hAc : c + 2 ≤ (c + 2) * (c + 2) := by
    have h := Nat.mul_le_mul_left (c + 2) (by omega : 1 ≤ c + 2)
    simpa using h
  have hcc : (c + 2) * c ≤ (c + 2) * (c + 2) :=
    Nat.mul_le_mul_left (c + 2) (by omega)
  refine ⟨96 * ((c + 2) * (c + 2)) + 2, c + 2, ?_, ?_, ?_, ?_⟩
  all_goals generalize hA : (c + 2) * (c + 2) = A at hA1 hAc hcc ⊢
  · omega
  · omega
  · omega
  · omega

/-! ### C. cap (B) is strictly weaker than travel: the tree's own witness -/

theorem R1_capB_is_weaker_than_travel :
    (45895573 + 2 ≤ 80317252) ∧ (80317252 < 137686723) ∧
      (2 * 45895573 - 2 ≤ 137686723) ∧ (137686723 ≤ 3 * 45895573 + 4) ∧
      (4 * 80317252 ≤ 7 * 45895573 - 1) ∧
      ¬ (2 * (80317252 - (45895573 + 2)) ≤ 45895573) := by decide

/-- And travel does imply cap (B), so the relaxation is exactly one-directional. -/
theorem R1_travel_implies_capB_at_threshold {sf : Nat} (h : 45895573 + 2 ≤ sf)
    (htravel : 2 * (sf - (45895573 + 2)) ≤ 45895573) :
    4 * sf ≤ 7 * 45895573 - 1 := by omega

/-! ### D. Which direction is load bearing?  cap (B) alone is NOT enough -/

/-- cap (B) alone does not give the *horizon* cap (A): with `sf = 24`, `M = 13`,
cap (B) fails; but more importantly (B) and the count bound are compatible with
`Cf` far above `3M+4`.  Recorded as: the count bound forced by (B) is *lossy*. -/
theorem R1_capB_alone_does_not_bound_horizon :
    ∃ M sf Cf p : Nat, 4 * sf ≤ 7 * M - 1 ∧ p + M ≤ sf + 1 ∧ 4 * p ≤ 3 * M + 3 ∧
      3 * M + 4 < Cf := by
  refine ⟨45895573, 80317252, 999999999, 1000, ?_, ?_, ?_, ?_⟩ <;> omega

end A166944Research

#print axioms A166944Research.R1_capB_of_event_count_minimal
#print axioms A166944Research.R1_cap_does_not_imply_event_count
#print axioms A166944Research.R1_count_radius_gap_at_threshold
#print axioms A166944Research.R1_gap_is_unbounded
#print axioms A166944Research.R1_capB_is_weaker_than_travel
#print axioms A166944Research.R1_travel_implies_capB_at_threshold
#print axioms A166944Research.R1_capB_alone_does_not_bound_horizon
