import A166944.TwinSignedReserveTarget210

/-! # The budget at the actual first crossing -/

namespace A166944Research

/-- The old signed condition follows from a budget using each unit of
total horizon growth once, with an allowance for the remaining costs. -/
theorem signed_reserve_at_short_prefix_of_growth_bound210 {M s C p first : Nat} {balance : Int}
    (ledger : HasMovingHorizonResidualPhaseBalances210 (primeHorizonPhase 210 (by decide))
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M)
    (growthBound : 2 * (((24 * first : Nat) : Int) + balance) ≤
      ((C - (2 * M - 2) : Nat) : Int) + 47798514) :
    2 * (((24 * first : Nat) : Int) + balance) ≤
      (M : Int) + 2 * (residualPhaseStartupBound210 : Int) := by
  have hh := canonical_horizon_bound_of_short_travel (residual_phase_balances210_path ledger) short
  change _ ≤ (M : Int) + 47798520
  omega

/-- Only candidate first crossings are tested, with the actual gap
and the record cap through the crossing event. This condition is open. -/
def ResidualCrossingBudgetCondition210 : Prop :=
  ∀ {M s C r C' p first : Nat} {balance : Int},
    50000000 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 (primeHorizonPhase 210 (by decide))
      (M + 2) (2 * M - 2) s C [] p first balance →
    IsMovingHorizonStep s C r C' → 2 * (s - (M + 2)) ≤ M → M < 2 * (r - (M + 2)) →
    r - s ≤ Nat.sqrt (4 * (3 * M + 4)) → IsAttainedPreviousMaximum M r →
    ((24 * (first + (r - s)) + 1315 : Nat) : Int) + balance ≤ M

theorem crossing_budget_of_signed_reserve_condition210 (bound : ResidualSignedReserveCondition210) :
    ResidualCrossingBudgetCondition210 := by
  intro M s C r C' p first balance hM htwin hcanon hledger hstep hshort _ hgap hmax
  have hstart := moving_horizon_path_index_le (residual_phase_balances210_path hledger)
  have hsMax : IsAttainedPreviousMaximum M s :=
    ⟨fun j hj hjs => hmax.1 j hj (hjs.trans (Nat.le_of_lt hstep.2.1)),
      ⟨M + 2, by omega, hstart, hcanon⟩⟩
  have hnet := signed_reserve_implies_fifty_million_net_budget210 hM
    (bound hM htwin hcanon hledger hshort hsMax)
  omega

/-- With the actual crossing budget, two thirds of the growth can be
used for the signed sum. The remaining allowance is explicit at 50M. -/
theorem crossing_budget_of_two_thirds_growth210 {M s C r p first : Nat} {balance : Int}
    (hM : 50000000 ≤ M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 (primeHorizonPhase 210 (by decide))
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M)
    (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (growthBound : 3 * (((24 * first : Nat) : Int) + balance) ≤
      2 * ((C - (2 * M - 2) : Nat) : Int) + 47652293) :
    ((24 * (first + (r - s)) + 1315 : Nat) : Int) + balance ≤ M := by
  have hC := canonical_horizon_bound_of_short_travel (residual_phase_balances210_path ledger) short
  have hQ := fifty_million_sqrt_budget hM
  omega

theorem twin_travel_of_crossing_budget_condition210 (bound : ResidualCrossingBudgetCondition210) :
    TwinPrimeTravelBoundFrom 50000000 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_contra hnot
  obtain ⟨s, C, r, C', q, first, balance, hledger, hstep, hr, _, hshort, hcross, hgap, hneeded⟩ :=
    canonical_first_crossing_requires_residual_phase_balances210
      (primeHorizonPhase 210 (by decide)) hcanon hpath (Nat.lt_of_not_ge hnot)
  have hstart := moving_horizon_path_index_le (residual_phase_balances210_path hledger)
  have hrMax : IsAttainedPreviousMaximum M r :=
    ⟨fun j hj hjr => hmax.1 j hj (hjr.trans hr),
      ⟨M + 2, by omega, hstart.trans (Nat.le_of_lt hstep.2.1), hcanon⟩⟩
  have hnet := bound hM htwin hcanon hledger hstep hshort hcross hgap hrMax
  omega

theorem target_of_crossing_budget_condition210 (bound : ResidualCrossingBudgetCondition210) : Target :=
  target_of_twin_travel_from_fifty_million (twin_travel_of_crossing_budget_condition210 bound)

theorem unbounded_twin_primes_of_crossing_budget_condition210
    (bound : ResidualCrossingBudgetCondition210) (N : Nat) :
    ∃ R : Nat, N < R ∧ IsGreaterTwinPrime R :=
  unbounded_greater_twin_primes_of_target (target_of_crossing_budget_condition210 bound) N

end A166944Research
