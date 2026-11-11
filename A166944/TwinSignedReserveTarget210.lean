import A166944.TwinReserveTarget210

/-!
# A signed reserve bound sufficient for the unrestricted targets

The signed bound is an open inequality on the original recurrence.
The implication needs only the signed ledger and its first-gap sum.
-/

namespace A166944Research

def ResidualSignedReserveCondition210 : Prop :=
  ∀ {M s C p first : Nat} {balance : Int},
    50000000 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 (primeHorizonPhase 210 (by decide))
      (M + 2) (2 * M - 2) s C [] p first balance →
    2 * (s - (M + 2)) ≤ M → IsAttainedPreviousMaximum M s →
    2 * (((24 * first : Nat) : Int) + balance) ≤
      (M : Int) + 2 * (residualPhaseStartupBound210 : Int)

theorem signed_reserve_of_allocation_condition210 {multiplier : Nat}
    (hreserve : ResidualReserveCondition210 multiplier) : ResidualSignedReserveCondition210 := by
  intro M s C p first balance hM htwin hcanon hledger hs hcap
  obtain ⟨cert⟩ := hreserve hM htwin hcanon hledger hs hcap
  have hbalance := residual_allocation_with_reserve_bound210 cert.allocation
    cert.startup_allowed cert.startup_cap
  rw [cert.sum_exact] at hbalance
  have hhalf := cert.reserve
  rw [Nat.add_mul] at hhalf
  omega

theorem twin_travel_of_signed_reserve_condition210
    (hreserve : ResidualSignedReserveCondition210) : TwinPrimeTravelBoundFrom 50000000 := by
  intro M sf Cf q hM htwin hcanon hpath hmax
  apply canonical_travel_of_capped_residual_net_budget210
    (primeHorizonPhase 210 (by decide)) hcanon hpath hmax
  intro s C p first balance hledger hs hcap
  exact signed_reserve_implies_fifty_million_net_budget210 hM
    (hreserve hM htwin hcanon hledger hs hcap)

theorem record_index_and_twin_prime_of_signed_reserve_condition210
    (hreserve : ResidualSignedReserveCondition210)
    {R n : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) :
    n = R + 2 ∧ IsGreaterTwinPrime R :=
  record_index_and_twin_prime_of_twin_travel_bound_from_45895573
    (twin_travel_from_fifty_million (twin_travel_of_signed_reserve_condition210 hreserve)) hR hn hd hprior

theorem target_of_signed_reserve_condition210 (hreserve : ResidualSignedReserveCondition210) : Target :=
  target_of_twin_travel_from_fifty_million (twin_travel_of_signed_reserve_condition210 hreserve)

theorem unbounded_twin_primes_of_signed_reserve_condition210
    (hreserve : ResidualSignedReserveCondition210) (N : Nat) :
    ∃ R : Nat, N < R ∧ IsGreaterTwinPrime R :=
  unbounded_greater_twin_primes_of_target (target_of_signed_reserve_condition210 hreserve) N

end A166944Research
