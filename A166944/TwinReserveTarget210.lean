import A166944.ResidualThreshold210
import A166944.VerifiedFiftyMillionBridge

/-!
# Exact remaining reserve hypothesis for the unrestricted targets

The condition below is open. It requires an actual-prefix allocation,
the proved startup restrictions, and the half-reserve inequality. The
finite interval below fifty million is discharged independently.
-/

namespace A166944Research

def ResidualReserveCondition210 (multiplier : Nat) : Prop :=
  ∀ {M s C p first : Nat} {balance : Int},
    50000000 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
    HasMovingHorizonResidualPhaseBalances210 (primeHorizonPhase 210 (by decide))
      (M + 2) (2 * M - 2) s C [] p first balance →
    2 * (s - (M + 2)) ≤ M → IsAttainedPreviousMaximum M s →
    Nonempty (ResidualReserveCertificate210 M first multiplier balance)

theorem twin_travel_of_reserve_condition210 {multiplier : Nat}
    (hreserve : ResidualReserveCondition210 multiplier) : TwinPrimeTravelBoundFrom 50000000 := by
  intro M sf Cf q hM htwin hcanon hpath hmax
  apply canonical_travel_of_half_reserve_certificates210
    (primeHorizonPhase 210 (by decide)) hM hcanon hpath hmax
  intro s C p first balance hledger hs hmax'
  exact hreserve hM htwin hcanon hledger hs hmax'

theorem record_index_and_twin_prime_of_reserve_condition210 {multiplier : Nat}
    (hreserve : ResidualReserveCondition210 multiplier)
    {R n : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) :
    n = R + 2 ∧ IsGreaterTwinPrime R :=
  record_index_and_twin_prime_of_twin_travel_bound_from_45895573
    (twin_travel_from_fifty_million (twin_travel_of_reserve_condition210 hreserve)) hR hn hd hprior

theorem target_of_reserve_condition210 {multiplier : Nat}
    (hreserve : ResidualReserveCondition210 multiplier) : Target :=
  target_of_twin_travel_from_fifty_million (twin_travel_of_reserve_condition210 hreserve)

theorem unbounded_twin_primes_of_reserve_condition210 {multiplier : Nat}
    (hreserve : ResidualReserveCondition210 multiplier) (N : Nat) :
    ∃ R : Nat, N < R ∧ IsGreaterTwinPrime R :=
  unbounded_greater_twin_primes_of_target (target_of_reserve_condition210 hreserve) N

end A166944Research
