import A166944.ResidualAllocation210

/-!
# An explicit fifty-million threshold under the reserve inequality

The reserve inequality is still an open recurrence hypothesis. Its
arithmetic consequence is explicit and does not use the earlier large
first-phase asymptotic threshold.
-/

open Finset

namespace A166944Research

set_option maxRecDepth 4096

private theorem fifty_million_sqrt_budget {M : Nat} (hM : 50000000 ≤ M) :
    1536 * Nat.sqrt (4 * (3 * M + 4)) ≤ M := by
  let Q := Nat.sqrt (4 * (3 * M + 4))
  change 1536 * Q ≤ M
  apply Nat.mul_self_le_mul_self_iff.mp
  have hQ : Q * Q ≤ 4 * (3 * M + 4) := Nat.sqrt_le _
  calc
    (1536 * Q) * (1536 * Q) = (1536 * 1536) * (Q * Q) := by ac_rfl
    _ ≤ (1536 * 1536) * (16 * M) := Nat.mul_le_mul_left _ (by omega)
    _ = 37748736 * M := by omega
    _ ≤ M * M := Nat.mul_le_mul_right _ (by omega)

theorem half_reserve_implies_fifty_million_net_budget210 {M first multiplier unused : Nat}
    (hM : 50000000 ≤ M)
    (hreserve : 2 * ((24 + multiplier) * first) ≤ M + 2 * unused) :
    (24 + multiplier) * first + residualPhaseStartupBound210 +
      24 * Nat.sqrt (4 * (3 * M + 4)) + 1315 ≤ M + unused := by
  have hQ := fifty_million_sqrt_budget hM
  have hstartup : 64 * (residualPhaseStartupBound210 + 1315) ≤ 31 * M := by
    change 64 * (23899260 + 1315) ≤ 31 * M
    omega
  have hscaled := Nat.mul_le_mul_left 32 hreserve
  omega

structure ResidualReserveCertificate210 (M first multiplier : Nat) (balance : Int) where
  n : Nat
  m : Nat
  cost : Fin n → Int
  key : Fin n → Fin (631 * 420)
  eligible : Fin n → Fin m → Prop
  sum_exact : (∑ i, cost i) = balance
  allocation : FundedPhaseCreditAllocation210 cost key eligible first multiplier
  startup_allowed : ∀ i ∈ allocation.startup, (key i).val ∈ residualStartupCodes210
  startup_cap : ∀ i ∈ allocation.startup, (cost i).toNat ≤ 1478
  reserve : 2 * ((24 + multiplier) * first) ≤ M + 2 * phaseCreditUnused210 allocation

theorem residual_net_budget_of_half_reserve210 {M first multiplier : Nat} {balance : Int}
    (hM : 50000000 ≤ M) (certificate : ResidualReserveCertificate210 M first multiplier balance) :
    ((24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 1315 : Nat) : Int) + balance ≤ M := by
  exact residual_net_budget_of_allocation210 certificate.allocation certificate.sum_exact
    certificate.startup_allowed certificate.startup_cap
    (half_reserve_implies_fifty_million_net_budget210 hM certificate.reserve)

theorem canonical_travel_of_half_reserve_certificates210 {slots M sf Cf q multiplier : Nat}
    (phase : Nat → Nat → Fin slots) (hM : 50000000 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hmax : IsAttainedPreviousMaximum M sf)
    (hcert : ∀ {s C p first : Nat} {balance : Int},
      HasMovingHorizonResidualPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M → IsAttainedPreviousMaximum M s →
      Nonempty (ResidualReserveCertificate210 M first multiplier balance)) :
    2 * (sf - (M + 2)) ≤ M := by
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, balance, hledger, hstep, hr, _, hs, _, hg, hcross⟩ :=
      canonical_first_crossing_requires_residual_phase_balances210 phase hcanon hpath (by omega)
    have hstart := moving_horizon_path_index_le (residual_phase_balances210_path hledger)
    have hs_sf : s ≤ sf := (Nat.le_of_lt hstep.2.1).trans hr
    have hmax' : IsAttainedPreviousMaximum M s :=
      ⟨fun j hj hjs => hmax.1 j hj (hjs.trans hs_sf),
        ⟨M + 2, Nat.le_add_left 2 M, hstart, hcanon⟩⟩
    obtain ⟨certificate⟩ := hcert hledger hs hmax'
    have hbudget := residual_net_budget_of_half_reserve210 hM certificate
    omega

end A166944Research
