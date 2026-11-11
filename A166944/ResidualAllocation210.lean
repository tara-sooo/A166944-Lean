import A166944.ResidualStartup210
import A166944.CreditDeficits210

/-!
# Startup costs and unused negative credit in the net budget

An allocation need not spend all its sources. Keeping the unused reserve
improves the signed bound and preserves cancellation with first-phase travel.
-/

open Finset

namespace A166944Research

def phaseCreditUnused210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop}
    (certificate : FundedPhaseCreditAllocation210 cost key eligible first multiplier) : Nat :=
  (∑ j, certificate.supply j) - ∑ i, ∑ j, certificate.allocation i j

theorem phase_allocation_with_reserve_bound210 {n m first multiplier startupBound : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop}
    (certificate : FundedPhaseCreditAllocation210 cost key eligible first multiplier)
    (hstartup : (∑ i ∈ certificate.startup, (cost i).toNat) ≤ startupBound) :
    (∑ i, cost i) + (phaseCreditUnused210 certificate : Int) ≤
      ((startupBound + multiplier * first : Nat) : Int) := by
  classical
  have hrow (i : Fin n) : (cost i).toNat ≤
      (if i ∈ certificate.startup then (cost i).toNat else 0) + ∑ j, certificate.allocation i j := by
    by_cases hi : i ∈ certificate.startup
    · rw [if_pos hi]
      omega
    · simpa only [if_neg hi, Nat.zero_add] using certificate.paid i hi
  have hpositive := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [Finset.sum_add_distrib] at hpositive
  have hstartupEq : (∑ i : Fin n, if i ∈ certificate.startup then (cost i).toNat else 0) =
      ∑ i ∈ certificate.startup, (cost i).toNat := by simp
  rw [hstartupEq] at hpositive
  have hused : (∑ i, ∑ j, certificate.allocation i j) ≤ ∑ j, certificate.supply j := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => certificate.capacity j)
  have hunused : phaseCreditUnused210 certificate + (∑ i, ∑ j, certificate.allocation i j) =
      ∑ j, certificate.supply j := Nat.sub_add_cancel hused
  have hfund := certificate.funding
  have hcost : (∑ i, cost i) = ((∑ i, (cost i).toNat : Nat) : Int) -
      ((∑ i, (-cost i).toNat : Nat) : Int) := by
    calc
      (∑ i, cost i) = ∑ i, (((cost i).toNat : Int) - ((-cost i).toNat : Int)) :=
        Finset.sum_congr rfl (fun i _ => by omega)
      _ = _ := by rw [Finset.sum_sub_distrib, Nat.cast_sum, Nat.cast_sum]
  omega

theorem residual_allocation_with_reserve_bound210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop}
    (certificate : FundedPhaseCreditAllocation210 cost key eligible first multiplier)
    (allowedStartup : ∀ i ∈ certificate.startup, (key i).val ∈ residualStartupCodes210)
    (cap : ∀ i ∈ certificate.startup, (cost i).toNat ≤ 1478) :
    (∑ i, cost i) + (phaseCreditUnused210 certificate : Int) ≤
      ((residualPhaseStartupBound210 + multiplier * first : Nat) : Int) := by
  have hunique : Set.InjOn (fun i => (key i).val) (certificate.startup : Set (Fin n)) := by
    intro i hi k hk heq
    exact certificate.startup_unique hi hk (Fin.ext heq)
  exact phase_allocation_with_reserve_bound210 certificate
    (residual_startup_sum_bound210 certificate.startup (fun i => (key i).val) hunique allowedStartup cap)

/-- A finite net inequality suffices at a prefix, including all unused
credit. No asymptotic threshold is needed for this implication. -/
theorem residual_net_budget_of_allocation210 {n m first multiplier M : Nat} {balance : Int}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop}
    (certificate : FundedPhaseCreditAllocation210 cost key eligible first multiplier)
    (hsum : (∑ i, cost i) = balance)
    (allowedStartup : ∀ i ∈ certificate.startup, (key i).val ∈ residualStartupCodes210)
    (cap : ∀ i ∈ certificate.startup, (cost i).toNat ≤ 1478)
    (hnet : (24 + multiplier) * first + residualPhaseStartupBound210 +
      24 * Nat.sqrt (4 * (3 * M + 4)) + 1315 ≤ M + phaseCreditUnused210 certificate) :
    ((24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 1315 : Nat) : Int) + balance ≤ M := by
  have hbound := residual_allocation_with_reserve_bound210 certificate allowedStartup cap
  rw [hsum] at hbound
  rw [Nat.add_mul] at hnet
  omega

end A166944Research
