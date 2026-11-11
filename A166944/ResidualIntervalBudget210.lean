import A166944.ResidualIntervals210
import A166944.ResidualThreshold210

/-! # Exact unused credit of a residual interval allocation -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

noncomputable section

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def startupCost : Nat := ∑ i ∈ trace.startup, (trace.event i).cost.toNat

theorem startup_cost_le : trace.startupCost ≤ residualPhaseStartupBound210 := by
  apply residual_startup_sum_bound210 trace.startup (fun i => (trace.key i).val)
  · intro i hi j hj h
    exact trace.startup_unique hi hj (Fin.ext h)
  · exact trace.startup_allowed
  · exact trace.startup_cap

theorem balance_add_supply :
    balance + ((∑ j, trace.supply j : Nat) : Int) =
      ((∑ i, trace.demand i : Nat) : Int) + (trace.startupCost : Int) := by
  classical
  have hcost : balance = ((∑ i, (trace.event i).cost.toNat : Nat) : Int) -
      ((∑ i, trace.supply i : Nat) : Int) := by
    calc
      balance = ∑ i, (trace.event i).cost := trace.sum_cost.symm
      _ = ∑ i, (((trace.event i).cost.toNat : Int) - (trace.supply i : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold supply
        omega
      _ = _ := by rw [Finset.sum_sub_distrib, Nat.cast_sum, Nat.cast_sum]
  have hpositive : (∑ i, (trace.event i).cost.toNat) = (∑ i, trace.demand i) + trace.startupCost := by
    calc
      (∑ i, (trace.event i).cost.toNat) = ∑ i, (trace.demand i +
          if i ∈ trace.startup then (trace.event i).cost.toNat else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ trace.startup <;> simp [demand, hi]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [startupCost]
  rw [hpositive, Nat.cast_add] at hcost
  omega

/-- An exact Hall allocation spends only the request amounts. The
unused credit plus the signed balance is exactly the startup cost. -/
theorem allocation_of_windows (windows : trace.Windows) :
    ∃ cert : FundedPhaseCreditAllocation210 (fun i => (trace.event i).cost)
        trace.key trace.Eligible first 0,
      cert.startup = trace.startup ∧
      balance + (phaseCreditUnused210 cert : Int) = (trace.startupCost : Int) := by
  classical
  obtain ⟨allocation, allowed, paid, capacity⟩ := credit_allocation_of_hall210
    (credit_hall_of_windows210 trace.left_le_right windows)
  let cert : FundedPhaseCreditAllocation210 (fun i => (trace.event i).cost)
      trace.key trace.Eligible first 0 := {
    startup := trace.startup
    startup_unique := trace.startup_unique
    startup_cap := fun i hi => (trace.startup_cap i hi).trans (by decide)
    supply := trace.supply
    allocation := allocation
    allowed := allowed
    paid := fun i hi => by simpa only [demand, if_neg hi] using (paid i).ge
    capacity := capacity
    funding := by simp [supply]
  }
  have hused : (∑ i, ∑ j, allocation i j) ≤ ∑ j, trace.supply j := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => capacity j)
  have hunused : phaseCreditUnused210 cert + (∑ i, trace.demand i) = ∑ j, trace.supply j := by
    have h := Nat.sub_add_cancel hused
    simpa only [phaseCreditUnused210, cert, paid] using h
  have hbalance := trace.balance_add_supply
  exact ⟨cert, rfl, by omega⟩

theorem reserve_certificate_of_windows {M : Nat} (windows : trace.Windows)
    (hbound : 2 * (((24 * first : Nat) : Int) + balance) ≤
      (M : Int) + 2 * (trace.startupCost : Int)) :
    Nonempty (ResidualReserveCertificate210 M first 0 balance) := by
  obtain ⟨cert, hstartup, hbalance⟩ := trace.allocation_of_windows windows
  refine ⟨⟨n, n, (fun i => (trace.event i).cost), trace.key, trace.Eligible, trace.sum_cost, cert,
    ?_, ?_, ?_⟩⟩
  · rw [hstartup]
    exact trace.startup_allowed
  · rw [hstartup]
    exact trace.startup_cap
  · omega

end

end A166944Research.ResidualPhaseTrace210
