import A166944.ResidualDeficitBounds210

/-! # Contributions to the signed crossing budget -/

open Finset

namespace A166944Research

namespace ResidualPhaseEvent210

def netCost (event : ResidualPhaseEvent210) : Int := (24 * event.firstGap : Nat) + event.cost

private theorem first_gap_le (event : ResidualPhaseEvent210) : event.firstGap ≤ event.hit - event.start := by
  unfold firstGap firstLongPrimePhaseGap
  split <;> omega

theorem net_cost_of_unsupported (event : ResidualPhaseEvent210) (unsupported : ¬ d event.hit ∣ 210) :
    event.netCost = (24 * (event.hit - event.start) : Nat) +
      (supportedPotential210 event.hit event.nextHorizon : Int) -
      (supportedPotential210 event.start event.horizon : Int) - 11 * ((d event.hit - 1 : Nat) : Int) := by
  have hgap := event.first_gap_le
  simp only [netCost, cost, residualPhaseSeparatorBalance210, if_neg unsupported]
  change _ + (((24 * (event.hit - event.start - event.firstGap) : Nat) : Int) + _ - _ - _) = _
  omega

theorem net_cost_positive_part_le (event : ResidualPhaseEvent210) :
    event.netCost.toNat ≤ 37 * d event.hit + 1326 := by
  by_cases supported : d event.hit ∣ 210
  · have hgap := (event.first_gap_le).trans (moving_horizon_supported_gap_le_fourteen event.step supported)
    simp only [netCost, cost, residualPhaseSeparatorBalance210, if_pos supported]
    omega
  · rw [event.net_cost_of_unsupported supported]
    have hgap := moving_horizon_step_gap_le_twice_increment event.step
    have hstate := event.step.2.2.2.2.2.2.2.2
    have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
    have hpotential := (supported_excess_and_potential210_bounds event.hit event.nextHorizon heven).2
    omega

theorem two_net_costs_le_prime_period (small large : ResidualPhaseEvent210)
    (hsize : d small.hit ≤ d large.hit) (hlarge : 86 ≤ d large.hit) :
    2 * (small.netCost.toNat + large.netCost.toNat) ≤ 210 * d large.hit := by
  have hsmall := small.net_cost_positive_part_le
  have hbig := large.net_cost_positive_part_le
  omega

end ResidualPhaseEvent210

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

theorem sum_net_cost : (∑ i, (trace.event i).netCost) = (24 * first : Nat) + balance := by
  simp only [ResidualPhaseEvent210.netCost]
  rw [Finset.sum_add_distrib, ← Nat.cast_sum, ← Finset.mul_sum, trace.sum_first, trace.sum_cost]

theorem horizon_strict_mono : StrictMono (fun i : Fin n => (trace.event i).horizon) := by
  intro i j hij
  have hle := D_le_of_le (trace.ordered hij)
  rw [← (trace.event i).step.2.2.2.2.2.2.1, (trace.event j).step.1.2.1] at hle
  have hstep := (trace.event i).step.2.2.2.2.2.2.2.1
  exact (show (trace.event i).horizon < (trace.event i).nextHorizon by omega).trans_le hle

/-- Charge the middle and final events to one earlier prime drift.
The two net costs include the first-gap terms at their own events. -/
theorem short_deficit_pair_net_cost {i j : Fin n} (hshort : j.val ≤ i.val + 2)
    (deficit : trace.Deficit (trace.right i) (trace.right j)) :
    ∃ prior middle : Fin n, prior < i ∧ middle.val = i.val + 1 ∧ j.val = middle.val + 1 ∧
      2 * ((trace.event middle).netCost.toNat + (trace.event j).netCost.toNat) ≤
        (trace.event middle).horizon - (trace.event prior).horizon := by
  obtain ⟨prior, middle, hprior, hmid, hj, hsize, hinc, hspan⟩ :=
    trace.short_deficit_prior_prime_drift hshort deficit
  have htwo := (trace.event j).two_net_costs_le_prime_period (trace.event middle) hinc.le (by omega)
  exact ⟨prior, middle, hprior, hmid, hj, by omega⟩

end ResidualPhaseTrace210

end A166944Research
