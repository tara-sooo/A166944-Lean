import A166944.ResidualScaledPotential210

/-! # First gaps and the remaining scaled costs -/

open Finset

namespace A166944Research

namespace ResidualPhaseEvent210

def scaledFirstGap (event : ResidualPhaseEvent210) : Nat :=
  if d event.hit ∣ 210 then 0 else event.firstGap

def adjustedCost (event : ResidualPhaseEvent210) : Int :=
  event.scaledNetCost - (24 * event.scaledFirstGap : Nat)

theorem scaled_first_gap_le (event : ResidualPhaseEvent210) : event.scaledFirstGap ≤ event.firstGap := by
  unfold scaledFirstGap
  split <;> omega

theorem adjusted_cost_positive_unsupported (event : ResidualPhaseEvent210) (h : 0 < event.adjustedCost) :
    ¬ d event.hit ∣ 210 := by
  intro hd
  simp [adjustedCost, scaledNetCost, scaledFirstGap, hd] at h

theorem adjusted_cost_of_long_reuse (event : ResidualPhaseEvent210) (seen : event.phaseKey ∈ event.seen) :
    event.adjustedCost = event.scaledNetCost := by
  have hnew : ¬ IsFirstLongPrimePhase residualHorizonPhase210 event.seen event.start event.horizon event.hit :=
    fun h => h.2.2 seen
  by_cases hd : d event.hit ∣ 210 <;>
    simp [adjustedCost, scaledFirstGap, firstGap, firstLongPrimePhaseGap, hd, hnew]

theorem adjusted_cost_le_of_unsupported (event : ResidualPhaseEvent210) (hu : ¬ d event.hit ∣ 210) :
    event.adjustedCost ≤ (24 * (event.hit - event.start) + 1120 : Nat) -
      11 * ((d event.hit - 1 : Nat) : Int) - (24 * event.firstGap : Nat) := by
  have h := event.scaled_net_cost_le_of_unsupported hu
  simp only [adjustedCost, scaledFirstGap, if_neg hu]
  omega

/-- At a sufficiently large increment the cofactor bound already pays
the whole gap, so this event has no positive scaled cost. -/
theorem scaled_net_cost_nonpos_of_cofactor_bound (event : ResidualPhaseEvent210)
    (hsize : 48 * (event.horizon + 1) + 1120 * d event.hit ≤ 11 * (d event.hit - 1) * d event.hit) :
    event.scaledNetCost ≤ 0 := by
  by_cases hd : d event.hit ∣ 210
  · simp [scaledNetCost, hd]
  · have h := moving_horizon_step_gap_mul_increment_le_twice_horizon event.step
    have he := event.step.2.2.2.1
    have hmul : (24 * (event.hit - event.start) + 1120) * d event.hit ≤
        (11 * (d event.hit - 1)) * d event.hit := by
      rw [Nat.add_mul, Nat.mul_assoc]
      omega
    have hgap := Nat.le_of_mul_le_mul_right hmul (by omega : 0 < d event.hit)
    have hcost := event.scaled_net_cost_le_of_unsupported hd
    omega

end ResidualPhaseEvent210

namespace ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def scaledFirstTravel : Nat := ∑ i, (trace.event i).scaledFirstGap

theorem scaled_first_travel_le : trace.scaledFirstTravel ≤ first := by
  calc
    trace.scaledFirstTravel ≤ ∑ i, (trace.event i).firstGap :=
      Finset.sum_le_sum fun i _ => (trace.event i).scaled_first_gap_le
    _ = first := trace.sum_first

theorem sum_scaled_net_cost_split :
    (∑ i, (trace.event i).scaledNetCost) = (24 * trace.scaledFirstTravel : Nat) +
      ∑ i, (trace.event i).adjustedCost := by
  rw [scaledFirstTravel, Finset.mul_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold ResidualPhaseEvent210.adjustedCost
  omega

abbrev ReusedLong (i : Fin n) : Prop :=
  (trace.event i).LongPrime ∧ (trace.event i).phaseKey ∈ (trace.event i).seen

private def priorAdjustedPositive (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => j < i ∧ 0 < (trace.event j).adjustedCost ∧
    (trace.event j).phaseKey = (trace.event i).phaseKey

/-- A long prime reuse keeps the latest long anchor. Other repeated
positive costs use their latest positive predecessor of the same key. -/
def adjustedAnchor (i : Fin n) : Fin n :=
  if trace.ReusedLong i then trace.anchor i
  else if h : (trace.priorAdjustedPositive i).Nonempty then (trace.priorAdjustedPositive i).max' h else i

def adjustedStartup : Finset (Fin n) :=
  univ.filter fun i => 0 < (trace.event i).adjustedCost ∧ ¬ trace.ReusedLong i ∧
    ¬ (trace.priorAdjustedPositive i).Nonempty

def adjustedDemand (i : Fin n) : Nat :=
  if i ∈ trace.adjustedStartup then 0 else (trace.event i).adjustedCost.toNat

def adjustedStartupCost : Nat := ∑ i ∈ trace.adjustedStartup, (trace.event i).adjustedCost.toNat

theorem adjusted_demand_eq_cost {i : Fin n} (hi : 0 < trace.adjustedDemand i) :
    trace.adjustedDemand i = (trace.event i).adjustedCost.toNat := by
  by_cases h : i ∈ trace.adjustedStartup
  · simp [adjustedDemand, h] at hi
  · simp [adjustedDemand, h]

theorem adjusted_startup_positive {i : Fin n} (hi : i ∈ trace.adjustedStartup) :
    0 < (trace.event i).adjustedCost := (Finset.mem_filter.mp hi).2.1

theorem adjusted_startup_not_reused {i : Fin n} (hi : i ∈ trace.adjustedStartup) :
    ¬ trace.ReusedLong i := (Finset.mem_filter.mp hi).2.2.1

theorem adjusted_startup_unique {i j : Fin n} (hi : i ∈ trace.adjustedStartup)
    (hj : j ∈ trace.adjustedStartup) (hkey : (trace.event i).phaseKey = (trace.event j).phaseKey) : i = j := by
  rcases lt_trichotomy i j with hij | heq | hji
  · exact ((Finset.mem_filter.mp hj).2.2.2
      ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hij, trace.adjusted_startup_positive hi, hkey⟩⟩).elim
  · exact heq
  · exact ((Finset.mem_filter.mp hi).2.2.2
      ⟨j, Finset.mem_filter.mpr ⟨mem_univ _, hji, trace.adjusted_startup_positive hj, hkey.symm⟩⟩).elim

theorem adjusted_demand_anchor {i : Fin n} (hi : 0 < trace.adjustedDemand i) :
    trace.adjustedAnchor i < i ∧
      (trace.event (trace.adjustedAnchor i)).phaseKey = (trace.event i).phaseKey := by
  have hs : i ∉ trace.adjustedStartup := by intro h; simp [adjustedDemand, h] at hi
  have hpos : 0 < (trace.event i).adjustedCost := by
    simp only [adjustedDemand, if_neg hs] at hi
    omega
  by_cases hl : trace.ReusedLong i
  · simpa only [adjustedAnchor, if_pos hl] using trace.anchor_of_seen_long hl.1 hl.2
  · have hprior : (trace.priorAdjustedPositive i).Nonempty := by
      by_contra h
      exact hs (Finset.mem_filter.mpr ⟨mem_univ _, hpos, hl, h⟩)
    rw [adjustedAnchor, if_neg hl, dif_pos hprior]
    have hm := (Finset.mem_filter.mp (Finset.max'_mem _ hprior)).2
    exact ⟨hm.1, hm.2.2⟩

theorem sum_adjusted_positive :
    (∑ i, (trace.event i).adjustedCost.toNat) = trace.adjustedStartupCost + ∑ i, trace.adjustedDemand i := by
  calc
    (∑ i, (trace.event i).adjustedCost.toNat) =
        ∑ i, ((if i ∈ trace.adjustedStartup then (trace.event i).adjustedCost.toNat else 0) +
          trace.adjustedDemand i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ trace.adjustedStartup <;> simp [adjustedDemand, hi]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [adjustedStartupCost]

end

end ResidualPhaseTrace210

end A166944Research
