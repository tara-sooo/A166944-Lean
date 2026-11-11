import A166944.ResidualEventTrace210
import A166944.RecurrenceDeficit210

/-! # Requests and negative sources from actual residual events -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

noncomputable section
open Classical

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

private def priorLong (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => j < i ∧ (trace.event j).LongPrime ∧
    (trace.event j).phaseKey = (trace.event i).phaseKey

private def priorPositive (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => j < i ∧ 0 < (trace.event j).cost ∧
    (trace.event j).phaseKey = (trace.event i).phaseKey

private def anchorCandidates (i : Fin n) : Finset (Fin n) :=
  if (trace.event i).LongPrime ∧ (trace.priorLong i).Nonempty then trace.priorLong i
  else trace.priorPositive i

/-- A repeated long prime uses its most recent long-phase occurrence.
The other positive requests use their most recent positive occurrence.
The event itself is the endpoint placeholder when there is no anchor. -/
def anchor (i : Fin n) : Fin n :=
  if h : (trace.anchorCandidates i).Nonempty then (trace.anchorCandidates i).max' h else i

def startup : Finset (Fin n) :=
  univ.filter fun i => 0 < (trace.event i).cost ∧ ¬ (trace.anchorCandidates i).Nonempty

def demand (i : Fin n) : Nat :=
  if i ∈ trace.startup then 0 else (trace.event i).cost.toNat

def supply (j : Fin n) : Nat := (-(trace.event j).cost).toNat

def time (j : Fin n) : Nat := 2 * (trace.event j).hit

def left (i : Fin n) : Nat := 2 * (trace.event (trace.anchor i)).hit + 1

def right (i : Fin n) : Nat := 2 * (trace.event i).hit + 1

def Eligible (i j : Fin n) : Prop := trace.left i ≤ trace.time j ∧ trace.time j ≤ trace.right i

private theorem anchor_mem {i : Fin n} (h : (trace.anchorCandidates i).Nonempty) :
    trace.anchor i ∈ trace.anchorCandidates i := by
  simp only [anchor, dif_pos h]
  exact Finset.max'_mem _ _

private theorem candidate_lt_and_key {i j : Fin n} (h : j ∈ trace.anchorCandidates i) :
    j < i ∧ (trace.event j).phaseKey = (trace.event i).phaseKey := by
  unfold anchorCandidates at h
  split at h
  · simp only [priorLong, mem_filter, mem_univ, true_and] at h
    exact ⟨h.1, h.2.2⟩
  · simp only [priorPositive, mem_filter, mem_univ, true_and] at h
    exact ⟨h.1, h.2.2⟩

theorem left_le_right (i : Fin n) : trace.left i ≤ trace.right i := by
  by_cases h : (trace.anchorCandidates i).Nonempty
  · have hji := (trace.candidate_lt_and_key (trace.anchor_mem h)).1
    have horder := trace.ordered hji
    have hstep := (trace.event i).step.2.1
    unfold left right
    omega
  · simp [left, right, anchor, h]

theorem demand_eq_cost {i : Fin n} (h : 0 < trace.demand i) :
    trace.demand i = (trace.event i).cost.toNat := by
  by_cases hi : i ∈ trace.startup
  · simp [demand, hi] at h
  · simp [demand, hi]

theorem demand_positive_cost {i : Fin n} (h : 0 < trace.demand i) : 0 < (trace.event i).cost := by
  rw [trace.demand_eq_cost h] at h
  omega

theorem demand_anchor_lt_key {i : Fin n} (h : 0 < trace.demand i) :
    trace.anchor i < i ∧ (trace.event (trace.anchor i)).phaseKey = (trace.event i).phaseKey := by
  have ha : (trace.anchorCandidates i).Nonempty := by
    by_contra hnone
    have hs : i ∈ trace.startup := Finset.mem_filter.mpr ⟨mem_univ _, trace.demand_positive_cost h, hnone⟩
    simp [demand, hs] at h
  exact trace.candidate_lt_and_key (trace.anchor_mem ha)

def samePhaseInterval {i j : Fin n} (ordered : i < j)
    (sameKey : (trace.event i).phaseKey = (trace.event j).phaseKey) : SamePhaseCreditInterval210 := by
  let prior := trace.event i
  let current := trace.event j
  exact ⟨prior.start, prior.horizon, prior.hit, prior.nextHorizon,
    current.start, current.horizon, current.hit, current.nextHorizon,
    prior.step, current.step, trace.ordered ordered, congrArg Prod.fst sameKey,
    congrArg Prod.snd sameKey⟩

def reuse (i : Fin n) (h : 0 < trace.demand i) : SamePhaseCreditInterval210 :=
  trace.samePhaseInterval (trace.demand_anchor_lt_key h).1 (trace.demand_anchor_lt_key h).2

private theorem startup_positive {i : Fin n} (hi : i ∈ trace.startup) :
    0 < (trace.event i).cost := (Finset.mem_filter.mp hi).2.1

private theorem startup_not_reused_long {i : Fin n} (hi : i ∈ trace.startup) :
    ¬ ((trace.event i).LongPrime ∧ (trace.event i).phaseKey ∈ (trace.event i).seen) := by
  rintro ⟨hl, hseen⟩
  obtain ⟨j, hj, hjlong, hjkey⟩ := ((trace.seen_iff i _).mp hseen).resolve_left (by simp)
  have hm : j ∈ trace.priorLong i := Finset.mem_filter.mpr ⟨mem_univ _, hj, hjlong, hjkey.symm⟩
  have hlong : (trace.event i).LongPrime ∧ (trace.priorLong i).Nonempty := ⟨hl, j, hm⟩
  apply (Finset.mem_filter.mp hi).2.2
  rw [anchorCandidates, if_pos hlong]
  exact hlong.2

private theorem startup_no_prior_positive {i j : Fin n} (hi : i ∈ trace.startup)
    (hlt : j < i) (hkey : (trace.event j).phaseKey = (trace.event i).phaseKey)
    (hpos : 0 < (trace.event j).cost) : False := by
  apply (Finset.mem_filter.mp hi).2.2
  unfold anchorCandidates
  split
  · rename_i hlong
    exact hlong.2
  · exact ⟨j, by simp [priorPositive, hlt, hpos, hkey]⟩

private theorem startup_bounds {i : Fin n} (hi : i ∈ trace.startup) :
    d (trace.event i).hit ≤ 169 ∧ (trace.event i).cost.toNat ≤ 1478 := by
  apply residual_phase_startup_bounds210 (trace.event i).step
  · rintro ⟨hg, hp, hs⟩
    exact trace.startup_not_reused_long hi ⟨⟨hg, hp⟩, hs⟩
  · exact trace.startup_positive hi

private def keyCode (i : Fin n) : Nat :=
  420 * (trace.event i).phaseKey.1 + (trace.event i).phaseKey.2.val

/-- The bound on startup increments makes reduction modulo this range
injective on startup codes. Non-startup keys carry no such requirement. -/
def key (i : Fin n) : Fin (631 * 420) :=
  ⟨trace.keyCode i % (631 * 420), Nat.mod_lt _ (by decide)⟩

private theorem startup_key_val {i : Fin n} (hi : i ∈ trace.startup) :
    (trace.key i).val = trace.keyCode i := by
  have he := (trace.startup_bounds hi).1
  have hp := (trace.event i).phaseKey.2.isLt
  change trace.keyCode i % (631 * 420) = trace.keyCode i
  apply Nat.mod_eq_of_lt
  unfold keyCode
  change 420 * d (trace.event i).hit + _ < _
  omega

theorem startup_allowed (i : Fin n) (hi : i ∈ trace.startup) :
    (trace.key i).val ∈ residualStartupCodes210 := by
  rw [trace.startup_key_val hi]
  unfold keyCode ResidualPhaseEvent210.phaseKey residualHorizonPhase210 primeHorizonPhase
  simpa only [Nat.add_assoc] using residual_phase_startup_key_mem210 (trace.event i).step
    (fun ⟨hg, hp, hs⟩ => trace.startup_not_reused_long hi ⟨⟨hg, hp⟩, hs⟩)
    (trace.startup_positive hi)

theorem startup_cap (i : Fin n) (hi : i ∈ trace.startup) :
    (trace.event i).cost.toNat ≤ 1478 := (trace.startup_bounds hi).2

theorem startup_unique : Set.InjOn trace.key (trace.startup : Set (Fin n)) := by
  intro i hi j hj heq
  have hc := congrArg Fin.val heq
  rw [trace.startup_key_val hi, trace.startup_key_val hj] at hc
  unfold keyCode at hc
  have hpi := (trace.event i).phaseKey.2.isLt
  have hpj := (trace.event j).phaseKey.2.isLt
  have hkey : (trace.event i).phaseKey = (trace.event j).phaseKey :=
    Prod.ext (by omega) (Fin.ext (by omega))
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (trace.startup_no_prior_positive hj hlt hkey (trace.startup_positive hi)).elim
  · exact heq
  · exact (trace.startup_no_prior_positive hi hgt hkey.symm (trace.startup_positive hj)).elim

def Windows : Prop := CreditWindowCondition210 trace.demand trace.supply trace.time trace.left trace.right

def Deficit (a b : Nat) : Prop :=
  CreditWindowDeficit210 trace.demand trace.supply trace.time trace.left trace.right a b

end

end A166944Research.ResidualPhaseTrace210
