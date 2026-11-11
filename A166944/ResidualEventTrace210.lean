import A166944.ResidualStartup210
import Mathlib.Algebra.BigOperators.Fin

/-! # Ordered events in the residual ledger -/

open Finset

namespace A166944Research

abbrev residualHorizonPhase210 := primeHorizonPhase 210 (by decide)

structure ResidualPhaseEvent210 where
  start : Nat
  horizon : Nat
  hit : Nat
  nextHorizon : Nat
  seen : List (Nat × Fin 420)
  step : IsMovingHorizonStep start horizon hit nextHorizon

namespace ResidualPhaseEvent210

def phaseKey (event : ResidualPhaseEvent210) : Nat × Fin 420 :=
  (d event.hit, residualHorizonPhase210 event.horizon event.hit)

abbrev LongPrime (event : ResidualPhaseEvent210) : Prop :=
  10 < event.hit - event.start ∧ NoProperFactor (d event.hit)

def firstGap (event : ResidualPhaseEvent210) : Nat :=
  firstLongPrimePhaseGap residualHorizonPhase210 event.seen event.start event.horizon event.hit

def cost (event : ResidualPhaseEvent210) : Int :=
  residualPhaseSeparatorBalance210 residualHorizonPhase210 event.seen event.start event.horizon
    event.hit event.nextHorizon

theorem positive_unsupported (event : ResidualPhaseEvent210) (h : 0 < event.cost) :
    ¬ d event.hit ∣ 210 := by
  intro hd
  simp [cost, residualPhaseSeparatorBalance210, hd] at h

end ResidualPhaseEvent210

structure ResidualPhaseTrace210 (s sf : Nat) (initialSeen : List (Nat × Fin 420))
    (n first : Nat) (balance : Int) where
  event : Fin n → ResidualPhaseEvent210
  start_ge : ∀ i, s ≤ (event i).start
  hit_le : ∀ i, (event i).hit ≤ sf
  ordered : ∀ {i j}, i < j → (event i).hit ≤ (event j).start
  initial : ∀ i, i.val = 0 → (event i).start = s
  consecutive : ∀ {i j}, j.val = i.val + 1 → (event j).start = (event i).hit
  seen_iff : ∀ i key, key ∈ (event i).seen ↔ key ∈ initialSeen ∨
    ∃ j, j < i ∧ (event j).LongPrime ∧ key = (event j).phaseKey
  sum_first : (∑ i, (event i).firstGap) = first
  sum_cost : (∑ i, (event i).cost) = balance

/-- The extracted trace also telescopes any integer-valued function of
the actual indices, including potentials that depend on `D`. -/
theorem residual_phase_trace_with_delta210 {s C sf Cf n first : Nat} {balance : Int}
    {seen : List (Nat × Fin 420)}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      s C sf Cf seen n first balance) :
    ∃ trace : ResidualPhaseTrace210 s sf seen n first balance,
      ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s := by
  induction n generalizing s C seen first balance with
  | zero =>
    obtain ⟨hpath, rfl, rfl⟩ := ledger
    refine ⟨{
      event := Fin.elim0
      start_ge := fun i => i.elim0
      hit_le := fun i => i.elim0
      ordered := fun {i} => i.elim0
      initial := fun i => i.elim0
      consecutive := fun {i} => i.elim0
      seen_iff := fun i => i.elim0
      sum_first := by simp
      sum_cost := by simp
    }, ?_⟩
    intro f
    simp [hpath.1]
  | succ n ih =>
    obtain ⟨r, C', tailFirst, tailCost, step, tail, rfl, rfl⟩ := ledger
    obtain ⟨history, hdelta⟩ := ih tail
    let head : ResidualPhaseEvent210 := ⟨s, C, r, C', seen, step⟩
    let events := Fin.cons (α := fun _ => ResidualPhaseEvent210) head history.event
    have hhead (key : Nat × Fin 420) :
        key ∈ recordLongPrimePhase residualHorizonPhase210 seen s C r ↔
          key ∈ seen ∨ (head.LongPrime ∧ key = head.phaseKey) := by
      change (key ∈ if 10 < r - s ∧ NoProperFactor (d r) then head.phaseKey :: seen else seen) ↔
        key ∈ seen ∨ ((10 < r - s ∧ NoProperFactor (d r)) ∧ key = head.phaseKey)
      by_cases hl : 10 < r - s ∧ NoProperFactor (d r)
      · rw [if_pos hl, List.mem_cons]
        exact ⟨fun h => h.elim (fun hk => Or.inr ⟨hl, hk⟩) Or.inl,
          fun h => h.elim Or.inr (fun hk => Or.inl hk.2)⟩
      · rw [if_neg hl]
        exact ⟨Or.inl, fun h => h.elim id (fun hk => (hl hk.1).elim)⟩
    refine ⟨⟨events, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [events, head]
      · simpa only [events, Fin.cons_succ] using (Nat.le_of_lt step.2.1).trans (history.start_ge j)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [events, Fin.cons_zero, head] using
          moving_horizon_path_index_le (residual_phase_balances210_path tail)
      · simpa only [events, Fin.cons_succ] using history.hit_le j
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (by simp) (fun j' _ => ?_) j
        simpa only [events, Fin.cons_zero, Fin.cons_succ, head] using history.start_ge j'
      · refine Fin.cases (by simp) (fun j' hij => ?_) j
        simpa only [events, Fin.cons_succ] using history.ordered (Fin.succ_lt_succ_iff.mp hij)
    · intro i
      refine Fin.cases (by simp [events, head]) (fun j => ?_) i
      simp
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (by simp) (fun j' hj => ?_) j
        simp only [Fin.val_succ, Fin.val_zero] at hj
        simpa only [events, Fin.cons_succ, Fin.cons_zero, head] using history.initial j' (by omega)
      · refine Fin.cases (by simp) (fun j' hj => ?_) j
        simp only [Fin.val_succ] at hj
        simpa only [events, Fin.cons_succ] using history.consecutive (by omega : j'.val = i'.val + 1)
    · intro i key
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [events, head]
      · rw [show (events j.succ).seen = (history.event j).seen by simp [events], history.seen_iff, hhead]
        constructor
        · rintro ((h | ⟨hl, hk⟩) | ⟨k, hkj, hl, hk⟩)
          · exact Or.inl h
          · exact Or.inr ⟨0, (Nat.succ_pos j.val : 0 < j.succ.val), by simpa [events] using hl,
              by simpa [events] using hk⟩
          · exact Or.inr ⟨k.succ, Fin.succ_lt_succ_iff.mpr hkj, by simpa [events] using hl,
              by simpa [events] using hk⟩
        · rintro (h | ⟨k, hkj, hl, hk⟩)
          · exact Or.inl (Or.inl h)
          · revert hkj hl hk
            refine Fin.cases (fun _ hl hk => ?_) (fun k' hkj hl hk => ?_) k
            · exact Or.inl (Or.inr ⟨by simpa [events] using hl, by simpa [events] using hk⟩)
            · exact Or.inr ⟨k', Fin.succ_lt_succ_iff.mp hkj, by simpa [events] using hl,
                by simpa [events] using hk⟩
    · simp only [Fin.sum_univ_succ, events, Fin.cons_zero, Fin.cons_succ, history.sum_first]
      rfl
    · simp only [Fin.sum_univ_succ, events, Fin.cons_zero, Fin.cons_succ, history.sum_cost]
      rfl
    · intro f
      simp only [Fin.sum_univ_succ, events, Fin.cons_zero, Fin.cons_succ, hdelta f, head]
      omega

/-- Read each residual cost and first gap from the actual ordered events.
The phase history at any event is exactly the initial history plus the
keys of earlier long prime events. -/
theorem residual_phase_trace210 {s C sf Cf n first : Nat} {balance : Int}
    {seen : List (Nat × Fin 420)}
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      s C sf Cf seen n first balance) :
    Nonempty (ResidualPhaseTrace210 s sf seen n first balance) := by
  obtain ⟨trace, _⟩ := residual_phase_trace_with_delta210 ledger
  exact ⟨trace⟩

end A166944Research
