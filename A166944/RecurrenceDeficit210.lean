import A166944.CreditDeficitStructure210
import A166944.TravelPhases210

/-!
# Actual recurrence constraints on deficient-window requests

A request can be annotated by its earlier and later uses of the same
increment and phase. Recurrence-index timestamps preserve the order of
ordinal timestamps. The minimal-window lemmas then force such a real
reuse across each interior cut, with both index and horizon constraints.
-/

namespace A166944Research

structure SamePhaseCreditInterval210 where
  s : Nat
  C : Nat
  r : Nat
  C' : Nat
  t : Nat
  H : Nat
  u : Nat
  H' : Nat
  earlier : IsMovingHorizonStep s C r C'
  later : IsMovingHorizonStep t H u H'
  ordered : r ≤ t
  same_increment : d r = d u
  same_phase : primeHorizonPhase 210 (by decide) C r = primeHorizonPhase 210 (by decide) H u

def SamePhaseCreditInterval210.leftTime (w : SamePhaseCreditInterval210) : Nat := 2 * w.r + 1

def SamePhaseCreditInterval210.rightTime (w : SamePhaseCreditInterval210) : Nat := 2 * w.u + 1

theorem same_phase_credit_interval_valid210 (w : SamePhaseCreditInterval210) :
    w.leftTime ≤ w.rightTime := by
  have h := w.ordered.trans (Nat.le_of_lt w.later.2.1)
  unfold SamePhaseCreditInterval210.leftTime SamePhaseCreditInterval210.rightTime
  omega

def SamePhaseCreditInterval210.Constraints (w : SamePhaseCreditInterval210) : Prop :=
  (2 * d w.r) ∣ w.u - w.r ∧
    Nat.lcm 210 (2 * d w.r) ∣ w.H - w.C ∧
    Nat.lcm 210 (2 * d w.r) ≤ w.H - w.C ∧
    ∃ j : Nat, w.r < j ∧ j < w.u ∧ ¬ d j ∣ Nat.lcm 210 (2 * d w.r)

theorem same_phase_credit_interval_constraints210 (w : SamePhaseCreditInterval210) : w.Constraints := by
  have hr : 3 ≤ w.r := by have := w.earlier.1.1; have := w.earlier.2.1; omega
  have hodd := d_mod_two_eq_one_of_three_le hr
  have he := w.earlier.2.2.2.1
  have hp : 2 < d w.r := by omega
  have hcode := congrArg Fin.val w.same_phase
  change 2 * (w.C % 210) + w.r % 2 = 2 * (w.H % 210) + w.u % 2 at hcode
  have hpar : w.r % 2 = w.u % 2 := by omega
  have hphase : w.C % 210 = w.H % 210 := by omega
  have hdiv : d w.r ∣ d w.u := by rw [← w.same_increment]
  have hindex : (2 * d w.r) ∣ w.u - w.r := by
    rcases moving_horizon_factor_reuse_drift_residues w.earlier w.later w.ordered hp
      (Nat.dvd_refl _) hdiv with h | h | h
    · exact h.2.1
    · omega
    · omega
  exact ⟨hindex, moving_horizon_same_phase_reuse_requires_separator w.earlier w.later w.ordered
    (by decide : 0 < 210) hp rfl hdiv hpar hphase⟩

theorem minimal_recurrence_deficit_cut210 {n m a b : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat} {time : Fin m → Nat}
    (requests : Fin n → SamePhaseCreditInterval210)
    (deficit : CreditWindowDeficit210 demand supply time
      (fun i => (requests i).leftTime) (fun i => (requests i).rightTime) a b)
    (minimal : ∀ a' b' : Nat, a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) →
      ¬ CreditWindowDeficit210 demand supply time
        (fun i => (requests i).leftTime) (fun i => (requests i).rightTime) a' b')
    (t : Nat) (hat : a ≤ t) (htb : t < b) :
    ∃ i : Fin n, a ≤ (requests i).leftTime ∧ (requests i).rightTime ≤ b ∧
      0 < demand i ∧ (requests i).leftTime ≤ t ∧ t < (requests i).rightTime ∧
      (requests i).Constraints := by
  obtain ⟨i, hi, hpos, hl, hr⟩ := minimal_credit_deficit_crosses_every_cut210
    (fun i => same_phase_credit_interval_valid210 (requests i)) deficit minimal t hat htb
  have hbounds := (Finset.mem_filter.mp hi).2
  exact ⟨i, hbounds.1, hbounds.2, hpos, hl, hr, same_phase_credit_interval_constraints210 _⟩

theorem minimal_recurrence_deficit_endpoints210 {n m a b : Nat}
    {demand : Fin n → Nat} {supply : Fin m → Nat} {time : Fin m → Nat}
    (requests : Fin n → SamePhaseCreditInterval210) (hab : a ≤ b)
    (deficit : CreditWindowDeficit210 demand supply time
      (fun i => (requests i).leftTime) (fun i => (requests i).rightTime) a b)
    (minimal : ∀ a' b' : Nat, a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) →
      ¬ CreditWindowDeficit210 demand supply time
        (fun i => (requests i).leftTime) (fun i => (requests i).rightTime) a' b') :
    (∃ i : Fin n, 0 < demand i ∧ a = 2 * (requests i).r + 1 ∧ (requests i).rightTime ≤ b) ∧
    (∃ k : Fin n, 0 < demand k ∧ b = 2 * (requests k).u + 1 ∧ a ≤ (requests k).leftTime) := by
  obtain ⟨⟨i, hi, hpos, hleft⟩, ⟨k, hk, hkpos, hright⟩⟩ :=
    minimal_credit_deficit_has_boundary_requests210
      (fun i => same_phase_credit_interval_valid210 (requests i)) hab deficit minimal
  exact ⟨⟨i, hpos, hleft.symm, (Finset.mem_filter.mp hi).2.2⟩,
    ⟨k, hkpos, hright.symm, (Finset.mem_filter.mp hk).2.1⟩⟩

end A166944Research
