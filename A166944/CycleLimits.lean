import A166944.Lemmas

namespace A166944Research

/-!
# Cycle limits for moving-horizon replays

What the existing two-cycle exclusions do and do not reach.

* `moving_horizon_no_two_event_drift_cycle` needs `3 <= e`; that hypothesis is
  sharp -- `(e1, e2) = (2, 4)` satisfies the divisibility and refutes it.
* Mutual divisibility `e1 | e2 - 2`, `e2 | e1 - 2` really is impossible for
  values `>= 3`.
* The naive three-value generalisation is FALSE: `(3, 15, 15)` is a witness.
* The drift lemma is silent on renewed cycles because it requires equal event
  values *and* equal parity; the abstract cycle alternates parity, and real
  renewals update the event value each time.
* Putting both defects right: adjacent same-parity events must differ, and the
  two-step slack identity holds exactly.
-/

/-! ## Part 1 — the reported theorem is TRUE (imported ⇒ kernel-checked) -/

example {e₁ e₂ : Nat} (h₁ : 3 ≤ e₁) (h₂ : 3 ≤ e₂)
    (hd₁ : e₁ ∣ e₁ + e₂ - 2) (hd₂ : e₂ ∣ e₁ + e₂ - 2) : False :=
  moving_horizon_no_two_event_drift_cycle h₁ h₂ hd₁ hd₂

/-! ## Part 2 — sharpness of `3 ≤ e`, and the truncation step -/

theorem probe_cycle_needs_three :
    ∃ e₁ e₂ : Nat, e₁ ∣ e₁ + e₂ - 2 ∧ e₂ ∣ e₁ + e₂ - 2 ∧ ¬ (3 ≤ e₁ ∧ 3 ≤ e₂) :=
  ⟨2, 4, by decide, by decide, by decide⟩

theorem probe_truncation (a b : Nat) : (a + b - 2) - a = b - 2 := by omega

/-! ## Part 3 — LIMITS: what does NOT generalise -/

/-- The naive three-value generalisation is FALSE: `(3,15,15)`. -/
theorem probe_three_value_cycle_is_false :
    ∃ e₁ e₂ e₃ : Nat, 3 ≤ e₁ ∧ 3 ≤ e₂ ∧ 3 ≤ e₃ ∧
      e₁ ∣ e₁ + e₂ + e₃ - 3 ∧ e₂ ∣ e₁ + e₂ + e₃ - 3 ∧
      e₃ ∣ e₁ + e₂ + e₃ - 3 :=
  ⟨3, 15, 15, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem probe_no_uniform_three_cycle :
    ¬ (∀ e₁ e₂ e₃ : Nat, 3 ≤ e₁ → 3 ≤ e₂ → 3 ≤ e₃ →
        e₁ ∣ e₁ + e₂ + e₃ - 3 → e₂ ∣ e₁ + e₂ + e₃ - 3 →
        e₃ ∣ e₁ + e₂ + e₃ - 3 → False) := by
  intro h
  exact h 3 15 15 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- But mutual divisibility IS impossible for values ≥ 3 (proved here). -/
theorem probe_mutual_divisibility_impossible :
    ∀ e₁ e₂ : Nat, 3 ≤ e₁ → 3 ≤ e₂ → e₁ ∣ e₂ - 2 → e₂ ∣ e₁ - 2 → False := by
  intro e₁ e₂ h₁ h₂ hd₁ hd₂
  rcases Nat.le_total e₁ e₂ with hle | hle
  · have hlt : e₁ - 2 < e₂ := by omega
    have hz : e₁ - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hd₂ hlt
    omega
  · have hlt : e₂ - 2 < e₁ := by omega
    have hz : e₂ - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hd₁ hlt
    omega

/-! ## Part 4 — why the drift lemma is silent on renewed cycles:
     it requires EQUAL event values and EQUAL parity, and even then
     `e | C' - C` forces `e | e - 1`. -/

theorem probe_drift_needs_same_parity :
    ∃ C₁ C₂ e : Nat, e = 5 ∧ C₁ = 28 ∧ C₂ = 40 ∧ ¬ e ∣ C₂ - C₁ :=
  ⟨28, 40, 5, rfl, rfl, rfl, by decide⟩

theorem probe_drift_needs_equal_values :
    ∃ e f C C' : Nat, e = 5 ∧ f = 3 ∧ C = 40 ∧ C' = 42 ∧ ¬ e ∣ C' - C :=
  ⟨5, 3, 40, 42, rfl, rfl, rfl, by decide⟩

/-! ## Part 5 — PROPOSED LEMMA (kernel-checked): adjacent same-parity events differ -/

theorem candidate_no_adjacent_equal_same_parity_event
    {s C r C' u U' e : Nat}
    (hstep₁ : IsMovingHorizonStep s C r C')
    (hstep₂ : IsMovingHorizonStep r C' u U')
    (he₁ : d r = e) (he₂ : d u = e)
    (hpar : r % 2 = u % 2) (he : 3 ≤ e) : False := by
  have hu₁ := moving_horizon_step_update hstep₁
  rw [he₁] at hu₁
  have hdrift := moving_horizon_same_parity_event_drift hstep₁ hstep₂ he₁ he₂ hpar
  have hC : C' - C = e - 1 := by omega
  rw [hC] at hdrift
  have hpos : 0 < e - 1 := by omega
  exact absurd (Nat.le_of_dvd hpos hdrift.2) (by omega)

/-! ## Part 6 — PROPOSED LEMMA (kernel-checked): exact two-step slack identity -/

theorem candidate_slack_after_two_steps
    {s C r C' u U' e f : Nat}
    (hstep₁ : IsMovingHorizonStep s C r C')
    (hstep₂ : IsMovingHorizonStep r C' u U')
    (he₁ : d r = e) (he₂ : d u = f) :
    U' - u + (u - s) = (C - s) + (e - 1) + (f - 1) := by
  have h₁ := moving_horizon_step_update hstep₁
  have h₂ := moving_horizon_step_update hstep₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  have hsC : s < C := hstep₁.1.2.2
  have hsu : s < u := Nat.lt_trans hstep₁.2.1 hstep₂.2.1
  have hUu : u < U' := hstep₂.2.2.2.2.2.2.2.2.2.2
  have hU'val : U' = C + (e - 1) + (f - 1) := by rw [h₂, h₁]
  have hsu' : u - s + s = u := Nat.sub_add_cancel (Nat.le_of_lt hsu)
  have hUu' : U' - u + u = U' := Nat.sub_add_cancel (Nat.le_of_lt hUu)
  have hsC' : C - s + s = C := Nat.sub_add_cancel (Nat.le_of_lt hsC)
  omega

/-- PROPOSED NEXT LEMMA (the missing input): under short travel the slack strictly
    increases, so no renewal cycle in `(slack, parity)` is possible. -/
theorem candidate_slack_strict_of_short_travel
    {s C r C' u U' e f : Nat}
    (hstep₁ : IsMovingHorizonStep s C r C')
    (hstep₂ : IsMovingHorizonStep r C' u U')
    (he₁ : d r = e) (he₂ : d u = f)
    (ht₁ : r - s ≤ e - 2) (ht₂ : u - r ≤ f - 2) :
    C - s < U' - u := by
  have h₁ := moving_horizon_step_update hstep₁
  have h₂ := moving_horizon_step_update hstep₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  have hsC : s < C := hstep₁.1.2.2
  have hsr : s ≤ r := Nat.le_of_lt hstep₁.2.1
  have hsu : s < u := Nat.lt_trans hstep₁.2.1 hstep₂.2.1
  have hU'val : U' = C + (e - 1) + (f - 1) := by rw [h₂, h₁]
  have key : C - s + u < U' := by omega
  exact (Nat.lt_sub_iff_add_lt).2 key

end A166944Research
