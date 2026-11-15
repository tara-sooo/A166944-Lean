import A166944.AngleC_Path13
namespace A166944Research

abbrev LeastNonunitDivisor (N m : Nat) : Prop :=
  2 ≤ m ∧ m ∣ N ∧ ∀ i : Fin (m - 2), ¬ (i.val + 2) ∣ N

example : LeastNonunitDivisor (96 - 1) 5 := by decide
example : LeastNonunitDivisor (24 + 1) 5 ∧ LeastNonunitDivisor (28 - 1) 3 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem no_smaller_test {N m g : Nat} (h : LeastNonunitDivisor N m)
    (hg : 2 ≤ g) (hgm : g < m) : ¬ g ∣ N := by
  obtain ⟨hm2, _, hmin⟩ := h
  have hlt : g - 2 < m - 2 := by omega
  have hid : g - 2 + 2 = g := by omega
  simpa [hid] using hmin ⟨g - 2, hlt⟩

-- the ge_three fix
theorem le_event_test {s C r C' m : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hm : LeastNonunitDivisor (if r % 2 = 0 then C - 1 else C + 1) m) :
    m ≤ d r := by
  have hdr3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases moving_horizon_step_event_package hstep with h | h
  · have hm' : LeastNonunitDivisor (C - 1) m := by simpa [if_pos h.1] using hm
    by_cases hle : m ≤ d r
    · exact hle
    · exact absurd h.2.1 (no_smaller_test hm' (by omega) (by omega))
  · have hodd : ¬ r % 2 = 0 := by omega
    have hm' : LeastNonunitDivisor (C + 1) m := by simpa [if_neg hodd] using hm
    by_cases hle : m ≤ d r
    · exact hle
    · exact absurd h.2.1 (no_smaller_test hm' (by omega) (by omega))

-- the if-dispatch fix
theorem gap_bound_test {s C r C' m : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hm : LeastNonunitDivisor (if r % 2 = 0 then C - 1 else C + 1) m) :
    r - s ≤ 2 * m := by
  by_cases hr : r % 2 = 0
  · have hm' : LeastNonunitDivisor (C - 1) m := by simpa [if_pos hr] using hm
    exact moving_horizon_gap_le_twice_even_factor hstep (by have := hm'.1; omega)
      hm'.2.1
  · have hm' : LeastNonunitDivisor (C + 1) m := by simpa [if_neg hr] using hm
    exact moving_horizon_gap_le_twice_odd_factor hstep (by have := hm'.1; omega)
      hm'.2.1
end A166944Research
