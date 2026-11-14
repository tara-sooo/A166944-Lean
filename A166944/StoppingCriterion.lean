import A166944.Lemmas

namespace A166944Research

/-!
# Exact stopping criterion for moving-horizon first events

The unit tail on `(s, C]` is equivalent to the coprimality sieve of `C - 1`
and `C + 1` clearing every index of the interval. This makes "no event before
the horizon" checkable by a purely arithmetic condition, and it is the
left-to-right/right-to-left characterisation that lane F asked for.
-/

/-- The unit tail of the interval `(s, C]`. -/
def HasUnitTail (s C : Nat) : Prop :=
  ∀ j : Nat, s < j → j ≤ C → d j = 1

/-- **Left-to-right half of the exact stopping criterion.** A unit tail forces the
coprimality sieve on the whole interval `(s, C]`. -/
theorem coprime_criterion_of_unit_tail {s C : Nat}
    (hs : IsMovingHorizonState s C) (hunit : HasUnitTail s C) :
    (∀ j : Nat, s < j → j ≤ C → j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (∀ j : Nat, s < j → j ≤ C → j % 2 = 1 →
        Nat.gcd (j - 2) (C + 1) = 1) := by
  obtain ⟨hs2, hDs, hsC⟩ := hs
  have hsieve : ∀ j : Nat, s < j → j ≤ C →
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    intro j hsj hjC
    have hj2 : 2 ≤ j := Nat.le_trans hs2 (Nat.le_of_lt hsj)
    have hfirst : ∀ l : Nat, s < l → l < j → d l = 1 := by
      intro l hsl hlj
      exact hunit l hsl (Nat.le_trans (Nat.le_of_lt hlj) hjC)
    have hDj : D (j - 1) = C := first_later_event_D_eq hs2 hDs hsj hfirst
    have hmap := constant_D_event_map hj2 hDj
    have hdj : d j = 1 := hunit j hsj hjC
    constructor
    · intro hje
      rw [if_pos hje] at hmap
      rw [hmap] at hdj
      exact hdj
    · intro hjo
      rw [if_neg (by simp [hjo])] at hmap
      rw [hmap] at hdj
      exact hdj
  exact ⟨fun j hsj hjC hje => (hsieve j hsj hjC).1 hje,
    fun j hsj hjC hjo => (hsieve j hsj hjC).2 hjo⟩

/-- **Right-to-left half of the exact stopping criterion.** If no even `j` in
`(s, C]` shares a factor with `C - 1`, and no odd `j` there has `j - 2` sharing a
factor with `C + 1`, then the whole interval is a unit tail. -/
theorem unit_tail_of_coprime_criterion {s C : Nat}
    (hs : IsMovingHorizonState s C)
    (hcop : (∀ j : Nat, s < j → j ≤ C → j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (∀ j : Nat, s < j → j ≤ C → j % 2 = 1 →
        Nat.gcd (j - 2) (C + 1) = 1)) :
    HasUnitTail s C := by
  obtain ⟨hs2, hDs, hsC⟩ := hs
  intro j hsj hjC
  by_cases hdj : d j = 1
  · exact hdj
  · have hj2 : 2 ≤ j := Nat.le_trans hs2 (Nat.le_of_lt hsj)
    have hd1 : 1 ≤ d j := one_le_d_of_two_le hj2
    have hdgt : 1 < d j := Nat.lt_of_le_of_ne hd1 (fun hh => hdj hh.symm)
    have hex : ∃ k : Nat, s < k ∧ k ≤ C ∧ 1 < d k := ⟨j, hsj, hjC, hdgt⟩
    obtain ⟨r, C', hstep⟩ := moving_horizon_step_of_exists ⟨hs2, hDs, hsC⟩ hex
    have hsr : s < r := hstep.2.1
    have hrC : r ≤ C := hstep.2.2.1
    have hdrgt : 1 < d r := hstep.2.2.2.1
    have hDr : D (r - 1) = C := hstep.2.2.2.2.2.1
    have hr2 : 2 ≤ r := Nat.le_trans hs2 (Nat.le_of_lt hsr)
    have hmap := constant_D_event_map hr2 hDr
    rcases Nat.mod_two_eq_zero_or_one r with hre | hro
    · rw [if_pos hre] at hmap
      have hbad := hcop.1 r hsr hrC hre
      rw [← hmap] at hbad
      rw [hbad] at hdrgt
      exact absurd hdrgt (Nat.lt_irrefl 1)
    · rw [if_neg (by simp [hro])] at hmap
      have hbad := hcop.2 r hsr hrC hro
      rw [← hmap] at hbad
      rw [hbad] at hdrgt
      exact absurd hdrgt (Nat.lt_irrefl 1)

/-- **Exact stopping criterion.** From a moving-horizon state `(s, C)`, the
interval `(s, C]` consists exclusively of unit increments if and only if the
coprimality sieve of `C - 1` and `C + 1` clears every index in the interval. -/
theorem no_event_on_interval_iff (s C : Nat) (h : IsMovingHorizonState s C) :
    HasUnitTail s C ↔
      ((∀ j : Nat, s < j → j ≤ C → j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
        (∀ j : Nat, s < j → j ≤ C → j % 2 = 1 →
          Nat.gcd (j - 2) (C + 1) = 1)) :=
  ⟨fun hunit => coprime_criterion_of_unit_tail h hunit,
    fun hcop => unit_tail_of_coprime_criterion h hcop⟩

end A166944Research
