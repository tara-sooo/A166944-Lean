import A166944.CanonicalTravel

/-!
# Travel accounting by the horizon modulo six

At an even horizon outside the residue zero modulo six, one horizon
term is divisible by three. Only the remaining event starts need the
square-root gap bound.
-/

namespace A166944Research

theorem moving_horizon_gap_le_six_of_six_not_dvd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hC : ¬ 6 ∣ C) : r - s ≤ 6 := by
  have hCe : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hpos := hstep.1.1
  have hsc := hstep.1.2.2
  by_cases h : C % 3 = 1
  · exact moving_horizon_gap_le_twice_even_factor (v := 3) hstep (by decide)
      (Nat.dvd_of_mod_eq_zero (by omega))
  · by_cases h' : C % 3 = 2
    · exact moving_horizon_gap_le_twice_odd_factor (v := 3) hstep (by decide)
        (Nat.dvd_of_mod_eq_zero (by omega))
    · exact False.elim (hC (Nat.dvd_of_mod_eq_zero (by omega)))

/-- The indices of starting states of the transitions in a genuine path. -/
abbrev IsReplayEventStart (s sf j : Nat) : Prop :=
  s ≤ j ∧ j < sf ∧ (j = s ∨ 1 < d j)

theorem moving_horizon_path_travel_by_six_cover {s C sf Cf p U : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p)
    (hU : ∀ j : Nat, IsReplayEventStart s sf j → D j ≤ U)
    (cover : List Nat)
    (hcover : ∀ j : Nat, IsReplayEventStart s sf j → 6 ∣ D j → j ∈ cover) :
    sf - s ≤ 6 * p + cover.length * (Nat.sqrt (4 * (U + 1)) - 6) := by
  induction p generalizing s C cover with
  | zero =>
      obtain ⟨rfl, _, _⟩ := hpath
      simp
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      have hsr := hstep.2.1
      have hrf := moving_horizon_path_index_le htail
      have hdr := hstep.2.2.2.1
      have hs : IsReplayEventStart s sf s := ⟨Nat.le_refl _, by omega, Or.inl rfl⟩
      have hlift (j : Nat) (hj : IsReplayEventStart r sf j) : IsReplayEventStart s sf j := by
        refine ⟨by have := hj.1; omega, hj.2.1, Or.inr ?_⟩
        rcases hj.2.2 with rfl | hd
        · exact hdr
        · exact hd
      have hUt (j : Nat) (hj : IsReplayEventStart r sf j) : D j ≤ U :=
        hU j (hlift j hj)
      by_cases hC : 6 ∣ C
      · have hmem := hcover s hs (hstep.1.2.1.symm ▸ hC)
        let rest := cover.erase s
        have hlen : rest.length + 1 = cover.length := by
          have hlength := List.length_erase_of_mem hmem
          have hpos := List.length_pos_of_mem hmem
          change rest.length = cover.length - 1 at hlength
          omega
        have htailCover (j : Nat) (hj : IsReplayEventStart r sf j) (hdiv : 6 ∣ D j) :
            j ∈ rest :=
          (List.mem_erase_of_ne (by have := hj.1; omega : j ≠ s)).2 (hcover j (hlift j hj) hdiv)
        have htailTime := ih htail hUt rest htailCover
        have hCbound : C ≤ U := hstep.1.2.1 ▸ hU s hs
        have hgap := moving_horizon_step_gap_le_sqrt hstep hCbound
        rw [← hlen, Nat.add_mul, Nat.one_mul, Nat.mul_succ 6 p]
        omega
      · have htailTime := ih htail hUt cover (fun j hj hd => hcover j (hlift j hj) hd)
        have hgap := moving_horizon_gap_le_six_of_six_not_dvd hstep hC
        rw [Nat.mul_succ 6 p]
        omega

theorem moving_horizon_path_first_index_crossing {s C sf Cf p cutoff : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hstart : s ≤ cutoff) (hcross : cutoff < sf) :
    ∃ sp Cp r Cr q : Nat, HasMovingHorizonPathTo s C sp Cp q ∧
      IsMovingHorizonStep sp Cp r Cr ∧ sp ≤ cutoff ∧ cutoff < r ∧ q + 1 ≤ p ∧ r ≤ sf := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hs, _, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨hstate, t, Ct, ht, htail⟩ := hpath
      by_cases h : t ≤ cutoff
      · obtain ⟨sp, Cp, r, Cr, q, hpre, hstep, hsp, hr, hq, hrf⟩ := ih htail h
        exact ⟨sp, Cp, r, Cr, q + 1, ⟨hstate, t, Ct, ht, hpre⟩, hstep,
          hsp, hr, by omega, hrf⟩
      · exact ⟨s, C, t, Ct, 0, ⟨rfl, rfl, hstate⟩, ht, hstart,
          by omega, by omega, moving_horizon_path_index_le htail⟩

/-- The residue-weighted time bound directly excludes a first violation
of short travel. It needs no assumed bound on the final horizon. -/
theorem canonical_travel_bound_of_six_cover {M sf Cf p : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (cover : List Nat)
    (hcover : ∀ j : Nat, IsReplayEventStart (M + 2) sf j → 6 ∣ D j → j ∈ cover)
    (hbudget : 2 * (6 * p + cover.length * (Nat.sqrt (4 * (3 * M + 4)) - 6)) ≤ M) :
    2 * (sf - (M + 2)) ≤ M := by
  by_cases h : 2 * (sf - (M + 2)) ≤ M
  · exact h
  · let cutoff := M + 2 + M / 2
    obtain ⟨sp, Cp, r, Cr, q, hpre, hstep, hsp, hr, hq, hrf⟩ :=
      moving_horizon_path_first_index_crossing hpath (by omega : M + 2 ≤ cutoff) (by omega)
    have hto := moving_horizon_path_append_step hpre hstep
    have hCp := canonical_horizon_bound_of_short_travel hpre (by omega)
    have hCpEven : Cp % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
    have hModd : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
    have hspStart := moving_horizon_path_index_le hpre
    have hU (j : Nat) (hj : IsReplayEventStart (M + 2) r j) : D j ≤ 3 * M + 3 := by
      have hjs : j ≤ sp := by
        by_cases hle : j ≤ sp
        · exact hle
        · have hone := hstep.2.2.2.2.1 j (by omega) hj.2.1
          rcases hj.2.2 with heq | hnon <;> omega
      have hD := D_le_of_le hjs
      rw [hstep.1.2.1] at hD
      omega
    have hcover' (j : Nat) (hj : IsReplayEventStart (M + 2) r j) (hdiv : 6 ∣ D j) :
        j ∈ cover := hcover j ⟨hj.1, by have := hj.2.1; omega, hj.2.2⟩ hdiv
    have ht := moving_horizon_path_travel_by_six_cover hto hU cover hcover'
    change r - (M + 2) ≤ 6 * (q + 1) + cover.length * (Nat.sqrt (4 * (3 * M + 4)) - 6) at ht
    omega

end A166944Research
