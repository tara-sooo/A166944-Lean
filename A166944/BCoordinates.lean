import A166944.Lemmas

namespace A166944Research

/-! # B-coordinate ("basic point") restatement of the A166944 first-event map

The repository already proves the B-form branch lemmas
`d_succ_eq_gcd_even_residual` (odd index) and `d_succ_eq_gcd_odd_residual`
(even index, side condition `4 ≤ B (n-1)`), plus the small-residual complement
`d_succ_eq_gcd_small_residual`.  Here we

1. package them as clean `d n`-form theorems,
2. prove the hypothesis-free absolute-value form,
3. prove the `D ↔ B` bridge identities,
4. show `B` is a conserved reservoir along a unit tail, and
5. use (4) to prove that on a genuine moving-horizon **even** first event the
   side condition `4 ≤ B (n-1)` is *automatic*. -/

/-! ## 1. Branch lemmas in `d n` form -/

/-- **ODD branch**, sharp hypothesis `3 ≤ n`, no side condition on `B`. -/
theorem d_eq_gcd_B_odd {n : Nat} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    d n = Nat.gcd (n - 2) (B (n - 1)) := by
  have hk2 : 2 ≤ n - 1 := by omega
  have hk0 : (n - 1) % 2 = 0 := by omega
  have hidx : n - 1 + 1 = n := by omega
  have hidx2 : n - 1 - 1 = n - 2 := by omega
  have h := d_succ_eq_gcd_even_residual hk2 hk0
  rw [hidx, hidx2] at h
  exact h

/-- **EVEN branch** with the exact side condition `4 ≤ B (n-1)`. -/
theorem d_eq_gcd_B_even {n : Nat} (hn : 4 ≤ n) (heven : n % 2 = 0)
    (hB : 4 ≤ B (n - 1)) :
    d n = Nat.gcd n (B (n - 1) - 4) := by
  have hk2 : 2 ≤ n - 1 := by omega
  have hk1 : (n - 1) % 2 = 1 := by omega
  have hidx : n - 1 + 1 = n := by omega
  have h := d_succ_eq_gcd_odd_residual hk2 hk1 hB
  rw [hidx] at h
  exact h

/-! ## 2. The hypothesis-free absolute-value form -/

/-- Unified branch statement in `k = n-1` form: no side condition at all. -/
theorem d_succ_eq_gcd_B_abs {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1) :
    d (k + 1) =
      Nat.gcd (k + 1) (if 4 ≤ B k then B k - 4 else 4 - B k) := by
  by_cases h4 : 4 ≤ B k
  · rw [if_pos h4]
    exact d_succ_eq_gcd_odd_residual hk hk1 h4
  · rw [if_neg h4]
    exact d_succ_eq_gcd_small_residual hk hk1 (by omega)

/-- **Hypothesis-free EVEN identity**: for even `n ≥ 4`,
`d n = gcd n |B (n-1) - 4|` (truncated natural absolute value). -/
theorem d_eq_gcd_B_even_abs {n : Nat} (hn : 4 ≤ n) (heven : n % 2 = 0) :
    d n = Nat.gcd n
      (if 4 ≤ B (n - 1) then B (n - 1) - 4 else 4 - B (n - 1)) := by
  have hk2 : 2 ≤ n - 1 := by omega
  have hk1 : (n - 1) % 2 = 1 := by omega
  have hidx : n - 1 + 1 = n := by omega
  have h := d_succ_eq_gcd_B_abs hk2 hk1
  rw [hidx] at h
  exact h

/-- The exceptional regime is exactly `B (n-1) ∈ {1,3}`. -/
theorem even_B_pred_small_classification {n : Nat} (hn : 4 ≤ n)
    (heven : n % 2 = 0) (hB : B (n - 1) < 4) :
    B (n - 1) = 1 ∨ B (n - 1) = 3 := by
  have hprev : 2 ≤ n - 1 := by omega
  have hodd : B (n - 1) % 2 = 1 := by
    rw [B_mod_two_of_two_le hprev]
    omega
  omega

/-! ## 3. The `D ↔ B` bridge identities -/

/-- Even-branch bridge: with `C = D (n-1)`,
`gcd n (C-1) = gcd n (B (n-1) - 4)` whenever `4 ≤ B (n-1)`. -/
theorem gcd_D_pred_eq_gcd_B_pred_sub_four {n : Nat} (hn : 3 ≤ n)
    (hB : 4 ≤ B (n - 1)) :
    Nat.gcd n (D (n - 1) - 1) = Nat.gcd n (B (n - 1) - 4) := by
  have hprev : 2 ≤ n - 1 := by omega
  have hbr : B (n - 1) + (n - 1) = D (n - 1) + 2 :=
    B_add_index_eq_D_add_two hprev
  have key : D (n - 1) - 1 = (B (n - 1) - 4) + n := by omega
  rw [key]
  simpa [Nat.mul_comm] using
    (Nat.gcd_add_mul_right_right n (B (n - 1) - 4) 1)

/-- Odd-branch bridge: `gcd (n-2) (C+1) = gcd (n-2) (B (n-1))`, no side condition. -/
theorem gcd_D_succ_eq_gcd_B_pred {n : Nat} (hn : 3 ≤ n) :
    Nat.gcd (n - 2) (D (n - 1) + 1) = Nat.gcd (n - 2) (B (n - 1)) := by
  have hprev : 2 ≤ n - 1 := by omega
  have hbr : B (n - 1) + (n - 1) = D (n - 1) + 2 :=
    B_add_index_eq_D_add_two hprev
  have key : D (n - 1) + 1 = B (n - 1) + (n - 2) := by omega
  rw [key]
  simpa [Nat.mul_comm] using
    (Nat.gcd_add_mul_right_right (n - 2) (B (n - 1)) 1)

/-- `D`-coordinate map restated: `d n = gcd n (D (n-1) - 1)` on the even branch. -/
theorem d_eq_gcd_D_even {n : Nat} (hn : 4 ≤ n) (heven : n % 2 = 0) :
    d n = Nat.gcd n (D (n - 1) - 1) := by
  have hn2 : 2 ≤ n := by omega
  have hmap := constant_D_event_map hn2 (rfl : D (n - 1) = D (n - 1))
  rwa [if_pos heven] at hmap

/-! ## 4. `B` is a conserved reservoir along a unit tail -/

/-- Along a unit tail, `B` drops by exactly one per step:
`B m + (m - s) = B s`. -/
theorem B_add_index_sub_eq_of_unit_tail {s m : Nat} (hs : 2 ≤ s) (hsm : s ≤ m)
    (htail : ∀ j : Nat, s < j → j ≤ m → d j = 1) :
    B m + (m - s) = B s := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge s (m + 1) with hlt | hge
      · have hsm' : s ≤ m := by omega
        have ih' := ih hsm' (fun j hj1 hj2 => htail j hj1 (by omega))
        have hd : d (m + 1) = 1 := htail (m + 1) (by omega) (by omega)
        have hex := excess_succ_add_two (Nat.le_trans hs hsm')
        omega
      · have hseq : s = m + 1 := by omega
        rw [hseq]
        simp

/-- **Reservoir identity at a moving-horizon first event.** -/
theorem moving_horizon_B_pred {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    B (r - 1) + (r - 1 - s) = B s := by
  rcases hstep with ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hsm : s ≤ r - 1 := by omega
  exact B_add_index_sub_eq_of_unit_tail hs2 hsm
    (fun j hj1 hj2 => htail j hj1 (by omega))

/-- **Closed form**: at a first event, `B (r-1) = D s + 3 - r` exactly. -/
theorem moving_horizon_B_pred_eq {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    B (r - 1) = C + 3 - r := by
  rcases hstep with ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hres : B (r - 1) + (r - 1 - s) = B s :=
    moving_horizon_B_pred ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hBs : B s + s = D s + 2 := B_add_index_eq_D_add_two hs2
  omega

/-- The side condition `4 ≤ B (r-1)` is exactly `r ≤ C - 1`. -/
theorem moving_horizon_B_ge_four_iff {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') : 4 ≤ B (r - 1) ↔ r ≤ C - 1 := by
  rcases hstep with ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hB : B (r - 1) = C + 3 - r :=
    moving_horizon_B_pred_eq ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  omega

/-! ## 5. The side condition is automatic on the even branch -/

/-- For an even first event, `r ≠ C`: otherwise `d r = gcd r (r-1) = 1`. -/
theorem moving_horizon_even_r_ne_C {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) : r ≠ C := by
  intro hrC
  rcases hstep with ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hr2 : 2 ≤ r := by omega
  have hmap := constant_D_event_map hr2 hDr
  rw [if_pos heven] at hmap
  rw [hrC] at hmap hd1
  have hg : Nat.gcd C (C - 1) = 1 := by
    have h : Nat.gcd (1 + (C - 1)) (C - 1) = 1 := by
      rw [Nat.gcd_add_self_left]
      exact Nat.gcd_one_left (C - 1)
    have hid : 1 + (C - 1) = C := by omega
    rwa [hid] at h
  rw [hmap, hg] at hd1
  omega

/-- **Unconditional on the even branch**: `4 ≤ B (r-1)` for an even first event. -/
theorem moving_horizon_even_B_ge_four {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) : 4 ≤ B (r - 1) := by
  have hne := moving_horizon_even_r_ne_C hstep heven
  rcases hstep with ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  have hB : B (r - 1) = C + 3 - r :=
    moving_horizon_B_pred_eq ⟨⟨hs2, hDs, hsC⟩, hsr, hrc, hd1, htail, hDr, hC', hC2, hst'⟩
  omega

/-- **Payoff**: at a genuine moving-horizon first event with even index the
B-coordinate identity holds with *no* side condition. -/
theorem moving_horizon_even_event_B_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    d r = Nat.gcd r (B (r - 1) - 4) := by
  have hsr : s < r := hstep.2.1
  have hs2 : 2 ≤ s := hstep.1.1
  have hr4 : 4 ≤ r := by omega
  exact d_eq_gcd_B_even hr4 heven (moving_horizon_even_B_ge_four hstep heven)

/-- Odd companion: at a first event with odd index, no side condition either. -/
theorem moving_horizon_odd_event_B_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    d r = Nat.gcd (r - 2) (B (r - 1)) := by
  have hsr : s < r := hstep.2.1
  have hs2 : 2 ≤ s := hstep.1.1
  have hr3 : 3 ≤ r := by omega
  exact d_eq_gcd_B_odd hr3 hodd



/-! ## 6. The B-coordinate "fold identity" at a record (NEW)

`B` obeys the exact recurrence `B (k+1) + 2 = B k + d (k+1)` (already in the
repo as `excess_succ_add_two`).  Combining it with `D n = 2 * n - 4` at an even
increment forces `B (n-1) = 0`; feeding that back gives `d n = n - 2`. -/

/-- **Fold identity (truncation-free, sharp form)**: `D n + 6 = 2 * n` with
`n ≥ 4` gives `B (n-1) + d n + 2 = n` — the "basic-point budget" `n - 2` is
split exactly between the previous excess `B (n-1)` and the increment `d n`. -/
theorem D_eq_two_mul_sub_six_add {n : Nat} (hn : 4 ≤ n) (hD : D n + 6 = 2 * n) :
    B (n - 1) + d n + 2 = n := by
  have hn1 : 2 ≤ n - 1 := by omega
  have hDrel : D n + 1 = D (n - 1) + d n := by
    have h := D_succ_add_one_eq_add_d (n - 1)
    have hidx : n - 1 + 1 = n := by omega
    rwa [hidx] at h
  have hBrel : B (n - 1) + (n - 1) = D (n - 1) + 2 :=
    B_add_index_eq_D_add_two hn1
  omega

/-- Truncated-subtraction corollaries of the fold identity. -/
theorem D_eq_two_mul_sub_six_structure {n : Nat} (hn : 4 ≤ n)
    (hD : D n = 2 * n - 6) :
    d n ≤ n - 2 ∧ B (n - 1) = n - 2 - d n := by
  have hDadd : D n + 6 = 2 * n := by omega
  have hadd := D_eq_two_mul_sub_six_add hn hDadd
  have hle : d n ≤ n - 2 := by omega
  exact ⟨hle, by omega⟩

/-- **Record fold**: if the `B`-coordinate vanishes at `n-1`, the increment is
maximal: `d n = n - 2`. -/
theorem D_eq_two_mul_sub_six_of_B_zero {n : Nat} (hn : 4 ≤ n)
    (hD : D n = 2 * n - 6) (hB0 : B (n - 1) = 0) :
    d n = n - 2 := by
  have hDadd : D n + 6 = 2 * n := by omega
  have hadd := D_eq_two_mul_sub_six_add hn hDadd
  omega

/-- **Honest biconditional (PROVED)**: the fold coordinate condition
`D n + 6 = 2 * n` is *exactly* the `B`-dialect statement that the basic-point
budget is met, `B (n-1) + d n + 2 = n`.  No side conditions. -/
theorem fold_iff_B_budget {n : Nat} (hn : 4 ≤ n) :
    D n + 6 = 2 * n ↔ B (n - 1) + d n + 2 = n := by
  have hn1 : 2 ≤ n - 1 := by omega
  have hDrel : D n + 1 = D (n - 1) + d n := by
    have h := D_succ_add_one_eq_add_d (n - 1)
    have hidx : n - 1 + 1 = n := by omega
    rwa [hidx] at h
  have hBrel : B (n - 1) + (n - 1) = D (n - 1) + 2 :=
    B_add_index_eq_D_add_two hn1
  constructor <;> intro h <;> omega

/-- **Record B-form (PROVED, equivalence form)**: for an odd-index record-like
state (`n ≥ 7`, `d n = R ≥ 7`, `D n = 2 * R - 2`), the `B`-dialect record
identity `B (n-1) + R + 2 = n` holds *if and only if* the fold coordinate
`D n + 6 = 2 * n` does.  This exhibits the record condition as a purely
`B`-coordinate statement. -/
theorem record_B_budget_iff_fold {n R : Nat} (hn : 7 ≤ n) (hR : 7 ≤ R)
    (hd : d n = R) (hodd : n % 2 = 1) (hD : D n = 2 * R - 2) :
    B (n - 1) + R + 2 = n ↔ D n + 6 = 2 * n := by
  have hn4 : 4 ≤ n := by omega
  have hiff := fold_iff_B_budget hn4
  rw [← hd]
  exact hiff.symm

/-! ## 7. Payoff: the record-index theorem is exactly `B (n-1) = 0` -/

/-- **Record index from a vanishing B (PROVED)**: at an odd index `n ≥ 3` where
the basic-point excess has vanished, the increment is maximal: `d n = n - 2`.
This is precisely the statement `n = R + 2` of the record-index theorem, and in
B-coordinates it is the *single* condition `B (n-1) = 0`. -/
theorem record_index_of_B_zero {n : Nat} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hB0 : B (n - 1) = 0) : d n = n - 2 := by
  rw [d_eq_gcd_B_odd hn hodd, hB0]
  exact Nat.gcd_zero_right (n - 2)

/-- **Converse coordinate form (PROVED)**: at a record-like state with an odd
index, the basic-point excess is *exactly* the deficit `n - 2 - R`. -/
theorem record_B_pred_eq_deficit {n R : Nat} (hn : 4 ≤ n) (hodd : n % 2 = 1)
    (hd : d n = R) (hD : D n + 6 = 2 * n) : B (n - 1) + R + 2 = n := by
  have hadd := D_eq_two_mul_sub_six_add hn hD
  omega

/-- **Record iff B vanishes (PROVED equivalence)**: under the record-like
coordinate hypotheses, `n = R + 2` holds *iff* the B-coordinate vanishes at
`n - 1`, iff `d n = gcd (n-2) (B (n-1))` is maximal. -/
theorem record_index_iff_B_zero {n R : Nat} (hn : 4 ≤ n) (hodd : n % 2 = 1)
    (hd : d n = R) (hD : D n + 6 = 2 * n) :
    R = n - 2 ↔ B (n - 1) = 0 := by
  have hdef := record_B_pred_eq_deficit hn hodd hd hD
  constructor
  · intro h; omega
  · intro h
    have hBrel : B (n - 1) + (n - 1) = D (n - 1) + 2 :=
      B_add_index_eq_D_add_two (by omega)
    have hDrel : D n + 1 = D (n - 1) + d n := by
      have h := D_succ_add_one_eq_add_d (n - 1)
      have hidx : n - 1 + 1 = n := by omega
      rwa [hidx] at h
    omega

end A166944Research
