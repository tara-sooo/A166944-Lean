import Init.Data.Nat.Sqrt
import A166944.CanonicalGrowth

/-!
# Index distance before a first horizon crossing

The increment and its cofactor both constrain the first-hit gap. The
resulting square bound is independent of how much the horizon grows
at that event.
-/

namespace A166944Research

theorem moving_horizon_step_gap_square {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r - s) * (r - s) ≤ 4 * (C + 1) := by
  obtain ⟨v, hprod, hv⟩ := moving_horizon_step_cofactor_gap hstep
  have he := moving_horizon_step_gap_le_twice_increment hstep
  calc
    (r - s) * (r - s) ≤ (2 * d r) * (2 * v) := Nat.mul_le_mul he hv
    _ = 4 * (d r * v) := by
      calc
        (2 * d r) * (2 * v) = (2 * 2) * (d r * v) := by ac_rfl
        _ = 4 * (d r * v) := rfl
    _ ≤ 4 * (C + 1) := Nat.mul_le_mul_left 4 hprod

theorem moving_horizon_step_gap_le_sqrt {s C r C' U : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hCU : C ≤ U) :
    r - s ≤ Nat.sqrt (4 * (U + 1)) := by
  have hsq := moving_horizon_step_gap_square hstep
  have hup := Nat.lt_succ_sqrt (4 * (U + 1))
  by_cases h : r - s ≤ Nat.sqrt (4 * (U + 1))
  · exact h
  · have hle : (Nat.sqrt (4 * (U + 1))).succ ≤ r - s := by omega
    have hmul := Nat.mul_le_mul hle hle
    omega

theorem moving_horizon_path_travel_bound {s C sf Cf p U : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hU : Cf ≤ U) :
    sf - s ≤ p * Nat.sqrt (4 * (U + 1)) := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, _, _⟩ := hpath
      simp
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      have hC' := (moving_horizon_path_gap_le_three_growth htail).2.1
      have hsr := hstep.2.1
      have hrf := moving_horizon_path_index_le htail
      have hgrowth := hstep.2.2.2.2.2.2.2.1
      have hgap := moving_horizon_step_gap_le_sqrt hstep (by omega : C ≤ U)
      have hrest := ih htail
      rw [Nat.succ_mul]
      omega

/-- Every first old crossing must have enough events to travel from the
canonical origin to an index where the upper bound can be exceeded. -/
theorem canonical_old_crossing_travel {M s C p r C' : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') :
    M < 2 * ((p + 1) * Nat.sqrt (4 * (3 * M + 4))) := by
  have hModd : M % 2 = 1 := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega)
  have hCU := (moving_horizon_old_crossing_band hModd hstep hcap hbelow hcross).2
  have hprefix := moving_horizon_path_travel_bound hpath hCU
  have hlast := moving_horizon_step_gap_le_sqrt hstep hCU
  change s - (M + 2) ≤ p * Nat.sqrt (4 * (3 * M + 4)) at hprefix
  change r - s ≤ Nat.sqrt (4 * (3 * M + 4)) at hlast
  have hbase := moving_horizon_path_index_le hpath
  have hsr := hstep.2.1
  have hC' : C' = D r := hstep.2.2.2.2.2.2.1
  have ha := a_le_three_mul r
  have hsum : D r + r = a r := Nat.sub_add_cancel (index_le_a _)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- With `p+1` events through the crossing, a first old crossing requires
`M ≤ 48*(p+1)^2+1`. This applies to either size of final increment. -/
theorem canonical_old_crossing_event_count {M s C p r C' : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') :
    M ≤ 48 * ((p + 1) * (p + 1)) + 1 := by
  let k := p + 1
  let Q := Nat.sqrt (4 * (3 * M + 4))
  have htravel : M < 2 * (k * Q) :=
    canonical_old_crossing_travel hM hcanon hpath hstep hcap hbelow hcross
  have hsquare : M * M < (2 * (k * Q)) * (2 * (k * Q)) := by
    have hlt := Nat.mul_lt_mul_of_pos_right htravel (by omega : 0 < M)
    exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_left _ (Nat.le_of_lt htravel))
  have hQ : Q * Q ≤ 4 * (3 * M + 4) := Nat.sqrt_le _
  have hup : M * M < 48 * (k * k) * M + 64 * (k * k) := by
    calc
      M * M < (2 * (k * Q)) * (2 * (k * Q)) := hsquare
      _ = (4 * (k * k)) * (Q * Q) := by
        calc
          (2 * (k * Q)) * (2 * (k * Q)) = ((2 * 2) * (k * k)) * (Q * Q) := by ac_rfl
          _ = (4 * (k * k)) * (Q * Q) := rfl
      _ ≤ (4 * (k * k)) * (4 * (3 * M + 4)) := Nat.mul_le_mul_left _ hQ
      _ = (16 * (k * k)) * (3 * M + 4) := by
        calc
          (4 * (k * k)) * (4 * (3 * M + 4)) = ((4 * 4) * (k * k)) * (3 * M + 4) := by ac_rfl
          _ = (16 * (k * k)) * (3 * M + 4) := rfl
      _ = 48 * (k * k) * M + 64 * (k * k) := by
        rw [Nat.mul_add (16 * (k * k))]
        congr 1
        · calc
            (16 * (k * k)) * (3 * M) = (16 * 3) * (k * k) * M := by ac_rfl
            _ = 48 * (k * k) * M := rfl
        · calc
            (16 * (k * k)) * 4 = (16 * 4) * (k * k) := by ac_rfl
            _ = 64 * (k * k) := rfl
  change M ≤ 48 * (k * k) + 1
  by_cases h : M ≤ 48 * (k * k) + 1
  · exact h
  · have hlow := Nat.mul_le_mul_right M (show 48 * (k * k) + 2 ≤ M by omega)
    rw [Nat.add_mul] at hlow
    omega

private theorem moving_horizon_path_first_crossing {s C sf Cf p H : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hbelow : C ≤ H) (hcross : H < Cf) :
    ∃ sp Cp r Cr q : Nat, HasMovingHorizonPathTo s C sp Cp q ∧
      IsMovingHorizonStep sp Cp r Cr ∧ Cp ≤ H ∧ H < Cr ∧ q + 1 ≤ p ∧ r ≤ sf := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨_, hC, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨hstate, t, Ct, ht, htail⟩ := hpath
      by_cases h : Ct ≤ H
      · obtain ⟨sp, Cp, r, Cr, q, hpre, hstep, hCp, hCr, hq, hr⟩ := ih htail h
        exact ⟨sp, Cp, r, Cr, q + 1, ⟨hstate, t, Ct, ht, hpre⟩, hstep,
          hCp, hCr, by omega, hr⟩
      · exact ⟨s, C, t, Ct, 0, ⟨rfl, rfl, hstate⟩, ht, hbelow,
          by omega, by omega, moving_horizon_path_index_le htail⟩

/-- A short capped replay cannot reach the horizon needed for a larger
first hit. This applies to every endpoint on that replay. -/
theorem canonical_horizon_bound_of_event_count {M sf Cf p : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) (hcount : 48 * (p * p) + 1 < M) :
    Cf ≤ 3 * M + 4 := by
  by_cases h : Cf ≤ 3 * M + 4
  · exact h
  · obtain ⟨sp, Cp, r, Cr, q, hpre, hstep, hbelow, hcross, hq, hr⟩ :=
      moving_horizon_path_first_crossing hpath (by omega : 2 * M - 2 ≤ 3 * M + 4) (by omega)
    have hr2 : 2 ≤ r := by have := hstep.1.1; have := hstep.2.1; omega
    have hcap := hmax.1 r hr2 hr
    have hMbound := canonical_old_crossing_event_count hM hcanon hpre hstep hcap hbelow hcross
    have hmul := Nat.mul_le_mul_left 48 (Nat.mul_le_mul hq hq)
    omega

private theorem moving_horizon_path_start_state {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) : IsMovingHorizonState s C := by
  cases p with
  | zero => exact hpath.2.2
  | succ p => exact hpath.1

theorem moving_horizon_path_travel_of_common_multiple {s C sf Cf p P : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hP : 0 < P) (hPeven : P % 2 = 0)
    (hdiv : ∀ j : Nat, s < j → j ≤ sf → d j ∣ P) :
    sf - s ≤ 3 * (P - 1) := by
  have hs := moving_horizon_path_start_state hpath
  have hf := moving_horizon_path_endpoint hpath
  obtain ⟨hsf, _, htravel⟩ := moving_horizon_path_gap_le_three_growth hpath
  have hD := D_growth_lt_of_common_even_multiple hs.1 hsf hP hPeven hdiv
  rw [hs.2.1, hf.2.1] at hD
  omega

/-- One run per gap between exceptional increments, with a first-hit
gap bound for each exception. -/
def divisorTravelBudget (P U k : Nat) : Nat :=
  (3 * (P - 1)) * (k + 1) + k * Nat.sqrt (4 * (U + 1))

private theorem divisorTravelBudget_succ (P U k : Nat) :
    divisorTravelBudget P U (k + 1) =
      divisorTravelBudget P U k + 3 * (P - 1) + Nat.sqrt (4 * (U + 1)) := by
  unfold divisorTravelBudget
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

theorem moving_horizon_path_travel_by_exception_list {s C sf Cf p P U : Nat}
    (hP : 0 < P) (hPeven : P % 2 = 0)
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hU : Cf ≤ U) (exceptions : List Nat)
    (hcover : ∀ j : Nat, s < j → j ≤ sf → ¬ d j ∣ P → j ∈ exceptions) :
    sf - s ≤ divisorTravelBudget P U exceptions.length := by
  have aux (k : Nat) : ∀ {sf Cf p : Nat} (exceptions : List Nat),
      exceptions.length = k → HasMovingHorizonPathTo s C sf Cf p → Cf ≤ U →
      (∀ j : Nat, s < j → j ≤ sf → ¬ d j ∣ P → j ∈ exceptions) →
      sf - s ≤ divisorTravelBudget P U k := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro sf Cf p exceptions hlen hpath hU hcover
      by_cases hex : ∃ j : Nat, s < j ∧ j ≤ sf ∧ ¬ d j ∣ P
      · obtain ⟨j, hj, hjs, hnd, hlast⟩ := exists_last_nondvd hex
        have hjunit : d j ≠ 1 := by
          intro h
          exact hnd (h.symm ▸ Nat.one_dvd P)
        obtain ⟨sp, Cp, Cj, q, u, hprefix, hstep, htail⟩ :=
          moving_horizon_path_split_at_nonunit hpath hj hjs hjunit
        have hspj := hstep.2.1
        have hCj := (moving_horizon_path_gap_le_three_growth htail).2.1
        have hCp : Cp ≤ U := by have := moving_horizon_step_update hstep; omega
        let rest := exceptions.erase j
        have hjmem := hcover j hj hjs hnd
        have hrest : rest.length + 1 = k := by
          have herase := List.length_erase_of_mem hjmem
          have hpos := List.length_pos_of_mem hjmem
          change rest.length = exceptions.length - 1 at herase
          omega
        have hcover' (i : Nat) (hi : s < i) (his : i ≤ sp) (hind : ¬ d i ∣ P) : i ∈ rest :=
          (List.mem_erase_of_ne (by omega : i ≠ j)).2 (hcover i hi (by omega) hind)
        have hpre := ih rest.length (by omega) rest rfl hprefix hCp hcover'
        have hgap := moving_horizon_step_gap_le_sqrt hstep hCp
        have hend := moving_horizon_path_travel_of_common_multiple htail hP hPeven hlast
        have hs := moving_horizon_path_index_le hprefix
        rw [← hrest, divisorTravelBudget_succ]
        omega
      · have hdiv (j : Nat) (hj : s < j) (hjs : j ≤ sf) : d j ∣ P := by
          by_cases h : d j ∣ P
          · exact h
          · exact False.elim (hex ⟨j, hj, hjs, h⟩)
        have hsmall := moving_horizon_path_travel_of_common_multiple hpath hP hPeven hdiv
        have hle := Nat.mul_le_mul_left (3 * (P - 1)) (show 1 ≤ k + 1 by omega)
        rw [Nat.mul_one] at hle
        unfold divisorTravelBudget
        omega
  exact aux exceptions.length exceptions rfl hpath hU hcover

/-- A cover of a genuine replay by contiguous segments. Each segment
can choose its own even multiple and list of exceptions. -/
inductive HasMovingHorizonTravelCover (U : Nat) : Nat → Nat → Nat → Nat → Nat → Prop
  | empty {s C : Nat} (hstate : IsMovingHorizonState s C) :
      HasMovingHorizonTravelCover U s C s C 0
  | segment {s C t Ct sf Cf p P budget : Nat} (hP : 0 < P) (hPeven : P % 2 = 0)
      (hpath : HasMovingHorizonPathTo s C t Ct p) (hU : Ct ≤ U) (exceptions : List Nat)
      (hcover : ∀ j : Nat, s < j → j ≤ t → ¬ d j ∣ P → j ∈ exceptions)
      (htail : HasMovingHorizonTravelCover U t Ct sf Cf budget) :
      HasMovingHorizonTravelCover U s C sf Cf (divisorTravelBudget P U exceptions.length + budget)

theorem moving_horizon_travel_cover_bound {U s C sf Cf budget : Nat}
    (hcover : HasMovingHorizonTravelCover U s C sf Cf budget) : sf - s ≤ budget := by
  induction hcover with
  | empty _ => simp
  | segment hP hPeven hpath hU exceptions hcover htail ih =>
      have hpre := moving_horizon_path_travel_by_exception_list hP hPeven hpath hU exceptions hcover
      omega

/-- A large crossing cannot follow a prefix whose travel cover is too
short. The final gap is at most six in the three surviving forms. -/
theorem canonical_large_old_crossing_travel_cover {M s C p r C' U budget : Nat}
    (hM : 25 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r)
    (hcover : HasMovingHorizonTravelCover U (M + 2) (2 * M - 2) s C budget) :
    M < 2 * budget + 13 := by
  obtain ⟨hr, _, _, _, hcases⟩ := canonical_path_large_old_crossing
    hM hcanon hpath hstep hcap hbelow hcross hlarge
  have hgap : r - s ≤ 6 := by
    rcases hcases with ⟨ht, _, _⟩ | ⟨ht, _, _⟩ | ⟨ht, _, _, _⟩ <;> omega
  have hsr := hstep.2.1
  have htravel := moving_horizon_travel_cover_bound hcover
  omega

end A166944Research
