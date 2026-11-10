import A166944.HorizonCrossing

/-!
# Bounding canonical replay growth by exceptional increments

A first hit is bounded by a linear combination of its index and the
previous horizon. Its cofactor bounds how long it can wait. Together
these facts control the growth due to increments outside a fixed
even common multiple.
-/

namespace A166944Research

private theorem moving_horizon_step_cofactor_gap {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    ∃ v : Nat, d r * v ≤ C + 1 ∧ r - s ≤ 2 * v := by
  rcases moving_horizon_step_event_package hstep with ⟨_, hdiv, hproper, _⟩ | ⟨_, hdiv, hproper, _⟩
  · obtain ⟨v, hv⟩ := hdiv
    have hv1 : 1 < v := by
      by_cases h : 1 < v
      · exact h
      · have hle := Nat.mul_le_mul_left (d r) (show v ≤ 1 by omega)
        simp only [Nat.mul_one] at hle
        omega
    have hdiv' : v ∣ C - 1 := ⟨d r, by simpa [Nat.mul_comm] using hv⟩
    exact ⟨v, by omega, moving_horizon_gap_le_twice_even_factor hstep hv1 hdiv'⟩
  · obtain ⟨v, hv⟩ := hdiv
    have hv1 : 1 < v := by
      by_cases h : 1 < v
      · exact h
      · have hle := Nat.mul_le_mul_left (d r) (show v ≤ 1 by omega)
        simp only [Nat.mul_one] at hle
        omega
    have hdiv' : v ∣ C + 1 := ⟨d r, by simpa [Nat.mul_comm] using hv⟩
    exact ⟨v, by omega, moving_horizon_gap_le_twice_odd_factor hstep hv1 hdiv'⟩

private theorem moving_horizon_step_gap_le_three_growth {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') : r - s ≤ 3 * (C' - C) := by
  have he3 := moving_horizon_step_event_ge_three hstep
  have hup := moving_horizon_step_update hstep
  have hgap : r - s ≤ 2 * d r := by
    rcases moving_horizon_step_event_package hstep with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩
    · exact moving_horizon_gap_le_twice_even_factor hstep (by omega) hd
    · exact moving_horizon_gap_le_twice_odd_factor hstep (by omega) hd
  omega

/-- A first-hit path travels at most three indices per unit of horizon growth. -/
theorem moving_horizon_path_gap_le_three_growth {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    s ≤ sf ∧ C ≤ Cf ∧ sf - s ≤ 3 * (Cf - C) := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, rfl, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨hrf, hCf, htailgap⟩ := ih htail
      have hsr := hstep.2.1
      have hup := moving_horizon_step_update hstep
      have hgap := moving_horizon_step_gap_le_three_growth hstep
      omega

private theorem dvd_le_sum_of_differences {e x y : Nat}
    (hx : e ∣ x) (hy : e ∣ y) (hne : x ≠ y) :
    e ≤ (x - y) + (y - x) := by
  by_cases h : x < y
  · have hle := Nat.le_of_dvd (by omega : 0 < y - x) (Nat.dvd_sub hy hx)
    omega
  · have hle := Nat.le_of_dvd (by omega : 0 < x - y) (Nat.dvd_sub hx hy)
    omega

/-- On a canonical replay, a large increment needs either horizon growth
before the event or a long gap immediately before it. -/
theorem canonical_path_step_offset_bound {M s C r C' p : Nat} (hM : 5 < M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') :
    d r ≤ 7 + 5 * (C - (2 * M - 2)) + 2 * (r - s) := by
  obtain ⟨hstart, hClo, hdist⟩ := moving_horizon_path_gap_le_three_growth hpath
  have hsr := hstep.2.1
  have hCpar : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · obtain ⟨hdivr, hdivC⟩ := moving_horizon_event_divisibility_even hstep rfl hr
    have hdiff := dvd_le_sum_of_differences (Nat.dvd_mul_left_of_dvd hdivr 2) hdivC (by omega)
    omega
  · obtain ⟨hdivr, hdivC⟩ := moving_horizon_event_divisibility_odd hstep rfl hr
    have hdiff := dvd_le_sum_of_differences (Nat.dvd_mul_left_of_dvd hdivr 2) hdivC (by omega)
    omega

/-- The cofactor removes the dependence on the last gap. A bound on
`4*(C+1)` by a square gives the displayed bound on the next increment. -/
theorem canonical_path_step_square_bound {M s C r C' p Q : Nat} (hM : 5 < M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hQ : 4 * (C + 1) ≤ Q * Q) :
    d r ≤ 7 + 5 * (C - (2 * M - 2)) + Q := by
  by_cases hsmall : d r ≤ Q
  · omega
  · obtain ⟨v, hvprod, hgap⟩ := moving_horizon_step_cofactor_gap hstep
    have h4v : 4 * v ≤ Q := by
      by_cases h : 4 * v ≤ Q
      · exact h
      · have hlo := Nat.mul_le_mul_left Q (show Q ≤ 4 * v by omega)
        have hlt := Nat.mul_lt_mul_of_pos_right (show Q < d r by omega)
          (show 0 < 4 * v by omega)
        have hhi := Nat.mul_le_mul_left 4 hvprod
        have heq : d r * (4 * v) = 4 * (d r * v) := by ac_rfl
        omega
    have hb := canonical_path_step_offset_bound hM hpath hstep
    omega

private theorem moving_horizon_path_before_nonunit {s C sf Cf p j : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p)
    (hsj : s < j) (hj : j ≤ sf) (he : d j ≠ 1) :
    ∃ sp Cp Cj q : Nat, HasMovingHorizonPathTo s C sp Cp q ∧
      IsMovingHorizonStep sp Cp j Cj := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨heq, _, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨hstart, r, C', hstep, htail⟩ := hpath
      by_cases h : j < r
      · exact False.elim (he (hstep.2.2.2.2.1 j hsj h))
      · by_cases hjr : j = r
        · subst j
          exact ⟨s, C, C', 0, ⟨rfl, rfl, hstart⟩, hstep⟩
        · obtain ⟨sp, Cp, Cj, q, hprefix, hlast⟩ := ih htail (by omega)
          exact ⟨sp, Cp, Cj, q + 1, ⟨hstart, r, C', hstep, hprefix⟩, hlast⟩

private theorem exists_last_nondvd {P s n : Nat}
    (hex : ∃ j : Nat, s < j ∧ j ≤ n ∧ ¬ d j ∣ P) :
    ∃ j : Nat, s < j ∧ j ≤ n ∧ ¬ d j ∣ P ∧
      ∀ i : Nat, j < i → i ≤ n → d i ∣ P := by
  induction n with
  | zero =>
      obtain ⟨j, hj, hle, _⟩ := hex
      omega
  | succ n ih =>
      by_cases h : d (n + 1) ∣ P
      · obtain ⟨j, hj, hle, hnd⟩ := hex
        have hlt : j ≤ n := by
          by_cases hjn : j = n + 1
          · exact False.elim (hnd (hjn.symm ▸ h))
          · omega
        obtain ⟨j', hj', hle', hnd', hlast⟩ := ih ⟨j, hj, hlt, hnd⟩
        refine ⟨j', hj', by omega, hnd', ?_⟩
        intro i hji hi
        by_cases hin : i = n + 1
        · simpa [hin] using h
        · exact hlast i hji (by omega)
      · obtain ⟨j, hj, hle, _⟩ := hex
        exact ⟨n + 1, by omega, Nat.le_refl _, h, fun i hi hil => False.elim (by omega)⟩

/-- A list covering the increments outside one even common multiple
bounds total growth on a genuine canonical prefix. Long runs of
increments dividing `P` cost less than `P`, independently of their length. -/
theorem canonical_path_growth_by_exception_list {M P Q s C p : Nat} (hM : 5 < M)
    (hcanon : d (M + 2) = M) (hP : 0 < P) (hPeven : P % 2 = 0)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hQ : 4 * (C + 1) ≤ Q * Q) (exceptions : List Nat)
    (hcover : ∀ j : Nat, M + 2 < j → j ≤ s → ¬ d j ∣ P → j ∈ exceptions) :
    C < 2 * M - 2 + 7 ^ exceptions.length * (P + Q + 6) := by
  have hDstart := (canonical_increment_coordinates hM hcanon).2.1
  let A := P + Q + 6
  have aux (k : Nat) : ∀ {s C p : Nat} (exceptions : List Nat),
      exceptions.length = k → HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p →
      4 * (C + 1) ≤ Q * Q →
      (∀ j : Nat, M + 2 < j → j ≤ s → ¬ d j ∣ P → j ∈ exceptions) →
      C < 2 * M - 2 + 7 ^ k * A := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro s C p exceptions hlen hpath hQ hcover
      have hDend := (moving_horizon_path_endpoint hpath).2.1
      by_cases hex : ∃ j : Nat, M + 2 < j ∧ j ≤ s ∧ ¬ d j ∣ P
      · obtain ⟨j, hj, hjs, hnd, hlast⟩ := exists_last_nondvd hex
        have hjunit : d j ≠ 1 := by
          intro h
          exact hnd (h.symm ▸ Nat.one_dvd P)
        obtain ⟨sp, Cp, Cj, q, hprefix, hstep⟩ :=
          moving_horizon_path_before_nonunit hpath hj hjs hjunit
        have hspj := hstep.2.1
        have hCp : Cp ≤ C := by
          rw [← hstep.1.2.1, ← hDend]
          exact D_le_of_le (by omega)
        have hQpre : 4 * (Cp + 1) ≤ Q * Q := by omega
        let rest := exceptions.erase j
        have hjmem := hcover j hj hjs hnd
        have hrest : rest.length + 1 = k := by
          have herase := List.length_erase_of_mem hjmem
          have hpos := List.length_pos_of_mem hjmem
          change rest.length = exceptions.length - 1 at herase
          omega
        have hcover' (i : Nat) (hi : M + 2 < i) (his : i ≤ sp) (hind : ¬ d i ∣ P) :
            i ∈ rest :=
          (List.mem_erase_of_ne (by omega : i ≠ j)).2 (hcover i hi (by omega) hind)
        have hpre := ih rest.length (by omega) rest rfl hprefix hQpre hcover'
        have hstepSize := canonical_path_step_square_bound hM hprefix hstep hQpre
        have hgrowth := moving_horizon_step_update hstep
        have hDj : D j = Cj := hstep.2.2.2.2.2.2.1.symm
        have htail := D_growth_lt_of_common_even_multiple (by omega : 2 ≤ j) hjs hP hPeven hlast
        rw [hDend, hDj] at htail
        have hClo := (moving_horizon_path_gap_le_three_growth hprefix).2.1
        have hA := Nat.mul_le_mul_right A (Nat.one_le_pow rest.length 7 (by decide))
        rw [Nat.one_mul] at hA
        rw [← hrest, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 7 A, ← Nat.mul_assoc]
        dsimp [A] at hpre hA ⊢
        omega
      · have hdiv (j : Nat) (hj : M + 2 < j) (hjs : j ≤ s) : d j ∣ P := by
          by_cases h : d j ∣ P
          · exact h
          · exact False.elim (hex ⟨j, hj, hjs, h⟩)
        have hstart := moving_horizon_path_index_le hpath
        have hsmall := D_growth_lt_of_common_even_multiple (by omega : 2 ≤ M + 2)
          hstart hP hPeven hdiv
        rw [hDstart, hDend] at hsmall
        have hA := Nat.mul_le_mul_right A (Nat.one_le_pow k 7 (by decide))
        rw [Nat.one_mul] at hA
        dsimp [A] at hA ⊢
        omega
  exact aux exceptions.length exceptions rfl hpath hQ hcover

/-- A large first crossing forces many exceptions to a fixed divisor
support when the previous record is large. -/
theorem canonical_large_old_crossing_exception_list {M s C p r C' P Q : Nat}
    (hM : 25 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r)
    (hP : 0 < P) (hPeven : P % 2 = 0) (hQ : 4 * (C + 1) ≤ Q * Q)
    (exceptions : List Nat)
    (hcover : ∀ j : Nat, M + 2 < j → j ≤ s → ¬ d j ∣ P → j ∈ exceptions) :
    M + 21 < 4 * (7 ^ exceptions.length * (P + Q + 6)) := by
  have hb := canonical_path_growth_by_exception_list (by omega) hcanon hP hPeven hpath hQ
    exceptions hcover
  have hshape := canonical_path_large_old_crossing hM hcanon hpath hstep hcap hbelow hcross hlarge
  have hC := hshape.2.1
  omega

/-- A large first crossing at a sufficiently large record needs at least
two earlier increments outside the even multiple 210. -/
theorem canonical_large_old_crossing_two_nondvd_210 {M s C p r C' : Nat}
    (hM : 65536 ≤ M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C') (hlarge : 3 * M + 3 < 4 * d r) :
    ∃ i j : Nat, M + 2 < i ∧ i < j ∧ j ≤ s ∧ ¬ d i ∣ 210 ∧ ¬ d j ∣ 210 := by
  by_cases htwo : ∃ i j : Nat, M + 2 < i ∧ i < j ∧ j ≤ s ∧ ¬ d i ∣ 210 ∧ ¬ d j ∣ 210
  · exact htwo
  · have hex : ∃ j : Nat, M + 2 < j ∧ j ≤ s ∧ ¬ d j ∣ 210 := by
      by_cases h : ∃ j : Nat, M + 2 < j ∧ j ≤ s ∧ ¬ d j ∣ 210
      · exact h
      · have hdiv (j : Nat) (hj : M + 2 < j) (hjs : j ≤ s) : d j ∣ 210 := by
          by_cases hd : d j ∣ 210
          · exact hd
          · exact False.elim (h ⟨j, hj, hjs, hd⟩)
        have hmul := canonical_large_old_crossing_prefix_multiple (by omega)
          hcanon hpath hstep hcap hbelow hcross hlarge (by decide) (by decide) hdiv
        omega
    obtain ⟨j, hj, hjs, hnd⟩ := hex
    have hcover (i : Nat) (hi : M + 2 < i) (his : i ≤ s) (hind : ¬ d i ∣ 210) : i ∈ [j] := by
      apply List.mem_singleton.2
      by_cases hij : i = j
      · exact hij
      · by_cases hlt : i < j
        · exact False.elim (htwo ⟨i, j, hi, hlt, hjs, hind, hnd⟩)
        · exact False.elim (htwo ⟨j, i, hj, by omega, his, hnd, hind⟩)
    let Q := M / 32
    have hQlo : 2048 ≤ Q := by omega
    have hQmul := Nat.mul_le_mul_right Q hQlo
    have hQ : 4 * (C + 1) ≤ Q * Q := by omega
    have hb := canonical_large_old_crossing_exception_list (by omega)
      hcanon hpath hstep hcap hbelow hcross hlarge (by decide) (by decide) hQ [j] hcover
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_one] at hb
    omega

private theorem moving_horizon_path_append_step {s C sf Cf r C' p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) (hstep : IsMovingHorizonStep sf Cf r C') :
    HasMovingHorizonPathTo s C r C' (p + 1) := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, rfl, hstate⟩ := hpath
      have hend : IsMovingHorizonState r C' := hstep.2.2.2.2.2.2.2.2
      exact ⟨hstate, r, C', hstep, rfl, rfl, hend⟩
  | succ p ih =>
      obtain ⟨hstate, t, Ct, ht, htail⟩ := hpath
      exact ⟨hstate, t, Ct, ht, ih htail⟩

/-- The same exception budget rules out a first crossing by any old
increment if the list covers the crossing index as well as the prefix. -/
theorem canonical_old_crossing_exception_list {M s C p r C' P Q : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C')
    (hP : 0 < P) (hPeven : P % 2 = 0) (hQ : 4 * (4 * M + 4) ≤ Q * Q)
    (exceptions : List Nat)
    (hcover : ∀ j : Nat, M + 2 < j → j ≤ r → ¬ d j ∣ P → j ∈ exceptions) :
    M + 6 < 7 ^ exceptions.length * (P + Q + 6) := by
  have hupdate := moving_horizon_step_update hstep
  have hQ' : 4 * (C' + 1) ≤ Q * Q := by omega
  have hgrowth := canonical_path_growth_by_exception_list hM hcanon hP hPeven
    (moving_horizon_path_append_step hpath hstep) hQ' exceptions hcover
  omega

/-- With a fixed even support and a fixed number of exceptions, any
first old crossing is confined to an explicit bounded range of `M`. -/
theorem canonical_old_crossing_bounded_of_exception_list {M s C p r C' P : Nat}
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) s C p)
    (hstep : IsMovingHorizonStep s C r C') (hcap : d r ≤ M)
    (hbelow : C ≤ 3 * M + 4) (hcross : 3 * M + 4 < C')
    (hP : 0 < P) (hPeven : P % 2 = 0) (exceptions : List Nat)
    (hcover : ∀ j : Nat, M + 2 < j → j ≤ r → ¬ d j ∣ P → j ∈ exceptions) :
    let A := 7 ^ exceptions.length
    M < max (128 * A * A) (2 * A * (P + 6)) := by
  let A := 7 ^ exceptions.length
  change M < max (128 * A * A) (2 * A * (P + 6))
  by_cases hbound : M < max (128 * A * A) (2 * A * (P + 6))
  · exact hbound
  · have hmax : max (128 * A * A) (2 * A * (P + 6)) ≤ M := by omega
    have hMlarge := Nat.le_trans (Nat.le_max_left (128 * A * A) (2 * A * (P + 6))) hmax
    have hMbudget := Nat.le_trans (Nat.le_max_right (128 * A * A) (2 * A * (P + 6))) hmax
    have hA : 0 < A := Nat.pow_pos (by decide)
    have hden : 0 < 2 * A := by omega
    let Q := M / (2 * A)
    have hQlo : 64 * A ≤ Q := (Nat.le_div_iff_mul_le hden).2 (by
      calc
        (64 * A) * (2 * A) = (64 * 2) * A * A := by ac_rfl
        _ = 128 * A * A := rfl
        _ ≤ M := hMlarge)
    have hMsplit := Nat.div_add_mod M (2 * A)
    change (2 * A) * Q + M % (2 * A) = M at hMsplit
    have hrem := Nat.mod_lt M hden
    have hMplus : M + 1 ≤ (2 * A) * (Q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hQ : 4 * (4 * M + 4) ≤ Q * Q := by
      calc
        4 * (4 * M + 4) = 16 * (M + 1) := by omega
        _ ≤ 16 * ((2 * A) * (Q + 1)) := Nat.mul_le_mul_left 16 hMplus
        _ = (32 * A) * (Q + 1) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        _ ≤ (32 * A) * (2 * Q) := Nat.mul_le_mul_left _ (by omega)
        _ = (64 * A) * Q := by
          calc
            (32 * A) * (2 * Q) = (32 * 2) * A * Q := by ac_rfl
            _ = (64 * A) * Q := rfl
        _ ≤ Q * Q := Nat.mul_le_mul_right Q hQlo
    have hbudget := canonical_old_crossing_exception_list hM hcanon hpath hstep hcap hbelow hcross
      hP hPeven hQ exceptions hcover
    change M + 6 < A * (P + Q + 6) at hbudget
    rw [show P + Q + 6 = (P + 6) + Q by omega, Nat.mul_add] at hbudget
    rw [Nat.mul_assoc] at hMbudget hMsplit
    omega

end A166944Research
