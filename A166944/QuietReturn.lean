import A166944.CanonicalTravel
import A166944.RecordReplay

/-!
# A long quiet return forces the twin factors

A small divisor of either horizon term produces a nonunit hit near the
horizon. A sufficiently early last old event therefore gives both the
next record's canonical index and its twin-primality certificate.
-/

namespace A166944Research

private theorem quiet_return_no_small_factors {s C root : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hlong : 2 * root < C - s) :
    NoSmallFactor (C - 1) root ∧ NoSmallFactor (C + 1) root := by
  have hs := hstate.1
  have hsc := hstate.2.2
  have hCe : C % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hs
  have hgcd (j : Nat) (hsj : s < j) (hjC : j ≤ C) :
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    have hD := first_later_event_D_eq hs hstate.2.1 hsj
      (fun i hsi hij => hquiet i hsi (by omega))
    have hmap := constant_D_event_map (by omega : 2 ≤ j) hD
    rw [hquiet j hsj hjC] at hmap
    constructor
    · intro h
      simpa only [h, if_pos] using hmap.symm
    · intro h
      simpa only [h, Nat.one_ne_zero, if_false] using hmap.symm
  constructor
  · intro f hf hdiv
    have hfle := f.isLt
    have hfodd : f.val % 2 = 1 := by
      by_cases h : f.val % 2 = 0
      · have h2 : 2 ∣ f.val := Nat.dvd_of_mod_eq_zero h
        have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hdiv)
        omega
      · omega
    let j := C - 1 - f.val
    have hsj : s < j := by omega
    have hjC : j ≤ C := by omega
    have hpar : j % 2 = 0 := by omega
    have hjdiv : f.val ∣ j := Nat.dvd_sub hdiv (Nat.dvd_refl _)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).1 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega
  · intro f hf hdiv
    have hfle := f.isLt
    let j := C + 3 - 2 * f.val
    have hsj : s < j := by omega
    have hjC : j ≤ C := by omega
    have hpar : j % 2 = 1 := by omega
    have hsub : j - 2 = C + 1 - 2 * f.val := by omega
    have hjdiv : f.val ∣ j - 2 := by
      rw [hsub]
      exact Nat.dvd_sub hdiv (Nat.dvd_mul_left_of_dvd (Nat.dvd_refl f.val) 2)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).2 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega

theorem quiet_return_no_proper_factors {s C : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hlong : 2 * Nat.sqrt (C + 1) < C - s) :
    NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  obtain ⟨hlo, hhi⟩ := quiet_return_no_small_factors hstate hquiet hlong
  have hroot : C + 1 < (Nat.sqrt (C + 1) + 1) * (Nat.sqrt (C + 1) + 1) :=
    Nat.lt_succ_sqrt (C + 1)
  exact ⟨no_proper_factor_of_no_small_factor hlo (by omega),
    no_proper_factor_of_no_small_factor hhi hroot⟩

private theorem long_quiet_gap_of_short_travel {M s C : Nat}
    (hM : 968 ≤ M) (hs : M + 2 ≤ s) (htravel : 2 * (s - (M + 2)) ≤ M)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) :
    2 * Nat.sqrt (C + 1) < C - s := by
  let q := Nat.sqrt (C + 1)
  let b := M / 8
  have hb : 121 ≤ b := by omega
  have hb2 := Nat.mul_le_mul_right b hb
  have hq2 : q * q ≤ C + 1 := Nat.sqrt_le _
  have hqb : q < b := by
    by_cases h : q < b
    · exact h
    · have hsq := Nat.mul_le_mul (show b ≤ q by omega) (show b ≤ q by omega)
      omega
  change 2 * q < C - s
  omega

/-- Short travel forces a quiet return, a canonical next record, and
factor certificates for both members of its twin pair. -/
theorem canonical_next_record_factors_of_short_travel {M : Nat}
    (hM : 968 ≤ M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (htravel : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have hM5 : 5 < M := by omega
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM5 hcanon).2.1, by omega⟩
  obtain ⟨sf, Cf, p, hpath, hfmax, hexit⟩ := capped_moving_horizon_eventual_exit hstart hmax
  have hsf := moving_horizon_path_index_le hpath
  have hstate := moving_horizon_path_endpoint hpath
  have hdist := htravel hpath hfmax
  have hhi := canonical_horizon_bound_of_short_travel hpath hdist
  have hlo := (moving_horizon_path_gap_le_three_growth hpath).2.1
  rcases hexit with ⟨_, hquiet⟩ | ⟨r, C', hstep, hnew⟩
  · obtain ⟨hgt, hpre, hd, _⟩ := canonical_quiet_return_next_record hM5 hlo hstate hfmax hquiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate hquiet
      (long_quiet_gap_of_short_travel hM hsf hdist hlo hhi)
    exact ⟨Cf, hgt, hpre, hd, hminus, hplus⟩
  · have hlow := moving_horizon_new_record_horizon_lower_bound hM5 hfmax hstep hnew
    omega

end A166944Research
