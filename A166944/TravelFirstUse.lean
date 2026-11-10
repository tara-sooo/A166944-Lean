import A166944.TravelFactors
import Mathlib.NumberTheory.Primorial

/-!
# Bounding the gaps at first uses of primes

Small first-used primes occur at most once and can be paid for by a
sum of distinct primes. For large increments the cofactor gives a
better gap bound, which can be summed against horizon growth.
-/

open Finset

namespace A166944Research

private def unusedPrimesLE (L : Nat) (seen : List Nat) : Finset Nat :=
  (Nat.primesLE L).filter (IsNewIncrementFactor seen)

private theorem unusedPrimesLE_cons_subset (L e : Nat) (seen : List Nat) :
    unusedPrimesLE L (e :: seen) ⊆ unusedPrimesLE L seen := by
  intro p hp
  obtain ⟨hprime, hnew⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hprime, fun x hx => hnew x (List.mem_cons_of_mem e hx)⟩

private theorem unusedPrimesLE_sum_cons_add {L e : Nat} {seen : List Nat}
    (he : e ∈ unusedPrimesLE L seen) :
    (∑ p ∈ unusedPrimesLE L (e :: seen), p) + e ≤ ∑ p ∈ unusedPrimesLE L seen, p := by
  have hnot : e ∉ unusedPrimesLE L (e :: seen) := by
    intro h
    exact (Finset.mem_filter.mp h).2 e (List.mem_cons_self) (Nat.dvd_refl _)
  have hsub : insert e (unusedPrimesLE L (e :: seen)) ⊆ unusedPrimesLE L seen :=
    Finset.insert_subset he (unusedPrimesLE_cons_subset L e seen)
  have hsum := Finset.sum_le_sum_of_subset (f := id) hsub
  rw [Finset.sum_insert hnot, add_comm] at hsum
  exact hsum

private theorem moving_horizon_large_increment_gap {s C r C' L U : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hL : L < d r) (hU : C ≤ U) :
    (L * (L + 1)) * (r - s) ≤ 2 * (U + 1) * (C' - C) := by
  obtain ⟨v, hv, hgap⟩ := moving_horizon_step_cofactor_gap hstep
  have hge : (r - s) * d r ≤ 2 * (U + 1) := by
    calc
      (r - s) * d r ≤ (2 * v) * d r := Nat.mul_le_mul_right _ hgap
      _ = 2 * (d r * v) := by ac_rfl
      _ ≤ 2 * (U + 1) := Nat.mul_le_mul_left _ (by omega)
  have hsize := Nat.mul_le_mul (by omega : L ≤ d r - 1) (by omega : L + 1 ≤ d r)
  have hupdate := moving_horizon_step_update hstep
  calc
    (L * (L + 1)) * (r - s) ≤ ((d r - 1) * d r) * (r - s) := Nat.mul_le_mul_right _ hsize
    _ = ((r - s) * d r) * (d r - 1) := by ac_rfl
    _ ≤ 2 * (U + 1) * (d r - 1) := Nat.mul_le_mul_right _ hge
    _ = 2 * (U + 1) * (C' - C) := by rw [hupdate, Nat.add_sub_cancel_left]

private theorem moving_horizon_first_use_weighted_bound {s C sf Cf q first L U : Nat}
    {seen : List Nat} (hcost : HasMovingHorizonFirstUseTravel s C sf Cf seen q first)
    (hU : Cf ≤ U) :
    C ≤ Cf ∧ (L * (L + 1)) * first ≤
      (L * (L + 1)) * (2 * ∑ p ∈ unusedPrimesLE L seen, p) + 2 * (U + 1) * (Cf - C) := by
  induction q generalizing s C seen first with
  | zero =>
    obtain ⟨⟨_, rfl, _⟩, rfl⟩ := hcost
    simp
  | succ q ih =>
    obtain ⟨r, C', rest, hstep, hrest, htotal⟩ := hcost
    obtain ⟨hC'f, htail⟩ := ih hrest
    have hup := moving_horizon_step_update hstep
    have hCf : C ≤ Cf := by omega
    refine ⟨hCf, ?_⟩
    let W := L * (L + 1)
    let K := 2 * (U + 1)
    let nextSum := ∑ p ∈ unusedPrimesLE L (d r :: seen), p
    let nowSum := ∑ p ∈ unusedPrimesLE L seen, p
    change W * rest ≤ W * (2 * nextSum) + K * (Cf - C') at htail
    change W * first ≤ W * (2 * nowSum) + K * (Cf - C)
    have hsum : nextSum ≤ nowSum := Finset.sum_le_sum_of_subset (f := id)
      (unusedPrimesLE_cons_subset L (d r) seen)
    have hgrowth : K * (Cf - C) = K * (Cf - C') + K * (C' - C) := by
      rw [← Nat.mul_add, show Cf - C' + (C' - C) = Cf - C by omega]
    by_cases hf : 10 < r - s ∧ NoProperFactor (d r) ∧ IsNewIncrementFactor seen (d r)
    · simp only [firstUseTravelGap, if_pos hf] at htotal
      rw [htotal, Nat.mul_add, hgrowth]
      by_cases hsmall : d r ≤ L
      · have hprime := Nat.prime_def_lt'.mpr ⟨hstep.2.2.2.1,
          fun f hf' hlt => hf.2.1 ⟨f, hlt⟩ hf'⟩
        have hmem : d r ∈ unusedPrimesLE L seen :=
          Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hsmall, hprime⟩, hf.2.2⟩
        have hsum' : nextSum + d r ≤ nowSum := unusedPrimesLE_sum_cons_add hmem
        have hpay : W * (2 * nextSum) + W * (2 * d r) ≤ W * (2 * nowSum) := by
          rw [← Nat.mul_add, ← Nat.mul_add]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum')
        have hgap := Nat.mul_le_mul_left W (moving_horizon_step_gap_le_twice_increment hstep)
        omega
      · have hlarge : W * (r - s) ≤ K * (C' - C) :=
          moving_horizon_large_increment_gap hstep (by omega) (by omega : C ≤ U)
        have hpay := Nat.mul_le_mul_left W (Nat.mul_le_mul_left 2 hsum)
        omega
    · simp only [firstUseTravelGap, if_neg hf, Nat.zero_add] at htotal
      rw [htotal, hgrowth]
      have hpay := Nat.mul_le_mul_left W (Nat.mul_le_mul_left 2 hsum)
      omega

/-- At an arbitrary cutoff `L`, pay once for each small prime and use
the cofactor bound against total horizon growth for the large primes. -/
theorem moving_horizon_first_use_travel_bound {s C sf Cf q first L U : Nat}
    (hcost : HasMovingHorizonFirstUseTravel s C sf Cf [] q first) (hU : Cf ≤ U) (hL : 0 < L) :
    first ≤ 2 * (∑ p ∈ Nat.primesLE L, p) +
      (2 * (U + 1) * (Cf - C)) / (L * (L + 1)) := by
  obtain ⟨_, hbound⟩ := moving_horizon_first_use_weighted_bound (L := L) hcost hU
  have hs : unusedPrimesLE L [] = Nat.primesLE L := by
    simp [unusedPrimesLE, IsNewIncrementFactor]
  rw [hs] at hbound
  let W := L * (L + 1)
  let low := 2 * (∑ p ∈ Nat.primesLE L, p)
  let growth := 2 * (U + 1) * (Cf - C)
  change W * first ≤ W * low + growth at hbound
  change first ≤ low + growth / W
  have hpos : 0 < W := Nat.mul_pos hL (by omega)
  have hd : (first - low) * W ≤ growth := by
    rw [Nat.sub_mul, Nat.mul_comm first W, Nat.mul_comm low W]
    omega
  have h := (Nat.le_div_iff_mul_le hpos).2 hd
  omega

theorem canonical_first_use_travel_bound {M sf Cf q first L : Nat}
    (hcanon : d (M + 2) = M)
    (hcost : HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) sf Cf [] q first)
    (hshort : 2 * (sf - (M + 2)) ≤ M) (hL : 0 < L) :
    first ≤ 2 * (∑ p ∈ Nat.primesLE L, p) +
      (2 * (3 * M + 4) * (Cf - (2 * M - 2))) / (L * (L + 1)) := by
  have hpath := moving_horizon_first_use_travel_path hcost
  have hC := canonical_horizon_bound_of_short_travel hpath hshort
  have hstate := moving_horizon_path_endpoint hpath
  have hCe := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hstart := moving_horizon_path_index_le hpath
  have hMpos : 0 < M := by
    have h := one_le_d_of_two_le (by omega : 2 ≤ M + 2)
    omega
  have hMo := hcanon ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
  have h := moving_horizon_first_use_travel_bound hcost (by omega : Cf ≤ 3 * M + 3) hL
  rwa [show 3 * M + 3 + 1 = 3 * M + 4 by omega] at h

/-- A natural-number form of zero prime density. Each prime at least
`4^k` contributes a factor of at least `4^k` to the primorial. -/
private theorem prime_counting_mul_le_add (n k : Nat) :
    k * Nat.primeCounting n ≤ n + k * 4 ^ k := by
  let large := (Nat.primesLE n).filter fun p => 4 ^ k ≤ p
  let small := (Nat.primesLE n).filter fun p => ¬ 4 ^ k ≤ p
  have hlarge : k * large.card ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (4 : Nat))).mp
    calc
      4 ^ (k * large.card) = (4 ^ k) ^ large.card := pow_mul 4 k large.card
      _ ≤ ∏ p ∈ large, p :=
        Finset.pow_card_le_prod large id (4 ^ k) (fun p hp => (Finset.mem_filter.mp hp).2)
      _ ≤ primorial n := by
        rw [primorial_eq_prod_primesLE]
        exact Finset.prod_le_prod_of_subset_of_one_le' (f := id) (Finset.filter_subset _ _)
          (fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_le)
      _ ≤ 4 ^ n := primorial_le_four_pow n
  have hsmall : small.card ≤ 4 ^ k := by
    rw [← Finset.card_range (4 ^ k)]
    exact Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2))
  have hcard : large.card + small.card = Nat.primeCounting n := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_filter_add_card_filter_not (fun p => 4 ^ k ≤ p)
  rw [← hcard, Nat.mul_add]
  exact Nat.add_le_add hlarge (Nat.mul_le_mul_left k hsmall)

/-- Uniform sublinearity of first-use prime travel on all short
canonical prefixes. The threshold may depend on the requested factor. -/
theorem canonical_first_use_travel_sublinear (k : Nat) (hk : 0 < k) :
    ∃ threshold : Nat, ∀ {M sf Cf q first : Nat}, threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) sf Cf [] q first →
      2 * (sf - (M + 2)) ≤ M → k * first ≤ M := by
  let A := 32 * k
  let K := A * (A * A)
  let B := K * 4 ^ K
  refine ⟨max 6 (B * B), ?_⟩
  intro M sf Cf q first hM hcanon hcost hshort
  have hM6 : 6 ≤ M := le_trans (le_max_left _ _) hM
  have hA : 0 < A := by omega
  let root := Nat.sqrt M
  let L := A * (root + 1)
  let W := L * (L + 1)
  let G := 2 * (3 * M + 4) * (Cf - (2 * M - 2))
  have hL : 0 < L := Nat.mul_pos hA (by omega)
  have hroot : root * root ≤ M := Nat.sqrt_le M
  have hroot' : M < (root + 1) * (root + 1) := Nat.lt_succ_sqrt M
  have hB : B ≤ root + 1 := by
    by_cases h : B ≤ root + 1
    · exact h
    · have hle : (root + 1) * (root + 1) ≤ B * B :=
        Nat.mul_le_mul (by omega : root + 1 ≤ B) (by omega)
      have hBM : B * B ≤ M := le_trans (le_max_right _ _) hM
      omega
  have hrootL : root + 1 ≤ L := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (root + 1) (by omega : 1 ≤ A)
  have hBL := hB.trans hrootL
  have hW : A * M ≤ W := by
    calc
      A * M ≤ A * ((root + 1) * (root + 1)) := Nat.mul_le_mul_left _ hroot'.le
      _ = L * (root + 1) := (Nat.mul_assoc A (root + 1) (root + 1)).symm
      _ ≤ W := Nat.mul_le_mul_left L (by omega : root + 1 ≤ L + 1)
  have hpath := moving_horizon_first_use_travel_path hcost
  have hCf := canonical_horizon_bound_of_short_travel hpath hshort
  have hG : G ≤ 16 * (M * M) := by
    change (2 * (3 * M + 4)) * (Cf - (2 * M - 2)) ≤ 16 * (M * M)
    calc
      _ ≤ (8 * M) * (2 * M) := Nat.mul_le_mul (by omega) (by omega)
      _ = 16 * (M * M) := by
        rw [show (16 : Nat) = 8 * 2 by decide]
        ac_rfl
  have hlarge : (2 * k) * (G / W) ≤ M := by
    have hWpos : 0 < W := Nat.mul_pos hL (by omega)
    apply Nat.le_of_mul_le_mul_left (c := W) _ hWpos
    calc
      W * ((2 * k) * (G / W)) = (2 * k) * (W * (G / W)) := by ac_rfl
      _ ≤ (2 * k) * G := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      _ ≤ (2 * k) * (16 * (M * M)) := Nat.mul_le_mul_left _ hG
      _ = (A * M) * M := by
        rw [show A = 32 * k by rfl, show (32 : Nat) = 2 * 16 by decide]
        ac_rfl
      _ ≤ W * M := Nat.mul_le_mul_right _ hW
  have hpi : K * Nat.primeCounting L ≤ 2 * L := by
    have hcount := prime_counting_mul_le_add L K
    change K * Nat.primeCounting L ≤ L + B at hcount
    omega
  have hrootPos : 1 ≤ root := by
    by_cases h : root = 0
    · simp [h] at hroot'
      omega
    · omega
  have hLsq : L * L ≤ (A * A) * (4 * M) := by
    calc
      L * L = (A * A) * ((root + 1) * (root + 1)) := by
        rw [show L = A * (root + 1) by rfl]
        ac_rfl
      _ ≤ (A * A) * ((2 * root) * (2 * root)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = (A * A) * (4 * (root * root)) := by
        rw [show (4 : Nat) = 2 * 2 by decide]
        ac_rfl
      _ ≤ (A * A) * (4 * M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hroot)
  have hpiWeighted : A * (L * Nat.primeCounting L) ≤ 8 * M := by
    apply Nat.le_of_mul_le_mul_left (c := A * A) _ (Nat.mul_pos hA hA)
    calc
      (A * A) * (A * (L * Nat.primeCounting L)) = (K * Nat.primeCounting L) * L := by
        rw [show K = A * (A * A) by rfl]
        ac_rfl
      _ ≤ (2 * L) * L := Nat.mul_le_mul_right _ hpi
      _ = 2 * (L * L) := Nat.mul_assoc _ _ _
      _ ≤ 2 * ((A * A) * (4 * M)) := Nat.mul_le_mul_left _ hLsq
      _ = (A * A) * (8 * M) := by
        rw [show (8 : Nat) = 2 * 4 by decide]
        ac_rfl
  have hsum : (∑ p ∈ Nat.primesLE L, p) ≤ L * Nat.primeCounting L := by
    calc
      _ ≤ ∑ _ ∈ Nat.primesLE L, L := Finset.sum_le_sum fun _ hp => Nat.le_of_mem_primesLE hp
      _ = L * Nat.primeCounting L := by
        rw [Finset.sum_const, Nat.primesLE_card_eq_primeCounting, nsmul_eq_mul, Nat.mul_comm]
        rfl
  have hsmall : (2 * k) * (2 * ∑ p ∈ Nat.primesLE L, p) ≤ M := by
    have h := Nat.mul_le_mul_left A hsum
    have h8 : 8 * ((2 * k) * (2 * ∑ p ∈ Nat.primesLE L, p)) = A * ∑ p ∈ Nat.primesLE L, p := by
      rw [show A = 32 * k by rfl, show (32 : Nat) = 8 * 2 * 2 by decide]
      ac_rfl
    omega
  have hF := canonical_first_use_travel_bound hcanon hcost hshort hL
  change first ≤ 2 * (∑ p ∈ Nat.primesLE L, p) + G / W at hF
  have h := Nat.mul_le_mul_left (2 * k) hF
  rw [Nat.mul_add, Nat.mul_assoc] at h
  omega

private theorem forty_eight_mul_crossing_gap_bound {M : Nat} (hM : 36864 ≤ M) :
    48 * Nat.sqrt (4 * (3 * M + 4)) ≤ M := by
  let Q := Nat.sqrt (4 * (3 * M + 4))
  change 48 * Q ≤ M
  apply Nat.mul_self_le_mul_self_iff.mp
  have hQ : Q * Q ≤ 4 * (3 * M + 4) := Nat.sqrt_le _
  calc
    (48 * Q) * (48 * Q) = (48 * 48) * (Q * Q) := by ac_rfl
    _ ≤ (48 * 48) * (16 * M) := Nat.mul_le_mul_left _ (by omega)
    _ = 36864 * M := by omega
    _ ≤ M * M := Nat.mul_le_mul_right _ hM

/-- For sufficiently large canonical starts, any first violation of
short travel needs more than `M/12` distance from short gaps and long
gaps ending at a previously used prime. -/
theorem canonical_travel_crossing_requires_short_or_reused :
    ∃ threshold : Nat, ∀ {M sf Cf q : Nat}, threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q → M < 2 * (sf - (M + 2)) →
      ∃ s C r C' p total first : Nat,
        HasMovingHorizonResidualTravel (M + 2) (2 * M - 2) s C p total ∧
        HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) s C [] p first ∧
        IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
        2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧ M < 12 * (total - first) := by
  obtain ⟨threshold, hbound⟩ := canonical_first_use_travel_sublinear 48 (by decide)
  refine ⟨max threshold 36864, ?_⟩
  intro M sf Cf q hM hcanon hpath hlong
  obtain ⟨s, C, r, C', p, total, hres, hstep, hr, hp, hshort, hcross, _, hlarge⟩ :=
    canonical_first_travel_crossing_residual hcanon hpath hlong
  obtain ⟨first, hfirst, hle⟩ := moving_horizon_residual_travel_first_use hres []
  have hF := hbound (le_trans (le_max_left _ _) hM) hcanon hfirst hshort
  have hMlarge : 36864 ≤ M := le_trans (le_max_right _ _) hM
  have hQ := forty_eight_mul_crossing_gap_bound hMlarge
  refine ⟨s, C, r, C', p, total, first, hres, hfirst, hstep, hr, hp, hshort, hcross, ?_⟩
  omega

end A166944Research
