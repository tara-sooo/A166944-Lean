import A166944.SeparatorBlocks210

/-!
# Credit allocations with first-phase funding

Small increments have bounded positive balances. Charging at most once
for each small increment and phase gives a fixed startup cost. A finite
allocation records both the allowed sources and the total use of each
source, including additional credit charged to first-phase travel.
-/

open Finset

namespace A166944Research

theorem prime_phase_separator_balance210_le_increment {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') :
    primePhaseSeparatorBalance210 phase seen s C r C' ≤ 45 * (d r : Int) + 1263 := by
  have hgap := moving_horizon_step_gap_le_twice_increment hstep
  have hE : longPrimePhaseExcess phase seen s C r ≤ 48 * d r - (d r - 1) := by
    unfold longPrimePhaseExcess
    split
    · omega
    · unfold shortOrReusedTravelExcess shortOrReusedTravelGap
      split <;> omega
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  unfold primePhaseSeparatorBalance210
  split <;> omega

theorem small_prime_phase_separator_positive_part_le210 {slots s C r C' : Nat}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hstep : IsMovingHorizonStep s C r C') (hsmall : d r ≤ 630) :
    (primePhaseSeparatorBalance210 phase seen s C r C').toNat ≤ 29613 := by
  have h := prime_phase_separator_balance210_le_increment (phase := phase) (seen := seen) hstep
  omega

def smallPhaseStartupBound210 : Nat := (631 * 420) * 29613

structure FundedPhaseCreditAllocation210 {n m : Nat}
    (cost : Fin n → Int) (key : Fin n → Fin (631 * 420))
    (eligible : Fin n → Fin m → Prop) (first multiplier : Nat) where
  startup : Finset (Fin n)
  startup_unique : Set.InjOn key (startup : Set (Fin n))
  startup_cap : ∀ i ∈ startup, (cost i).toNat ≤ 29613
  supply : Fin m → Nat
  allocation : Fin n → Fin m → Nat
  allowed : ∀ i j, 0 < allocation i j → eligible i j
  paid : ∀ i, i ∉ startup → (cost i).toNat ≤ ∑ j, allocation i j
  capacity : ∀ j, (∑ i, allocation i j) ≤ supply j
  funding : (∑ j, supply j) ≤ (∑ i, (-cost i).toNat) + multiplier * first

/-- Row bounds pay the positive costs and column bounds prevent using
one unit of supply twice. Startup keys need only be distinct there. -/
theorem funded_phase_credit_allocation_bound210 {n m first multiplier : Nat}
    {cost : Fin n → Int} {key : Fin n → Fin (631 * 420)}
    {eligible : Fin n → Fin m → Prop}
    (certificate : FundedPhaseCreditAllocation210 cost key eligible first multiplier) :
    (∑ i, cost i) ≤ ((smallPhaseStartupBound210 + multiplier * first : Nat) : Int) := by
  have hcard : certificate.startup.card ≤ 631 * 420 := by
    have h := Finset.card_le_card_of_injOn key (t := Finset.univ)
      (fun i _ => Finset.mem_univ (key i)) certificate.startup_unique
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hrow (i : Fin n) : (cost i).toNat ≤
      (if i ∈ certificate.startup then 29613 else 0) + ∑ j, certificate.allocation i j := by
    by_cases hi : i ∈ certificate.startup
    · rw [if_pos hi]
      have h := certificate.startup_cap i hi
      omega
    · simpa only [if_neg hi, Nat.zero_add] using certificate.paid i hi
  have hpositive := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [Finset.sum_add_distrib] at hpositive
  have hstartup : (∑ i : Fin n, if i ∈ certificate.startup then 29613 else 0) =
      certificate.startup.card * 29613 := by simp
  have hsupplies : (∑ i, ∑ j, certificate.allocation i j) ≤ ∑ j, certificate.supply j := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => certificate.capacity j)
  rw [hstartup] at hpositive
  have hstart := Nat.mul_le_mul_right 29613 hcard
  change certificate.startup.card * 29613 ≤ smallPhaseStartupBound210 at hstart
  have hfund := certificate.funding
  have hcost : (∑ i, cost i) = ((∑ i, (cost i).toNat : Nat) : Int) -
      ((∑ i, (-cost i).toNat : Nat) : Int) := by
    calc
      (∑ i, cost i) = ∑ i, (((cost i).toNat : Int) - ((-cost i).toNat : Int)) :=
        Finset.sum_congr rfl (fun i _ => by omega)
      _ = _ := by rw [Finset.sum_sub_distrib, Nat.cast_sum, Nat.cast_sum]
  omega

/-- Under the allocation certificate, the signed sum is uniformly
sublinear on short canonical prefixes, including all startup charges. -/
theorem canonical_funded_phase_balance_sublinear210 (slots multiplier k : Nat) (hk : 0 < k) :
    ∃ threshold : Nat, ∀ {M sf Cf q first n m : Nat} {separators : Int}
      {phase : Nat → Nat → Fin slots} {cost : Fin n → Int}
      {key : Fin n → Fin (631 * 420)} {eligible : Fin n → Fin m → Prop},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonPhaseBalances210 phase (M + 2) (2 * M - 2) sf Cf [] q first separators →
      2 * (sf - (M + 2)) ≤ M → (∑ i, cost i) = separators →
      FundedPhaseCreditAllocation210 cost key eligible first multiplier → k * separators.toNat ≤ M := by
  have hfactor : 0 < 2 * k * (multiplier + 1) :=
    Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hk) (Nat.succ_pos multiplier)
  obtain ⟨threshold, hfirst⟩ :=
    canonical_first_prime_phase_travel_sublinear slots (2 * k * (multiplier + 1)) hfactor
  refine ⟨max threshold (2 * k * smallPhaseStartupBound210), ?_⟩
  intro M sf Cf q first n m separators phase cost key eligible hM hcanon hledger hshort hsum certificate
  have hF := hfirst (le_trans (le_max_left _ _) hM) hcanon hledger hshort
  have hstartup : 2 * k * smallPhaseStartupBound210 ≤ M := le_trans (le_max_right _ _) hM
  have hbound := funded_phase_credit_allocation_bound210 certificate
  rw [hsum] at hbound
  have hnonneg : separators.toNat ≤ smallPhaseStartupBound210 + multiplier * first := by omega
  have hmul := Nat.mul_le_mul_left (2 * k) hnonneg
  have hlarge : (2 * k) * (multiplier * first) ≤ (2 * k * (multiplier + 1)) * first := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right first (Nat.mul_le_mul_left (2 * k) (by omega : multiplier ≤ multiplier + 1))
  rw [Nat.mul_add] at hmul
  have hpaid := hlarge.trans hF
  have htwice : (2 * k) * separators.toNat = 2 * (k * separators.toNat) := Nat.mul_assoc _ _ _
  omega

private theorem ninety_six_mul_crossing_gap_bound {M : Nat} (hM : 147456 ≤ M) :
    96 * Nat.sqrt (4 * (3 * M + 4)) ≤ M := by
  let Q := Nat.sqrt (4 * (3 * M + 4))
  change 96 * Q ≤ M
  apply Nat.mul_self_le_mul_self_iff.mp
  have hQ : Q * Q ≤ 4 * (3 * M + 4) := Nat.sqrt_le _
  calc
    (96 * Q) * (96 * Q) = (96 * 96) * (Q * Q) := by ac_rfl
    _ ≤ (96 * 96) * (16 * M) := Nat.mul_le_mul_left _ (by omega)
    _ = 147456 * M := by omega
    _ ≤ M * M := Nat.mul_le_mul_right _ hM

/-- If every short capped prefix admits the funded allocation, all sufficiently
large capped canonical paths satisfy short travel. Allocation existence is the
explicit unproved hypothesis. -/
theorem canonical_travel_of_funded_prefix_allocations210 (slots multiplier : Nat) :
    ∃ threshold : Nat, ∀ {M sf Cf q : Nat} (phase : Nat → Nat → Fin slots),
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q →
      IsAttainedPreviousMaximum M sf →
      (∀ {s C p first : Nat} {separators : Int},
        HasMovingHorizonPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first separators →
        2 * (s - (M + 2)) ≤ M →
        IsAttainedPreviousMaximum M s →
        ∃ (n m : Nat) (cost : Fin n → Int) (key : Fin n → Fin (631 * 420))
          (eligible : Fin n → Fin m → Prop),
          (∑ i, cost i) = separators ∧
            Nonempty (FundedPhaseCreditAllocation210 cost key eligible first multiplier)) →
      2 * (sf - (M + 2)) ≤ M := by
  obtain ⟨firstThreshold, hfirst⟩ := canonical_first_prime_phase_travel_sublinear slots 96 (by decide)
  obtain ⟨signedThreshold, hsigned⟩ := canonical_funded_phase_balance_sublinear210 slots multiplier 4 (by decide)
  refine ⟨max (max firstThreshold signedThreshold) 147456, ?_⟩
  intro M sf Cf q phase hM hcanon hpath hmax hallocate
  have hMF : firstThreshold ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMS : signedThreshold ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMLarge : 147456 ≤ M := le_trans (le_max_right _ _) hM
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, separators, hledger, hstep, hr, _, hs, _, hgap, hcross⟩ :=
      canonical_first_crossing_requires_phase_balances210 phase hcanon hpath (by omega)
    have hstart := moving_horizon_path_index_le (moving_horizon_phase_balances210_path hledger)
    have hsr := hstep.2.1
    have hmax' : IsAttainedPreviousMaximum M s :=
      ⟨fun j hj hjs => hmax.1 j hj (by omega), ⟨M + 2, by omega, hstart, hcanon⟩⟩
    obtain ⟨n, m, cost, key, eligible, hsum, ⟨certificate⟩⟩ := hallocate hledger hs hmax'
    have hF := hfirst hMF hcanon hledger hs
    have hS := hsigned hMS hcanon hledger hs hsum certificate
    have hQ := ninety_six_mul_crossing_gap_bound hMLarge
    have hg := (Nat.mul_le_mul_left 96 hgap).trans hQ
    omega

end A166944Research
