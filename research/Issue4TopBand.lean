import Mathlib.Tactic

set_option autoImplicit false

namespace Issue4TopBand

/-- The increasing index of the two q-clock residues in a period of length 2q:
    even indices give 0 mod 2q, odd indices give q+2 mod 2q. -/
def qClockSlot (q k : Nat) : Nat := k * q + 2 * (k % 2)

/-- A q-clock time is one of the two calendar residues modulo 2q. -/
def qClockTime (q n : Nat) : Prop := n % (2 * q) = 0 ∨ n % (2 * q) = q + 2

theorem qClockSlot_is_qClock {q k : Nat} (hq : 3 ≤ q) :
    qClockTime q (qClockSlot q k) := by
  unfold qClockTime
  by_cases hk : k % 2 = 0
  · have hkform : k = 2 * (k / 2) := by omega
    have hslot : qClockSlot q k = (2 * q) * (k / 2) := by
      unfold qClockSlot
      calc
        k * q + 2 * (k % 2) = k * q := by simp [hk]
        _ = (2 * (k / 2)) * q := congrArg (fun x : Nat => x * q) hkform
        _ = (2 * q) * (k / 2) := by ring
    left
    rw [hslot]
    exact Nat.mod_eq_zero_of_dvd ⟨k / 2, rfl⟩
  · have hkone : k % 2 = 1 := by omega
    have hkform : k = 2 * (k / 2) + 1 := by omega
    have hslot : qClockSlot q k = 2 * q * (k / 2) + (q + 2) := by
      unfold qClockSlot
      calc
        k * q + 2 * (k % 2) = k * q + 2 := by omega
        _ = (2 * (k / 2) + 1) * q + 2 := congrArg (fun x : Nat => x * q + 2) hkform
        _ = 2 * q * (k / 2) + (q + 2) := by ring
    right
    rw [hslot, Nat.add_mod]
    have hdiv : (2 * q * (k / 2)) % (2 * q) = 0 :=
      Nat.mod_eq_zero_of_dvd ⟨k / 2, rfl⟩
    simp [hdiv, Nat.mod_eq_of_lt (by omega : q + 2 < 2 * q)]

theorem qClockTime_iff_slot {q n : Nat} (hq : 3 ≤ q) :
    qClockTime q n ↔ ∃ k, qClockSlot q k = n := by
  constructor
  · rintro (hzero | hshift)
    · have hdvd : 2 * q ∣ n := Nat.dvd_of_mod_eq_zero hzero
      obtain ⟨a, ha⟩ := hdvd
      refine ⟨2 * a, ?_⟩
      calc
        qClockSlot q (2 * a) = (2 * q) * a := by
          unfold qClockSlot
          have hmod : (2 * a) % 2 = 0 := by omega
          rw [hmod]
          ring
        _ = n := ha.symm
    · have hdiv : n % (2 * q) + (2 * q) * (n / (2 * q)) = n :=
        Nat.mod_add_div n (2 * q)
      rw [hshift] at hdiv
      have hform : n = 2 * q * (n / (2 * q)) + (q + 2) := by omega
      refine ⟨2 * (n / (2 * q)) + 1, ?_⟩
      calc
        qClockSlot q (2 * (n / (2 * q)) + 1) =
            2 * q * (n / (2 * q)) + (q + 2) := by
          unfold qClockSlot
          have hmod : (2 * (n / (2 * q)) + 1) % 2 = 1 := by omega
          rw [hmod]
          ring
        _ = n := hform.symm
  · rintro ⟨k, rfl⟩
    exact qClockSlot_is_qClock hq

/-- The m-th later q-clock is no earlier than m*q-2 after the current one. -/
theorem qClockSlot_spread (q j m : Nat) :
    qClockSlot q j + m * q ≤ qClockSlot q (j + m) + 2 := by
  unfold qClockSlot
  rw [Nat.add_mul]
  have hmod : j % 2 ≤ (j + m) % 2 + 1 := by omega
  omega

/-- The calendar has strictly increasing slots once q≥3. -/
theorem qClockSlot_succ_lt {q k : Nat} (hq : 3 ≤ q) :
    qClockSlot q k < qClockSlot q (k + 1) := by
  have hspread := qClockSlot_spread q k 1
  omega

/-- All future q-clock slots before K, indexed by zero-based offsets. -/
def futureClockIndices (q j K : Nat) : Finset Nat :=
  (Finset.range ((K - qClockSlot q j + 2) / q)).filter
    (fun i => qClockSlot q (j + i + 1) ≤ K)

theorem qClockSlot_index_bound {q j m K : Nat} (hq : 0 < q)
    (hstart : qClockSlot q j ≤ K)
    (hfuture : qClockSlot q (j + m) ≤ K) :
    m ≤ (K - qClockSlot q j + 2) / q := by
  have hspread := qClockSlot_spread q j m
  have hmul : m * q ≤ K - qClockSlot q j + 2 := by omega
  exact (Nat.le_div_iff_mul_le hq).2 hmul

/-- Every q-clock time in the window after the tagged slot is represented by
    one of `futureClockIndices`. -/
theorem qClockTime_mem_futureClockIndices {q j K n : Nat}
    (hq : 3 ≤ q) (hstart : qClockSlot q j ≤ K)
    (hclock : qClockTime q n) (hafter : qClockSlot q j < n) (hcut : n ≤ K) :
    ∃ i, i ∈ futureClockIndices q j K ∧ qClockSlot q (j + i + 1) = n := by
  obtain ⟨k, hk⟩ := (qClockTime_iff_slot hq).mp hclock
  have hmono : StrictMono (qClockSlot q) :=
    strictMono_nat_of_lt_succ (fun k => qClockSlot_succ_lt hq)
  have hsk : qClockSlot q j < qClockSlot q k := by simpa [hk] using hafter
  have hjk : j < k := by
    by_contra hnot
    have hkj : k ≤ j := by omega
    have hval : qClockSlot q k ≤ qClockSlot q j := hmono.monotone hkj
    omega
  let m := k - j
  have hm : 0 < m := by dsimp [m]; omega
  have hjm : j + m = k := by dsimp [m]; omega
  have hslot : qClockSlot q (j + m) = n := by rw [hjm]; exact hk
  have hfuture : qClockSlot q (j + m) ≤ K := by rw [hslot]; exact hcut
  have hmBound := qClockSlot_index_bound (by omega : 0 < q) hstart hfuture
  let i := m - 1
  have hi : i < (K - qClockSlot q j + 2) / q := by dsimp [i]; omega
  have hidx : j + i + 1 = j + m := by dsimp [i]; omega
  have hmem : i ∈ futureClockIndices q j K := by
    unfold futureClockIndices
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hi
    · rw [hidx]
      exact hfuture
  refine ⟨i, hmem, ?_⟩
  rw [hidx]
  exact hslot

/-- The distinct phase offsets at those future q-clock slots. -/
def futurePhaseSet (q j K : Nat) (phase : Nat → Nat) : Finset Nat :=
  (futureClockIndices q j K).image phase

theorem futureClockIndices_card_le (q j K : Nat) :
    (futureClockIndices q j K).card ≤ (K - qClockSlot q j + 2) / q := by
  unfold futureClockIndices
  calc
    _ ≤ (Finset.range ((K - qClockSlot q j + 2) / q)).card := Finset.card_filter_le _ _
    _ = (K - qClockSlot q j + 2) / q := by simp

theorem futurePhaseSet_card_mul_q_le (q j K : Nat) (phase : Nat → Nat) :
    (futurePhaseSet q j K phase).card * q ≤ K - qClockSlot q j + 2 := by
  have himage : (futurePhaseSet q j K phase).card ≤ (futureClockIndices q j K).card :=
    Finset.card_image_le
  have hindices := futureClockIndices_card_le q j K
  calc
    (futurePhaseSet q j K phase).card * q ≤ (futureClockIndices q j K).card * q :=
      Nat.mul_le_mul_right q himage
    _ ≤ ((K - qClockSlot q j + 2) / q) * q :=
      Nat.mul_le_mul_right q hindices
    _ ≤ K - qClockSlot q j + 2 := Nat.div_mul_le_self _ _

theorem qClock_phase_mem_futurePhaseSet {q j K n : Nat}
    (hq : 3 ≤ q) (hstart : qClockSlot q j ≤ K)
    (hclock : qClockTime q n) (hafter : qClockSlot q j < n) (hcut : n ≤ K)
    (phase : Nat → Nat) :
    ∃ i, i ∈ futureClockIndices q j K ∧
      qClockSlot q (j + i + 1) = n ∧ phase i ∈ futurePhaseSet q j K phase := by
  obtain ⟨i, hi, htime⟩ := qClockTime_mem_futureClockIndices hq hstart hclock hafter hcut
  refine ⟨i, hi, htime, ?_⟩
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem phaseSubset_card_mul_q_le {q j K : Nat} (phase : Nat → Nat)
    (A : Finset Nat) (hA : A ⊆ futurePhaseSet q j K phase) :
    A.card * q ≤ K - qClockSlot q j + 2 := by
  have hcard : A.card ≤ (futurePhaseSet q j K phase).card := Finset.card_le_card hA
  calc
    A.card * q ≤ (futurePhaseSet q j K phase).card * q := Nat.mul_le_mul_right q hcard
    _ ≤ K - qClockSlot q j + 2 := futurePhaseSet_card_mul_q_le q j K phase

theorem topBand_q_scale {X B q : Nat} (hBsq : 7 * X ≤ B * B)
    (hBq : B ≤ 2 * q) : 7 * X ≤ 4 * q * q := by
  calc
    7 * X ≤ B * B := hBsq
    _ ≤ (2 * q) * (2 * q) := Nat.mul_le_mul hBq hBq
    _ = 4 * q * q := by ring

/-- The window ending at floor((7M-1)/4), after a tag at t≥M+3,
    has fewer than 3X/2 units of remaining time. -/
theorem topBand_window_bound {X M K t : Nat}
    (_hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ t) (hcut : t ≤ K) :
    4 * (K - t + 2) < 6 * X := by
  have hdiv : 4 * K ≤ 7 * M - 1 := by
    rw [hK]
    nlinarith [Nat.div_mul_le_self (7 * M - 1) 4]
  omega

/-- Exact integer form of the top-band phase contraction, conditional only on
    the q-calendar cardinal budget and q^2≥7X/4.  The conclusion is
    |phase set|/q < 6/7 without using real-number rounding. -/
theorem topBand_phase_contraction {X M K t q N : Nat}
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ t) (hcut : t ≤ K)
    (hcount : N * q ≤ K - t + 2) (hscale : 7 * X ≤ 4 * q * q) :
    7 * N < 6 * q := by
  have hwindow := topBand_window_bound hX hXM hM2X hK ht hcut
  have hprod : 4 * (N * q) < 6 * X := by
    have hmul : 4 * (N * q) ≤ 4 * (K - t + 2) := Nat.mul_le_mul_left 4 hcount
    omega
  have hleft : 28 * (N * q) < 42 * X := by nlinarith
  have hright : 42 * X ≤ 24 * (q * q) := by nlinarith
  have hmul : (4 * q) * (7 * N) < (4 * q) * (6 * q) := by
    calc
      (4 * q) * (7 * N) = 28 * (N * q) := by ring
      _ < 24 * (q * q) := lt_of_lt_of_le hleft hright
      _ = (4 * q) * (6 * q) := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

theorem futurePhaseSet_topBand_contraction {X M K q j : Nat}
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ qClockSlot q j)
    (hcut : qClockSlot q j ≤ K) (hscale : 7 * X ≤ 4 * q * q)
    (phase : Nat → Nat) :
    7 * (futurePhaseSet q j K phase).card < 6 * q := by
  exact topBand_phase_contraction hX hXM hM2X hK ht hcut
    (futurePhaseSet_card_mul_q_le q j K phase) hscale

theorem phaseSubset_topBand_contraction {X M K q j : Nat}
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ qClockSlot q j)
    (hcut : qClockSlot q j ≤ K) (hscale : 7 * X ≤ 4 * q * q)
    (phase : Nat → Nat) (A : Finset Nat)
    (hA : A ⊆ futurePhaseSet q j K phase) :
    7 * A.card < 6 * q := by
  exact topBand_phase_contraction hX hXM hM2X hK ht hcut
    (phaseSubset_card_mul_q_le phase A hA) hscale

#print axioms qClockSlot_is_qClock
#print axioms qClockTime_iff_slot
#print axioms qClockSlot_spread
#print axioms qClockSlot_succ_lt
#print axioms qClockSlot_index_bound
#print axioms qClockTime_mem_futureClockIndices
#print axioms futureClockIndices_card_le
#print axioms futurePhaseSet_card_mul_q_le
#print axioms qClock_phase_mem_futurePhaseSet
#print axioms phaseSubset_card_mul_q_le
#print axioms topBand_q_scale
#print axioms topBand_window_bound
#print axioms topBand_phase_contraction
#print axioms futurePhaseSet_topBand_contraction
#print axioms phaseSubset_topBand_contraction

end Issue4TopBand
