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

/-- For odd q, the residue-only calendar is exactly the parity-labelled one. -/
theorem qClockTime_iff_sourceCalendar {q n : Nat} (hqodd : q % 2 = 1) :
    qClockTime q n ↔
      ((n % 2 = 0 ∧ n % (2 * q) = 0) ∨
       (n % 2 = 1 ∧ n % (2 * q) = q + 2)) := by
  constructor
  · intro hclock
    rcases hclock with hzero | hshift
    · left
      constructor
      · have h2q : 2 ∣ 2 * q := ⟨q, by ring⟩
        have hn2 : 2 ∣ n := Nat.dvd_trans h2q (Nat.dvd_of_mod_eq_zero hzero)
        exact Nat.mod_eq_zero_of_dvd hn2
      · exact hzero
    · right
      constructor
      · have hform : n = (q + 2) + (2 * q) * (n / (2 * q)) := by
          have hdiv := Nat.mod_add_div n (2 * q)
          rw [hshift] at hdiv
          exact hdiv.symm
        have hqplus : (q + 2) % 2 = 1 := by omega
        have hmul : ((2 * q) * (n / (2 * q))) % 2 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          exact ⟨q * (n / (2 * q)), by ring⟩
        rw [hform, Nat.add_mod, hqplus, hmul]
      · exact hshift
  · rintro (⟨_, hzero⟩ | ⟨_, hshift⟩)
    · exact Or.inl hzero
    · exact Or.inr hshift

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

/-- The odd prime factors in the squarefree clipped wheel. -/
def wheelOddPrimes (B : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 3 B).filter Nat.Prime

theorem q_mem_wheelOddPrimes {B q : Nat} (hq : 3 ≤ q)
    (hqB : q ≤ B) (hqPrime : Nat.Prime q) : q ∈ wheelOddPrimes B := by
  unfold wheelOddPrimes
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hq, hqB⟩, hqPrime⟩

/-- The original parity-dependent gcd input at time n and horizon C. -/
def parityWheelGcd (n C : Nat) : Nat :=
  if n % 2 = 0 then Nat.gcd n (C - 1) else Nat.gcd (n - 2) (C + 1)

/-- Distinct clipped prime factors retained when q is deleted. -/
def qFreeFactorSet (B q n C : Nat) : Finset Nat := by
  classical
  exact (wheelOddPrimes B).filter (fun p => p ≠ q ∧ p ∣ parityWheelGcd n C)

/-- The q-deleted event increment: product of the retained distinct primes. -/
def qFreeIncrement (B q n C : Nat) : Nat :=
  (qFreeFactorSet B q n C).prod id

theorem qFreeIncrement_ge_one (B q n C : Nat) :
    1 ≤ qFreeIncrement B q n C := by
  classical
  have hprod : ∀ s : Finset Nat, (∀ p ∈ s, 1 ≤ p) → 1 ≤ s.prod id := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert p s hnot ih =>
        intro hs
        rw [Finset.prod_insert hnot]
        have hp1 : 1 ≤ p := hs p (Finset.mem_insert_self p s)
        have htail : ∀ x ∈ s, 1 ≤ x := by
          intro x hx
          exact hs x (Finset.mem_insert_of_mem hx)
        have hprodTail : 1 ≤ s.prod id := ih htail
        simpa using Nat.mul_le_mul hp1 hprodTail
  unfold qFreeIncrement
  apply hprod
  intro p hp
  unfold qFreeFactorSet at hp
  have hpWheel : p ∈ wheelOddPrimes B := (Finset.mem_filter.mp hp).1
  unfold wheelOddPrimes at hpWheel
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpWheel).2
  have hp2 : 2 ≤ p := hpPrime.two_le
  omega

theorem qFreeIncrement_odd (B q n C : Nat) :
    qFreeIncrement B q n C % 2 = 1 := by
  classical
  have hprod : ∀ s : Finset Nat, (∀ p ∈ s, p % 2 = 1) → s.prod id % 2 = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert p s hnot ih =>
        intro hs
        rw [Finset.prod_insert hnot, Nat.mul_mod]
        have hpOdd := hs p (Finset.mem_insert_self p s)
        have htail : ∀ x ∈ s, x % 2 = 1 := by
          intro x hx
          exact hs x (Finset.mem_insert_of_mem hx)
        change p % 2 * (s.prod id % 2) % 2 = 1
        rw [hpOdd, ih htail]
  unfold qFreeIncrement
  apply hprod
  intro p hp
  unfold qFreeFactorSet at hp
  have hpWheel : p ∈ wheelOddPrimes B := (Finset.mem_filter.mp hp).1
  unfold wheelOddPrimes at hpWheel
  have hpMem := Finset.mem_filter.mp hpWheel
  have hpPrime : Nat.Prime p := hpMem.2
  have hpLower : 3 ≤ p := (Finset.mem_Icc.mp hpMem.1).1
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  rcases hpOdd with ⟨k, hk⟩
  omega

/-- Full-horizon q-deleted ghost horizon after processing every index ≤n.
    It starts in the tagged post-q state at `qClockSlot q j` and updates by
    d−1 at each later non-q clipped-GCD event. -/
def qGhostHorizon (B q j C : Nat) : Nat → Nat
  | 0 => C
  | n + 1 =>
      if qClockSlot q j < n + 1 then
        let previous := qGhostHorizon B q j C n
        previous + (qFreeIncrement B q (n + 1) previous - 1)
      else C

theorem qGhostHorizon_ge_two {B q j C n : Nat} (hC : 2 ≤ C) :
    2 ≤ qGhostHorizon B q j C n := by
  induction n with
  | zero => simpa [qGhostHorizon] using hC
  | succ n ih =>
      simp only [qGhostHorizon]
      split_ifs with hstart
      · have hinc := qFreeIncrement_ge_one B q (n + 1)
          (qGhostHorizon B q j C n)
        omega
      · exact hC

theorem qGhostHorizon_even {B q j C n : Nat} (hC : C % 2 = 0) :
    qGhostHorizon B q j C n % 2 = 0 := by
  induction n with
  | zero => simpa [qGhostHorizon] using hC
  | succ n ih =>
      simp only [qGhostHorizon]
      split_ifs with hstart
      · have hodd := qFreeIncrement_odd B q (n + 1)
          (qGhostHorizon B q j C n)
        have hpos := qFreeIncrement_ge_one B q (n + 1)
          (qGhostHorizon B q j C n)
        have hstep :
            (qFreeIncrement B q (n + 1) (qGhostHorizon B q j C n) - 1) % 2 = 0 := by
          omega
        rw [Nat.add_mod, ih, hstep]
      · exact hC

/-- A non-q ghost event has occurred strictly before calendar time n. -/
def qGhostHasNonQEventBefore (B q j C n : Nat) : Prop :=
  ∃ r ∈ Finset.Icc (qClockSlot q j + 1) (n - 1),
    1 < qFreeIncrement B q r (qGhostHorizon B q j C (r - 1))

/-- q-calendar times in the ghost after at least one non-q event, up to K.
    This omits the entire first post-q plateau, including its right endpoint. -/
noncomputable def qGhostPhaseTimes (B q j C K : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc (qClockSlot q j + 1) K).filter
    (fun n => qClockTime q n ∧ qGhostHasNonQEventBefore B q j C n)

/-- The pre-event ghost phase at a q-calendar time. -/
def qGhostPhaseAt (B q j C n : Nat) : Nat :=
  let previous := qGhostHorizon B q j C (n - 1)
  if n % 2 = 0 then (previous - 1) % q else (previous + 1) % q

/-- The source-selected A_q(v): distinct phases on all later ghost q-clock
    slots after the first post-q plateau has been excluded. Here `j` indexes
    the tagged q-clock and `C` is its post-q horizon; reachability of that
    state in the original recurrence is a separate premise. -/
noncomputable def qDeletedPhaseSet (B q j C K : Nat) : Finset Nat :=
  (qGhostPhaseTimes B q j C K).image (qGhostPhaseAt B q j C)

/-- Source-domain data for a slot-indexed q-deleted ghost input: q is an odd
    prime in the wheel, C is a positive even post-event horizon, and its
    residue is the one forced by a q-bearing event. This record does not
    assert reachability from an original recurrence run. -/
structure QGhostInput (B q j C : Nat) : Prop where
  qPrime : Nat.Prime q
  qOdd : q % 2 = 1
  qAtLeast11 : 11 ≤ q
  qInWheel : q ≤ B
  postHorizon_ge_two : 2 ≤ C
  postHorizon_even : C % 2 = 0
  postQ_residue :
    if qClockSlot q j % 2 = 0 then C % q = 0 else C % q = (q - 2) % q

/-- Under odd q, every retained ghost phase time is one of the source's
    parity-labelled calendar slots. -/
theorem qGhostPhaseTimes_sourceCalendar {B q j C K n : Nat}
    (hqodd : q % 2 = 1) (hn : n ∈ qGhostPhaseTimes B q j C K) :
    ((n % 2 = 0 ∧ n % (2 * q) = 0) ∨
     (n % 2 = 1 ∧ n % (2 * q) = q + 2)) := by
  classical
  unfold qGhostPhaseTimes at hn
  exact (qClockTime_iff_sourceCalendar hqodd).mp
    (Finset.mem_filter.mp hn).2.1

/-- Every q-deleted ghost phase in the cutoff window belongs to the
    previously defined finite future phase set. -/
theorem qDeletedPhaseSet_subset_futurePhaseSet {B q j C K : Nat}
    (hq : 3 ≤ q) (hcut : qClockSlot q j ≤ K) :
    qDeletedPhaseSet B q j C K ⊆
      futurePhaseSet q j K (fun i => qGhostPhaseAt B q j C (qClockSlot q (j + i + 1))) := by
  classical
  intro a ha
  unfold qDeletedPhaseSet at ha
  rcases Finset.mem_image.mp ha with ⟨n, hn, hphase⟩
  have hparts := Finset.mem_filter.mp hn
  have hinterval := Finset.mem_Icc.mp hparts.1
  have hclock := hparts.2.1
  have hafter : qClockSlot q j < n := by omega
  have hncut : n ≤ K := by omega
  obtain ⟨i, hi, hslot⟩ :=
    qClockTime_mem_futureClockIndices hq hcut hclock hafter hncut
  unfold futurePhaseSet
  apply Finset.mem_image.mpr
  refine ⟨i, hi, ?_⟩
  rw [hslot]
  exact hphase

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

/-- Pure calendar-state cardinal bound for the Lean-defined set. Source-faithful
    use requires `QGhostInput`; reachability from the original recurrence is
    a separate premise. -/
theorem qDeletedPhaseSet_calendarBound {X M K B q j C : Nat}
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ qClockSlot q j)
    (hcut : qClockSlot q j ≤ K) (hBsq : 7 * X ≤ B * B)
    (hBq : B ≤ 2 * q) (hq : 3 ≤ q) :
    7 * (qDeletedPhaseSet B q j C K).card < 6 * q := by
  exact phaseSubset_topBand_contraction hX hXM hM2X hK ht hcut
    (topBand_q_scale hBsq hBq)
    (fun i => qGhostPhaseAt B q j C (qClockSlot q (j + i + 1)))
    (qDeletedPhaseSet B q j C K)
    (qDeletedPhaseSet_subset_futurePhaseSet hq hcut)

/-- A source-valid state certificate: q lies in the odd-prime wheel, the
    q-deleted horizon stays in the valid C≥2 range, the retained phase times
    match the source calendar, and the top-band phase contraction holds.
    This is still state-level; `QGhostInput` does not prove recurrence reachability. -/
theorem qDeletedPhaseSet_topBand_certificate {X M K B q j C : Nat}
    (input : QGhostInput B q j C)
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ qClockSlot q j)
    (hcut : qClockSlot q j ≤ K) (hBsq : 7 * X ≤ B * B)
    (hBq : B ≤ 2 * q) :
    q ∈ wheelOddPrimes B ∧
      4 ≤ qClockSlot q j ∧
      (∀ n, 2 ≤ qGhostHorizon B q j C n) ∧
      (∀ n, qGhostHorizon B q j C n % 2 = 0) ∧
      (∀ n, n ∈ qGhostPhaseTimes B q j C K →
        ((n % 2 = 0 ∧ n % (2 * q) = 0) ∨
         (n % 2 = 1 ∧ n % (2 * q) = q + 2))) ∧
      (if qClockSlot q j % 2 = 0 then C % q = 0 else C % q = (q - 2) % q) ∧
      7 * (qDeletedPhaseSet B q j C K).card < 6 * q := by
  have hq2 : 2 ≤ q := input.qPrime.two_le
  have hqOdd : q % 2 = 1 := input.qOdd
  have hq3 : 3 ≤ q := by omega
  have htag4 : 4 ≤ qClockSlot q j := by omega
  refine ⟨q_mem_wheelOddPrimes hq3 input.qInWheel input.qPrime, htag4,
    ?_, ?_, ?_, input.postQ_residue, ?_⟩
  · intro n
    exact qGhostHorizon_ge_two input.postHorizon_ge_two
  · intro n
    exact qGhostHorizon_even input.postHorizon_even
  · intro n hn
    exact qGhostPhaseTimes_sourceCalendar input.qOdd hn
  · exact qDeletedPhaseSet_calendarBound hX hXM hM2X hK ht hcut hBsq hBq hq3

/-- Top-band contraction for an odd-prime in-wheel q and a valid post-q
    horizon, conditional on the slot-indexed state. Reachability of that state
    from the original recurrence remains separate. -/
theorem qDeletedPhaseSet_topBand_contraction {X M K B q j C : Nat}
    (input : QGhostInput B q j C)
    (hX : 0 < X) (hXM : X ≤ M) (hM2X : M < 2 * X)
    (hK : K = (7 * M - 1) / 4) (ht : M + 3 ≤ qClockSlot q j)
    (hcut : qClockSlot q j ≤ K) (hBsq : 7 * X ≤ B * B)
    (hBq : B ≤ 2 * q) :
    7 * (qDeletedPhaseSet B q j C K).card < 6 * q := by
  exact (qDeletedPhaseSet_topBand_certificate input hX hXM hM2X hK ht hcut hBsq hBq).2.2.2.2.2.2

#print axioms qClockSlot_is_qClock
#print axioms qClockTime_iff_slot
#print axioms qClockTime_iff_sourceCalendar
#print axioms q_mem_wheelOddPrimes
#print axioms qFreeIncrement
#print axioms qFreeIncrement_ge_one
#print axioms qFreeIncrement_odd
#print axioms qGhostHorizon
#print axioms qGhostHorizon_ge_two
#print axioms qGhostHorizon_even
#print axioms qGhostPhaseTimes
#print axioms qGhostPhaseTimes_sourceCalendar
#print axioms qGhostPhaseAt
#print axioms qDeletedPhaseSet_subset_futurePhaseSet
#print axioms qDeletedPhaseSet_calendarBound
#print axioms qDeletedPhaseSet_topBand_certificate
#print axioms qDeletedPhaseSet_topBand_contraction
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
