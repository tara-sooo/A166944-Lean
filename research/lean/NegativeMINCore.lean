import Lean.Elab.Tactic.Omega

/-! Negative MIN, exact tick semantics. Independent research lane #10.
This source is a candidate until the pinned checker accepts it.
The clock is an integer; the center is a natural number (positive even
centers in the research slab). The transition uses *all* odd prime
divisors, not a square-root cutoff or a relaxed choice of labels.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace NegativeMIN

/-- Executable primality test for the odd labels used in MIN.
The bridge to Nat.Prime is a separate Mathlib task. -/
def oddPrime (p : Nat) : Bool :=
  decide (3 ≤ p ∧ p % 2 = 1) &&
    (List.range p).all (fun d => decide (d < 2 ∨ p % d ≠ 0))

structure State where
  x : Nat
  n : Int
  deriving DecidableEq, Repr

/-- The even clock selects a factor of x+1; the odd clock a factor of x-1.
The congruence is in Z, including negative clocks. -/
def eligible (x : Nat) (n : Int) (p : Nat) : Bool :=
  oddPrime p &&
    (if n % 2 = 0 then
      decide ((x + 1) % p = 0 ∧ n % (2 * (p : Int)) = 0)
    else
      decide (x ≥ 2 ∧ (x - 1) % p = 0 ∧
        n % (2 * (p : Int)) = (p : Int) + 2))

/-- Search labels in increasing order. Zero means no eligible label.
No opaque choice or arbitrary witness is used. -/
def firstLabel (x : Nat) (n : Int) : Nat → Nat
  | 0 => 0
  | b + 1 =>
    let p := firstLabel x n b
    if p = 0 ∧ eligible x n (b + 1) = true then b + 1 else p

def winner (s : State) : Nat := firstLabel s.x (s.n + 1) (s.x + 1)

def tick (s : State) : State :=
  ⟨s.x - (winner s - 1), s.n + 1⟩

def birth (A : Nat) : State := ⟨A, 3 - (A : Int) / 2⟩

def evolve (s : State) : Nat → State
  | 0 => s
  | k + 1 => tick (evolve s k)

def orbit (A age : Nat) : State := evolve (birth A) age

/-- Twice the height; avoids truncation and rational divisions. -/
def height2 (s : State) : Int := 2 * s.n + (s.x : Int)

def gain (s t : State) : Nat := s.x - t.x

/-- An actual first non-idle tick after state s; idle prefix is explicit. -/
def FirstEvent (s : State) (w p : Nat) : Prop :=
  0 < w ∧ 0 < p ∧ winner (evolve s (w - 1)) = p ∧
    ∀ j : Nat, j + 1 < w → winner (evolve s j) = 0

theorem firstLabel_le (x : Nat) (n : Int) (b : Nat) :
    firstLabel x n b ≤ b := by
  induction b with
  | zero => simp [firstLabel]
  | succ b ih =>
    simp only [firstLabel]
    split <;> omega

theorem firstLabel_sound (x : Nat) (n : Int) (b : Nat)
    (h : firstLabel x n b ≠ 0) :
    eligible x n (firstLabel x n b) = true := by
  induction b with
  | zero => simp [firstLabel] at h
  | succ b ih =>
    by_cases hc : firstLabel x n b = 0 ∧ eligible x n (b + 1) = true
    · simpa [firstLabel, hc] using hc.2
    · have hb : firstLabel x n b ≠ 0 := by simpa [firstLabel, hc] using h
      simpa [firstLabel, hc] using ih hb

theorem firstLabel_le_of_eligible (x : Nat) (n : Int) (b q : Nat)
    (hq : 0 < q) (hb : q ≤ b) (he : eligible x n q = true) :
    0 < firstLabel x n b ∧ firstLabel x n b ≤ q := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hqb : q ≤ b
    · have h := ih hqb
      simp [firstLabel, Nat.ne_of_gt h.1, h]
    · have hqe : q = b + 1 := by omega
      subst q
      by_cases hz : firstLabel x n b = 0
      · simp [firstLabel, hz, he]
      · simp [firstLabel, hz]
        have hl := firstLabel_le x n b
        omega

theorem eligible_three_le (x : Nat) (n : Int) (p : Nat)
    (he : eligible x n p = true) : 3 ≤ p ∧ p % 2 = 1 := by
  simp only [eligible, Bool.and_eq_true, oddPrime, decide_eq_true_eq] at he
  exact he.1.1

theorem winner_le (s : State) : winner s ≤ s.x + 1 :=
  firstLabel_le s.x (s.n + 1) (s.x + 1)

theorem winner_sound (s : State) (h : winner s ≠ 0) :
    eligible s.x (s.n + 1) (winner s) = true :=
  firstLabel_sound s.x (s.n + 1) (s.x + 1) h

theorem winner_minimal (s : State) (p : Nat) (hp : 0 < p)
    (hb : p ≤ s.x + 1) (he : eligible s.x (s.n + 1) p = true) :
    0 < winner s ∧ winner s ≤ p :=
  firstLabel_le_of_eligible s.x (s.n + 1) (s.x + 1) p hp hb he

theorem tick_clock (s : State) : (tick s).n = s.n + 1 := rfl

theorem tick_center_le (s : State) : (tick s).x ≤ s.x := by
  simp [tick, Nat.sub_le]

theorem tick_gain_exact (s : State) :
    (tick s).x + (winner s - 1) = s.x := by
  have h := winner_le s
  simp only [tick]
  omega

theorem tick_even (s : State) (h : s.x % 2 = 0) :
    (tick s).x % 2 = 0 := by
  have hgain := tick_gain_exact s
  by_cases hp : winner s = 0
  · simp [tick, hp, h]
  · have ho := eligible_three_le s.x (s.n + 1) (winner s) (winner_sound s hp)
    omega

theorem evolve_clock (s : State) (k : Nat) :
    (evolve s k).n = s.n + (k : Int) := by
  induction k with
  | zero => simp [evolve]
  | succ k ih =>
    simp only [evolve, tick_clock, ih]
    omega

theorem evolve_center_le (s : State) (k : Nat) : (evolve s k).x ≤ s.x := by
  induction k with
  | zero => simp [evolve]
  | succ k ih => exact Nat.le_trans (tick_center_le _) ih

theorem evolve_even (s : State) (k : Nat) (h : s.x % 2 = 0) :
    (evolve s k).x % 2 = 0 := by
  induction k with
  | zero => exact h
  | succ k ih => exact tick_even _ ih

theorem evolve_add (s : State) (a b : Nat) :
    evolve s (a + b) = evolve (evolve s a) b := by
  induction b with
  | zero => simp [evolve]
  | succ b ih =>
    rw [Nat.add_succ, evolve, ih, evolve]

/-- Coalescence is physical-state equality, not just equal centers. -/
theorem coalescence (A B a b k : Nat)
    (h : orbit A a = orbit B b) :
    orbit A (a + k) = orbit B (b + k) := by
  simp only [orbit, evolve_add]
  exact congrArg (fun s => evolve s k) h

theorem height_gain_identity (s : State) (k : Nat) :
    height2 (evolve s k) + (gain s (evolve s k) : Int) =
      height2 s + 2 * (k : Int) := by
  have hx := evolve_center_le s k
  have hn := evolve_clock s k
  simp only [height2, gain]
  omega

theorem birth_height2 (A : Nat) (h : A % 2 = 0) : height2 (birth A) = 6 := by
  simp only [height2, birth]
  omega

/-- This uses an explicit nonnegative endpoint height, to be discharged
from the actual clock pins in the next proof layer, not assumed globally. -/
theorem gain_le_of_nonneg_height (A k : Nat) (he : A % 2 = 0)
    (hh : 0 ≤ height2 (orbit A k)) :
    (gain (birth A) (orbit A k) : Int) ≤ 6 + 2 * (k : Int) := by
  have h := height_gain_identity (birth A) k
  have hb := birth_height2 A he
  change 0 ≤ height2 (evolve (birth A) k) at hh
  rw [hb] at h
  change (gain (birth A) (evolve (birth A) k) : Int) ≤ _
  omega

/-- Latest birth and fixed common observation interval for each spatial
window. Rounding matches the research scripts, including partial last window. -/
def slabLo (R : Nat) : Nat := 6 * ((R + 5) / 6)
def windowWidth (T : Nat) : Nat := 6 * (T / 6)
def windowId (R T A : Nat) : Nat := (A - slabLo R) / windowWidth T
def observeStart (R T A : Nat) : Int :=
  3 - ((slabLo R + windowId R T A * windowWidth T : Nat) : Int) / 2
def observeAge (R T A : Nat) : Nat :=
  (observeStart R T A - (birth A).n).toNat

def roots (R : Nat) : List Nat :=
  (List.range (2 * R + 1)).filter (fun A => decide (R ≤ A ∧ A % 6 = 0))

/-- Death age is the first posttick at which a token is no longer alive.
All choices are prefixes of the actual deterministic path. -/
def liveAt (deathAge : Nat → Nat) (R T A u : Nat) : Bool :=
  decide (observeAge R T A + u < deathAge A)

def observedState (R T A u : Nat) : State :=
  orbit A (observeAge R T A + u)

def fiberAt (deathAge : Nat → Nat) (R T J x u : Nat) : List Nat :=
  (roots R).filter (fun A => liveAt deathAge R T A u &&
    decide (windowId R T A = J ∧ (observedState R T A u).x = x))

def Capped (deathAge : Nat → Nat) (R T M : Nat) : Prop :=
  ∀ J x u : Nat, u < T → (fiberAt deathAge R T J x u).length ≤ M

def life (deathAge : Nat → Nat) (R T A : Nat) : Nat :=
  min T (deathAge A - observeAge R T A)

def liveTicks (deathAge : Nat → Nat) (R T : Nat) : Nat :=
  ((roots R).map (life deathAge R T)).sum

theorem life_le (deathAge : Nat → Nat) (R T A : Nat) :
    life deathAge R T A ≤ T := Nat.min_le_left _ _

theorem liveAt_iff_lt_life (deathAge : Nat → Nat) (R T A u : Nat)
    (hu : u < T) :
    liveAt deathAge R T A u = true ↔ u < life deathAge R T A := by
  simp only [liveAt, decide_eq_true_eq, life]
  omega

theorem life_eq_full_of_survives (deathAge : Nat → Nat) (R T A : Nat)
    (h : observeAge R T A + T ≤ deathAge A) :
    life deathAge R T A = T := by
  simp only [life]
  omega

/-- Exact finite extraction: this witness is an actual live observation,
not a terminal proxy, and the arithmetic proof uses no asymptotic claim. -/
def TwinCenter (x : Nat) : Prop :=
  2 ≤ x ∧ oddPrime (x - 1) = true ∧ oddPrime (x + 1) = true

instance (x : Nat) : Decidable (TwinCenter x) := by
  unfold TwinCenter
  infer_instance

def liveNonTwinTicks (deathAge : Nat → Nat) (R T : Nat) : Nat :=
  ((roots R).map (fun A =>
    ((List.range (life deathAge R T A)).filter (fun u =>
      !(decide (TwinCenter (observedState R T A u).x)))).length)).sum

/-- No future-state or external distribution assumptions enter the count. -/
def LiveTwinAbove (deathAge : Nat → Nat) (R T B : Nat) : Prop :=
  ∃ A : Nat, A ∈ roots R ∧ ∃ u : Nat,
    u < life deathAge R T A ∧
    B < (observedState R T A u).x ∧ TwinCenter (observedState R T A u).x

/-- A finite statement of the slab location obligation. -/
def LiveAbove (deathAge : Nat → Nat) (R T B : Nat) : Prop :=
  ∀ A : Nat, A ∈ roots R → ∀ u : Nat, u < life deathAge R T A →
    B < (observedState R T A u).x

/-- Finite-gap extraction obligation. This is not a replacement for the
specific weighted asymptotic criterion; that criterion is recorded separately. -/
def LiveGapTarget : Prop :=
  ∀ B : Nat, ∃ R T M : Nat, 6 ≤ T ∧ 0 < M ∧
    ∃ deathAge : Nat → Nat, Capped deathAge R T M ∧
      LiveAbove deathAge R T B ∧
      liveNonTwinTicks deathAge R T < liveTicks deathAge R T

theorem liveNonTwin_eq_of_no_twin
    (deathAge : Nat → Nat) (R T B : Nat)
    (hAbove : LiveAbove deathAge R T B)
    (hNo : ¬ LiveTwinAbove deathAge R T B) :
    liveNonTwinTicks deathAge R T = liveTicks deathAge R T := by
  unfold liveNonTwinTicks liveTicks
  congr 1
  apply List.map_congr_left
  intro A hA
  have hfilter :
      (List.range (life deathAge R T A)).filter
        (fun u => !(decide (TwinCenter (observedState R T A u).x))) =
        List.range (life deathAge R T A) := by
    apply List.filter_eq_self.mpr
    intro u hu
    have hul : u < life deathAge R T A := List.mem_range.mp hu
    have hn : ¬ TwinCenter (observedState R T A u).x :=
      fun ht => hNo ⟨A, hA, u, hul, hAbove A hA u hul, ht⟩
    simp [hn]
  rw [hfilter, List.length_range]

theorem actual_twin_of_live_gap
    (deathAge : Nat → Nat) (R T B : Nat)
    (hAbove : LiveAbove deathAge R T B)
    (hGap : liveNonTwinTicks deathAge R T < liveTicks deathAge R T) :
    LiveTwinAbove deathAge R T B := by
  classical
  by_cases h : LiveTwinAbove deathAge R T B
  · exact h
  · have he := liveNonTwin_eq_of_no_twin deathAge R T B hAbove h
    omega

def UnboundedTwinCenters : Prop := ∀ B : Nat, ∃ x : Nat, B < x ∧ TwinCenter x

theorem unbounded_of_liveGap (h : LiveGapTarget) : UnboundedTwinCenters := by
  intro B
  obtain ⟨R, T, M, _, _, deathAge, _, hAbove, hGap⟩ := h B
  obtain ⟨A, _, u, _, hB, ht⟩ := actual_twin_of_live_gap deathAge R T B hAbove hGap
  exact ⟨(observedState R T A u).x, hB, ht⟩

/-- A pin modulo an odd label, together with evenness, implies
nonnegative postheight. The lower bound 3-p comes from one real tick.
Unlike a mere modulo-p estimate, parity excludes the spurious negative
representative 6-p in the odd-clock branch. -/
theorem nonnegative_of_height_pin (p H j c : Int)
    (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (heven : H % 2 = 0) (hc : c = 0 ∨ c = 6)
    (hfloor : 3 - p ≤ H) (hpin : H = p * j + c) : 0 ≤ H := by
  have hj : j % 2 = 0 := by
    have hmod := congrArg (fun t : Int => t % 2) hpin
    rcases hc with rfl | rfl <;>
      rw [heven, Int.add_emod, Int.mul_emod, hodd] at hmod <;> omega
  by_cases h : 0 ≤ j
  · have hm := Int.mul_nonneg (by omega : 0 ≤ p) h
    omega
  · have hle : j ≤ -2 := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hle (by omega : 0 ≤ p)
    rw [Int.mul_comm p (-2)] at hm
    omega

/-- Actual postheight pins are obtained by retaining the exact signed
clock and spatial quotient; no height invariant is assumed here. -/
theorem tick_height_pin (s : State) (hp : winner s ≠ 0) :
    ∃ j : Int, height2 (tick s) =
      (winner s : Int) * j + (if (s.n + 1) % 2 = 0 then 0 else 6) := by
  let p := winner s
  have hprime := eligible_three_le s.x (s.n + 1) p (winner_sound s hp)
  have he := winner_sound s hp
  change eligible s.x (s.n + 1) p = true at he
  simp only [eligible, Bool.and_eq_true] at he
  have hg := tick_gain_exact s
  change (tick s).x + (p - 1) = s.x at hg
  have hcoord : height2 (tick s) =
      2 * (s.n + 1) + (s.x : Int) - (p : Int) + 1 := by
    simp only [height2, tick_clock]
    omega
  let j := (s.n + 1) / (2 * (p : Int))
  have hn := Int.mul_ediv_add_emod (s.n + 1) (2 * (p : Int))
  change (2 * (p : Int)) * j + (s.n + 1) % (2 * (p : Int)) = s.n + 1 at hn
  by_cases hc : (s.n + 1) % 2 = 0
  · rw [if_pos hc] at he
    have hdiv := of_decide_eq_true he.2
    have hx := Nat.div_add_mod (s.x + 1) p
    rw [hdiv.1, Nat.add_zero] at hx
    have hx' := congrArg (fun t : Nat => (t : Int)) hx
    simp only [Int.natCast_mul, Int.natCast_add] at hx'
    rw [hdiv.2, Int.add_zero] at hn
    refine ⟨4 * j + ((s.x + 1) / p : Nat) - 1, ?_⟩
    change height2 (tick s) = (p : Int) * _ + (if (s.n + 1) % 2 = 0 then 0 else 6)
    rw [if_pos hc, hcoord]
    have h4 : 2 * ((2 * (p : Int)) * j) = (p : Int) * (4 * j) := by
      change 2 * ((2 * (p : Int)) * j) = (p : Int) * ((2 * 2) * j)
      ac_rfl
    rw [Int.mul_sub]
    simp only [Int.mul_add, Int.mul_one]
    rw [← h4]
    omega
  · rw [if_neg hc] at he
    have hdiv := of_decide_eq_true he.2
    have hx := Nat.div_add_mod (s.x - 1) p
    rw [hdiv.2.1, Nat.add_zero] at hx
    have hx' := congrArg (fun t : Nat => (t : Int)) hx
    simp only [Int.natCast_mul] at hx'
    rw [hdiv.2.2] at hn
    refine ⟨4 * j + ((s.x - 1) / p : Nat) + 1, ?_⟩
    change height2 (tick s) = (p : Int) * _ + (if (s.n + 1) % 2 = 0 then 0 else 6)
    rw [if_neg hc, hcoord]
    have h4 : 2 * ((2 * (p : Int)) * j) = (p : Int) * (4 * j) := by
      change 2 * ((2 * (p : Int)) * j) = (p : Int) * ((2 * 2) * j)
      ac_rfl
    simp only [Int.mul_add, Int.mul_one]
    rw [← h4]
    omega

theorem tick_height_nonneg (s : State) (he : s.x % 2 = 0)
    (hh : 0 ≤ height2 s) : 0 ≤ height2 (tick s) := by
  by_cases hp : winner s = 0
  · simp only [height2, tick, hp, Nat.zero_sub, Nat.sub_zero] at *
    omega
  · have hp' := eligible_three_le s.x (s.n + 1) (winner s) (winner_sound s hp)
    obtain ⟨j, hj⟩ := tick_height_pin s hp
    have he' := tick_even s he
    have hg := tick_gain_exact s
    have hn := tick_clock s
    apply nonnegative_of_height_pin (winner s : Int) (height2 (tick s)) j
      (if (s.n + 1) % 2 = 0 then 0 else 6)
    · omega
    · omega
    · unfold height2
      omega
    · split <;> simp
    · unfold height2 at hh ⊢
      omega
    · exact hj

theorem evolve_height_nonneg (s : State) (k : Nat) (he : s.x % 2 = 0)
    (hh : 0 ≤ height2 s) : 0 ≤ height2 (evolve s k) := by
  induction k with
  | zero => exact hh
  | succ k ih => exact tick_height_nonneg _ (evolve_even s k he) ih

theorem canonical_gain_bound (A k : Nat) (he : A % 2 = 0) :
    (gain (birth A) (orbit A k) : Int) ≤ 6 + 2 * (k : Int) := by
  apply gain_le_of_nonneg_height A k he
  apply evolve_height_nonneg
  · exact he
  · rw [birth_height2 A he]
    decide

/-- No non-idle event can occur in an explicitly quiet prefix. -/
theorem quiet_center (s : State) (k : Nat)
    (h : ∀ j : Nat, j < k → winner (evolve s j) = 0) :
    (evolve s k).x = s.x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : winner (evolve s k) = 0 := h k (by omega)
    have hpre : (evolve s k).x = s.x := ih (fun j hj => h j (by omega))
    simp [evolve, tick, hk, hpre]

theorem firstEvent_actual_pin (s : State) (w p : Nat)
    (h : FirstEvent s w p) :
    eligible s.x (s.n + (w : Int)) p = true := by
  obtain ⟨hw, hp, hwin, hquiet⟩ := h
  have hq := quiet_center s (w - 1) (fun j hj => hquiet j (by omega))
  have hc := evolve_clock s (w - 1)
  have hs : winner (evolve s (w - 1)) ≠ 0 := by omega
  have he := winner_sound (evolve s (w - 1)) hs
  have hclock : (evolve s (w - 1)).n + 1 = s.n + (w : Int) := by omega
  rw [hq, hclock, hwin] at he
  exact he

theorem firstEvent_gain (s : State) (w p : Nat)
    (h : FirstEvent s w p) :
    (evolve s w).x + (p - 1) = s.x := by
  obtain ⟨hw, _, hwin, hquiet⟩ := h
  have hq := quiet_center s (w - 1) (fun j hj => hquiet j (by omega))
  have hg := tick_gain_exact (evolve s (w - 1))
  rw [hwin, hq] at hg
  have hw' : w - 1 + 1 = w := by omega
  calc
    (evolve s w).x + (p - 1) = (evolve s (w - 1 + 1)).x + (p - 1) := by rw [hw']
    _ = s.x := hg

/-- The exact candidate calendar wait for either sign. A positive wait
is required even if the current tick is itself congruent to the pin. -/
def calendarWait (n : Int) (p : Nat) (plus : Bool) : Nat :=
  ((((if plus then (p : Int) + 2 else 0) - n - 1) %
    (2 * (p : Int))) + 1).toNat

theorem calendarWait_pos_le (n : Int) (p : Nat) (plus : Bool)
    (hp : 0 < p) :
    0 < calendarWait n p plus ∧ calendarWait n p plus ≤ 2 * p := by
  let r := (if plus then (p : Int) + 2 else 0) - n - 1
  have hm : 0 ≤ r % (2 * (p : Int)) :=
    Int.emod_nonneg _ (by omega)
  have hl : r % (2 * (p : Int)) < 2 * (p : Int) :=
    Int.emod_lt_of_pos _ (by omega)
  change 0 < (r % (2 * (p : Int)) + 1).toNat ∧
      (r % (2 * (p : Int)) + 1).toNat ≤ 2 * p
  omega

/-- The candidate calendar reaches its prescribed congruence, including
the negative-clock case. For p≥3 both offsets lie in [0,2p). -/
theorem calendarWait_pin (n : Int) (p : Nat) (plus : Bool)
    (hp : 3 ≤ p) :
    (n + (calendarWait n p plus : Int)) % (2 * (p : Int)) =
      (if plus then (p : Int) + 2 else 0) := by
  let t : Int := if plus then (p : Int) + 2 else 0
  let m : Int := 2 * (p : Int)
  let r := t - n - 1
  have hm : 0 ≤ r % m := Int.emod_nonneg _ (by dsimp [m]; omega)
  have h0 : 0 ≤ t := by cases plus <;> simp [t] <;> omega
  have ht : t < m := by cases plus <;> simp [t, m] <;> omega
  have hr := Int.emod_add_mul_ediv r m
  have hc : (calendarWait n p plus : Int) = r % m + 1 := by
    change ((r % m + 1).toNat : Int) = r % m + 1
    omega
  change (n + (calendarWait n p plus : Int)) % m = t
  rw [hc]
  have heq : n + (r % m + 1) = t - m * (r / m) := by
    dsimp [r] at hr ⊢
    omega
  rw [heq, Int.sub_mul_emod_self_left]
  exact Int.emod_eq_of_lt h0 ht

/-- First hit has minimum clock, and at that clock minimum prime.
This formulation compares to every eligible earlier tick without assuming
that the proposed competitor actually wins. -/
theorem firstEvent_minimum_tick (s : State) (w p v q : Nat)
    (h : FirstEvent s w p) (hv : 0 < v)
    (hq : 0 < q) (hb : q ≤ s.x + 1)
    (he : eligible s.x (s.n + (v : Int)) q = true) :
    w ≤ v := by
  by_cases hc : w ≤ v
  · exact hc
  · have hquiet := h.2.2.2
    have hqcenter := quiet_center s (v - 1) (fun j hj => hquiet j (by omega))
    have hn := evolve_clock s (v - 1)
    have hclock : (evolve s (v - 1)).n + 1 = s.n + (v : Int) := by omega
    have hbound : q ≤ (evolve s (v - 1)).x + 1 := by simpa [hqcenter] using hb
    have hel : eligible (evolve s (v - 1)).x
        ((evolve s (v - 1)).n + 1) q = true := by simpa [hqcenter, hclock] using he
    have hmin := winner_minimal (evolve s (v - 1)) q hq hbound hel
    have hz := hquiet (v - 1) (by omega)
    omega

theorem firstEvent_minimum_label (s : State) (w p q : Nat)
    (h : FirstEvent s w p) (hq : 0 < q) (hb : q ≤ s.x + 1)
    (he : eligible s.x (s.n + (w : Int)) q = true) :
    p ≤ q := by
  have hw := h.1
  have hqcenter := quiet_center s (w - 1) (fun j hj => h.2.2.2 j (by omega))
  have hn := evolve_clock s (w - 1)
  have hclock : (evolve s (w - 1)).n + 1 = s.n + (w : Int) := by omega
  have hbound : q ≤ (evolve s (w - 1)).x + 1 := by simpa [hqcenter] using hb
  have hel : eligible (evolve s (w - 1)).x
      ((evolve s (w - 1)).n + 1) q = true := by simpa [hqcenter, hclock] using he
  have hmin := winner_minimal (evolve s (w - 1)) q hq hbound hel
  rw [h.2.2.1] at hmin
  exact hmin.2

#print axioms NegativeMIN.firstEvent_minimum_tick
#print axioms NegativeMIN.firstEvent_minimum_label
#print axioms NegativeMIN.calendarWait_pin

/-- Factor eligibility before the clock is selected. -/
def SpatialFactor (x p : Nat) (plus : Bool) : Prop :=
  oddPrime p = true ∧
    (if plus then x ≥ 2 ∧ (x - 1) % p = 0 else (x + 1) % p = 0)

theorem oddPrime_bounds (p : Nat) (h : oddPrime p = true) :
    3 ≤ p ∧ p % 2 = 1 := by
  simp only [oddPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem calendarWait_eligible (s : State) (p : Nat) (plus : Bool)
    (h : SpatialFactor s.x p plus) :
    eligible s.x (s.n + (calendarWait s.n p plus : Int)) p = true := by
  have hp := oddPrime_bounds p h.1
  let t := s.n + (calendarWait s.n p plus : Int)
  let m : Int := 2 * (p : Int)
  have hpin := calendarWait_pin s.n p plus hp.1
  change t % m = _ at hpin
  have hdiv := Int.mul_ediv_add_emod t m
  rw [hpin] at hdiv
  have hm : (m * (t / m)) % 2 = 0 := by
    dsimp [m]
    rw [Int.mul_assoc, Int.mul_emod_right]
  have hpar := congrArg (fun a : Int => a % 2) hdiv
  rw [Int.add_emod, hm, Int.zero_add] at hpar
  cases plus
  · have hzero : t % 2 = 0 := by simpa using hpar.symm
    have hx : (s.x + 1) % p = 0 := h.2
    change eligible s.x t p = true
    simp [eligible, h.1, hzero, hx, hpin, m]
  · have hone : t % 2 = 1 := by
      simp only [Bool.true_eq, if_true] at hpar
      omega
    have hx : s.x ≥ 2 ∧ (s.x - 1) % p = 0 := h.2
    have hne : t % 2 ≠ 0 := by omega
    change eligible s.x t p = true
    simp [eligible, h.1, hne, hx.1, hx.2, hpin, m]

theorem firstEvent_wait_le_factor (s : State) (w p q : Nat) (plus : Bool)
    (he : FirstEvent s w p) (hf : SpatialFactor s.x q plus)
    (hq : q ≤ s.x + 1) : w ≤ 2 * q := by
  have hp := oddPrime_bounds q hf.1
  have hwait := calendarWait_pos_le s.n q plus (by omega)
  have hmin := firstEvent_minimum_tick s w p (calendarWait s.n q plus) q
    he hwait.1 (by omega) hq (calendarWait_eligible s q plus hf)
  omega

theorem firstEvent_wait_le_three_gain (s : State) (w p : Nat)
    (he : FirstEvent s w p) : w ≤ 3 * (p - 1) := by
  have hp := firstEvent_actual_pin s w p he
  have hodd := eligible_three_le s.x (s.n + (w : Int)) p hp
  have hwin := winner_le (evolve s (w - 1))
  have hcenter := quiet_center s (w - 1) (fun j hj => he.2.2.2 j (by omega))
  have hbound : p ≤ s.x + 1 := by
    rw [he.2.2.1, hcenter] at hwin
    exact hwin
  by_cases hpar : (s.n + (w : Int)) % 2 = 0
  · simp only [eligible, Bool.and_eq_true, if_pos hpar, decide_eq_true_eq] at hp
    have hf : SpatialFactor s.x p false := ⟨hp.1, hp.2.1⟩
    have h := firstEvent_wait_le_factor s w p p false he hf hbound
    omega
  · simp only [eligible, Bool.and_eq_true, if_neg hpar, decide_eq_true_eq] at hp
    have hf : SpatialFactor s.x p true := ⟨hp.1, hp.2.1, hp.2.2.1⟩
    have h := firstEvent_wait_le_factor s w p p true he hf hbound
    omega

/-- The exact synchronized window construction costs at most half a
horizon of pre-observation age, including the partial last window. -/
theorem observeAge_le_half (R T A : Nat)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0) :
    2 * observeAge R T A ≤ T := by
  let L := slabLo R
  let W := windowWidth T
  let J := (A - L) / W
  have hL : L ≤ A := by dsimp [L, slabLo]; omega
  have hW : 0 < W := by dsimp [W, windowWidth]; omega
  have hWT : W ≤ T := by dsimp [W, windowWidth]; omega
  have hrem := Nat.mod_lt (A - L) hW
  have hdiv := Nat.div_add_mod (A - L) W
  change W * J + (A - L) % W = A - L at hdiv
  rw [Nat.mul_comm W J] at hdiv
  have hbase : L + J * W ≤ A := by omega
  have hgap : A < L + J * W + W := by omega
  change 2 * ((3 - ((L + J * W : Nat) : Int) / 2) -
    (3 - (A : Int) / 2)).toNat ≤ T
  omega

theorem observed_center_lower (R T A u : Nat)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0) (hu : u < T) :
    R ≤ (observedState R T A u).x + 3 * T + 6 := by
  have ha := observeAge_le_half R T A hT hR h6
  have he : A % 2 = 0 := by omega
  have hg := canonical_gain_bound A (observeAge R T A + u) he
  have hmono := evolve_center_le (birth A) (observeAge R T A + u)
  change ((A - (observedState R T A u).x : Nat) : Int) ≤ _ at hg
  change (observedState R T A u).x ≤ A at hmono
  omega

theorem liveAbove_of_slab (deathAge : Nat → Nat) (R T B : Nat)
    (hT : 6 ≤ T) (hB : B + 3 * T + 6 < R) :
    LiveAbove deathAge R T B := by
  intro A hA u hu
  simp only [roots, List.mem_filter, decide_eq_true_eq] at hA
  have hul := life_le deathAge R T A
  have h := observed_center_lower R T A u hT hA.2.1 hA.2.2 (by omega)
  omega

#print axioms NegativeMIN.firstEvent_wait_le_three_gain
#print axioms NegativeMIN.liveAbove_of_slab

/-- The same prime test used by the transition excludes every proper
nontrivial divisor; this is later bridged to Mathlib Nat.Prime. -/
theorem oddPrime_no_small_divisor (n p : Nat)
    (hn : oddPrime n = true) (hp : 2 ≤ p) (hlt : p < n) :
    n % p ≠ 0 := by
  simp only [oddPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hn
  have h := hn.2 p (List.mem_range.mpr hlt)
  omega

theorem twin_winner_large (s : State) (ht : TwinCenter s.x)
    (hw : winner s ≠ 0) : s.x - 1 ≤ winner s := by
  have he := winner_sound s hw
  have hp := eligible_three_le s.x (s.n + 1) (winner s) he
  by_cases hlt : winner s < s.x - 1
  · exfalso
    by_cases hc : (s.n + 1) % 2 = 0
    · simp only [eligible, Bool.and_eq_true, if_pos hc, decide_eq_true_eq] at he
      exact (oddPrime_no_small_divisor (s.x + 1) (winner s) ht.2.2
        (by omega) (by omega)) he.2.1
    · simp only [eligible, Bool.and_eq_true, if_neg hc, decide_eq_true_eq] at he
      exact (oddPrime_no_small_divisor (s.x - 1) (winner s) ht.2.1
        (by omega) hlt) he.2.2.1
  · omega

/-- The actual trajectory cannot leave a visited twin center during the
square-root sized observation window. This uses the total gain budget,
not a rule that declares twins artificially absorbing. -/
theorem observedTwin_next_idle (R T A u : Nat)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0)
    (hu : u < T) (hlarge : 6 * T + 14 < R)
    (ht : TwinCenter (observedState R T A u).x) :
    winner (observedState R T A u) = 0 := by
  let s := observedState R T A u
  by_cases hw : winner s = 0
  · exact hw
  · have hl := twin_winner_large s ht hw
    have hage := observeAge_le_half R T A hT hR h6
    have hloc := observed_center_lower R T A u hT hR h6 hu
    have hgain := canonical_gain_bound A (observeAge R T A + u + 1) (by omega)
    have hx := evolve_center_le (birth A) (observeAge R T A + u)
    have hstep := tick_gain_exact s
    change R ≤ s.x + 3 * T + 6 at hloc
    change s.x ≤ A at hx
    change ((A - (tick s).x : Nat) : Int) ≤ _ at hgain
    omega

theorem observedTwin_stays (R T A u k : Nat)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0)
    (hend : u + k ≤ T) (hlarge : 6 * T + 14 < R)
    (ht : TwinCenter (observedState R T A u).x) :
    (observedState R T A (u + k)).x = (observedState R T A u).x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpre := ih (by omega)
    have htw : TwinCenter (observedState R T A (u + k)).x := by rw [hpre]; exact ht
    have hw := observedTwin_next_idle R T A (u + k) hT hR h6 (by omega) hlarge htw
    have hnext : observedState R T A (u + (k + 1)) =
        tick (observedState R T A (u + k)) := by
      unfold observedState orbit
      rw [show observeAge R T A + (u + (k + 1)) = (observeAge R T A + (u + k)) + 1 by omega]
      rfl
    rw [hnext]
    simp [tick, hw, hpre]

/-- Full physical cap, including pre-window births and stationary age
promotions. This is stronger in scope than the observation-only Capped. -/
def physicalAge (A : Nat) (n : Int) : Nat := (n - (birth A).n).toNat

def physicalLiveAt (deathAge : Nat → Nat) (R T A : Nat) (n : Int) : Bool :=
  decide ((birth A).n ≤ n ∧ n < observeStart R T A + (T : Int) ∧
    physicalAge A n < deathAge A)

def physicalFiber (deathAge : Nat → Nat) (R T J x : Nat) (n : Int) : List Nat :=
  (roots R).filter (fun A => physicalLiveAt deathAge R T A n &&
    decide (windowId R T A = J ∧ (orbit A (physicalAge A n)).x = x))

def FullCapped (deathAge : Nat → Nat) (R T M : Nat) : Prop :=
  ∀ (J x : Nat) (n : Int), (physicalFiber deathAge R T J x n).length ≤ M

/-- Exact tick-integral form of each lifetime. -/
theorem range_below_length (T l : Nat) :
    ((List.range T).filter (fun u => decide (u < l))).length = min T l := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : T < l <;> simp [h] <;> omega

theorem life_integral (deathAge : Nat → Nat) (R T A : Nat) :
    ((List.range T).filter (fun u => liveAt deathAge R T A u)).length =
      life deathAge R T A := by
  have hfilter : (List.range T).filter (fun u => liveAt deathAge R T A u) =
      (List.range T).filter (fun u => decide (u < life deathAge R T A)) := by
    apply List.filter_congr
    intro u hu
    have ht := List.mem_range.mp hu
    have h := liveAt_iff_lt_life deathAge R T A u ht
    by_cases hh : u < life deathAge R T A
    · simp [hh, h.mpr hh]
    · have hfalse : liveAt deathAge R T A u = false := by
        cases he : liveAt deathAge R T A u
        · rfl
        · exact False.elim (hh (h.mp he))
      simp [hh, hfalse]
  rw [hfilter, range_below_length]
  exact Nat.min_eq_right (life_le deathAge R T A)

/-- Prefix events include the event on whose arrival a budget death occurs;
pre-window events also count. Only observation time is truncated below. -/
def prefixAge (deathAge : Nat → Nat) (R T A : Nat) : Nat :=
  min (deathAge A) (observeAge R T A + T)

def leastOddFactor (n : Nat) : Nat :=
  ((List.range (n + 1)).find? (fun p => oddPrime p && decide (n % p = 0))).getD n

def qmin (x : Nat) : Nat := min (leastOddFactor (x - 1)) (leastOddFactor (x + 1))

def narrowCount (deathAge : Nat → Nat) (R T z Y0 : Nat) : Nat :=
  ((roots R).map (fun A =>
    ((List.range (prefixAge deathAge R T A)).filter (fun i =>
      let p := winner (orbit A i)
      decide (z < p ∧ p < Y0))).length)).sum

/-- This is the exact rough medium charge for the selected d=3/5:
q>=p^(3/5)/2 iff (2q)^5>=p^3, with no floating-point approximation. -/
def mediumCharge (deathAge : Nat → Nat) (R T Y0 Y1 : Nat) : Nat :=
  ((roots R).map (fun A =>
    ((List.range (prefixAge deathAge R T A)).map (fun i =>
      let s := orbit A i
      let p := winner s
      let q := qmin s.x
      if Y0 ≤ p ∧ p < Y1 ∧ p^3 ≤ (2*q)^5 then 2*q else 0)).sum)).sum

def twinSites (R T : Nat) : List Nat :=
  (List.range (2 * R + 1)).filter (fun x =>
    decide (R ≤ x + 3 * T + 6 ∧ TwinCenter x))

def twinCount (R T : Nat) : Nat := (twinSites R T).length

/-- Integer-scaled form of the actual paper's live-time upper estimate:
multiply eta <= B0 M twinCount/N + C E*cost + Err by D*N*T.
The coefficient wN scales C*T*exp(-L^alpha)/(k+1), wQ scales C,
and err scales Err*N*T. This predicate is an OPEN analytic obligation,
not a proved bound. No proof is hidden in its definition. -/
def ScaledLiveEstimate (deathAge : Nat → Nat) (R T M B0 z Y0 Y1 D wN wQ err : Nat) : Prop :=
  D * liveTicks deathAge R T ≤
    D * B0 * M * T * twinCount R T +
    wN * narrowCount deathAge R T z Y0 +
    wQ * mediumCharge deathAge R T Y0 Y1 + err

/-- The exact finite quantitative implication of the paper estimate,
separate from the unresolved estimate and survival bound. -/
theorem scaled_twin_count_lower (deathAge : Nat → Nat)
    (R T M B0 z Y0 Y1 D wN wQ err : Nat)
    (h : ScaledLiveEstimate deathAge R T M B0 z Y0 Y1 D wN wQ err) :
    D * liveTicks deathAge R T -
      (wN * narrowCount deathAge R T z Y0 +
        wQ * mediumCharge deathAge R T Y0 Y1 + err)
      ≤ D * B0 * M * T * twinCount R T := by
  unfold ScaledLiveEstimate at h
  omega

theorem twin_above_of_scaled_live_estimate (deathAge : Nat → Nat)
    (R T M B0 z Y0 Y1 D wN wQ err B : Nat)
    (hlarge : B + 3*T + 6 < R)
    (h : ScaledLiveEstimate deathAge R T M B0 z Y0 Y1 D wN wQ err)
    (hgap : wN * narrowCount deathAge R T z Y0 +
        wQ * mediumCharge deathAge R T Y0 Y1 + err <
        D * liveTicks deathAge R T) :
    ∃ x : Nat, B < x ∧ TwinCenter x := by
  have hc : 0 < twinCount R T := by
    by_cases hz : twinCount R T = 0
    · unfold ScaledLiveEstimate at h
      rw [hz, Nat.mul_zero, Nat.zero_add] at h
      omega
    · omega
  unfold twinCount at hc
  generalize hl : twinSites R T = xs at hc
  cases xs with
  | nil => simp at hc
  | cons x xs =>
    have hm : x ∈ twinSites R T := by rw [hl]; simp
    simp only [twinSites, List.mem_filter, decide_eq_true_eq] at hm
    have hloc := hm.2.1
    exact ⟨x, by omega, hm.2.2⟩

/-- Repeated finite weighted certificates imply unbounded actual twin
centers. The hypotheses are the explicit scaled analytical estimate and
strict survival surplus; neither is asserted to be automatic. -/
theorem unbounded_of_scaled_live_family
    (h : ∀ B : Nat, ∃ (R T M B0 z Y0 Y1 D wN wQ err : Nat) (deathAge : Nat → Nat),
      B + 3*T + 6 < R ∧ 6 ≤ T ∧ 0 < M ∧ FullCapped deathAge R T M ∧
      ScaledLiveEstimate deathAge R T M B0 z Y0 Y1 D wN wQ err ∧
      wN * narrowCount deathAge R T z Y0 +
        wQ * mediumCharge deathAge R T Y0 Y1 + err < D * liveTicks deathAge R T) :
    UnboundedTwinCenters := by
  intro B
  obtain ⟨R, T, M, B0, z, Y0, Y1, D, wN, wQ, err, deathAge,
    hlarge, _, _, _, hest, hgap⟩ := h B
  exact twin_above_of_scaled_live_estimate deathAge R T M B0 z Y0 Y1 D wN wQ err B
    hlarge hest hgap

/-! Finite, independently generated controls. These are kernel-reduced
specific examples, not evidence for a universal asymptotic theorem. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
example : orbit 36 5 = ⟨30, -10⟩ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
example : orbit 54 20 = ⟨30, -4⟩ := by decide

set_option maxRecDepth 10000 in
example : eligible 62 0 7 = true ∧ winner ⟨62, -1⟩ = 3 := by decide

/-- Refutes coalescence based only on center, on actual canonical histories.
Both times are from the same canonical root A=6. -/
theorem center_only_coalescence_false :
    (orbit 6 1).x = (orbit 6 6).x ∧
    (orbit 6 2).x ≠ (orbit 6 7).x := by decide

#print axioms NegativeMIN.unbounded_of_scaled_live_family
#print axioms NegativeMIN.center_only_coalescence_false

#print axioms NegativeMIN.observedTwin_stays
#print axioms NegativeMIN.life_integral
#print axioms NegativeMIN.scaled_twin_count_lower
#print axioms NegativeMIN.twin_above_of_scaled_live_estimate

#print axioms NegativeMIN.actual_twin_of_live_gap
#print axioms NegativeMIN.unbounded_of_liveGap
#print axioms NegativeMIN.canonical_gain_bound
#print axioms NegativeMIN.winner_minimal
#print axioms NegativeMIN.coalescence
#print axioms NegativeMIN.height_gain_identity
#print axioms NegativeMIN.liveAt_iff_lt_life

/-! Fixed-cohort rank selection and integrated collision charging.
A cohort is selected once, before the policy begins (it may be chosen by
a deterministic lookahead). This does not alter any underlying orbit. -/

def physicalState (A : Nat) (n : Int) : State :=
  orbit A (physicalAge A n)

theorem physicalState_clock (A : Nat) (n : Int) (hb : (birth A).n ≤ n) :
    (physicalState A n).n = n := by
  unfold physicalState orbit physicalAge
  rw [evolve_clock]
  omega

theorem physicalState_advance (A : Nat) (n : Int) (k : Nat)
    (hb : (birth A).n ≤ n) :
    physicalState A (n + (k : Int)) = evolve (physicalState A n) k := by
  have ha : physicalAge A (n + (k : Int)) = physicalAge A n + k := by
    unfold physicalAge
    omega
  simp only [physicalState, ha, orbit, evolve_add]

def Contact (R T A B : Nat) (n : Int) : Prop :=
  (birth A).n ≤ n ∧ (birth B).n ≤ n ∧
    windowId R T A = windowId R T B ∧ physicalState A n = physicalState B n

instance (R T A B : Nat) (n : Int) : Decidable (Contact R T A B n) := by
  unfold Contact
  infer_instance

theorem contact_mono (R T A B : Nat) (n m : Int) (hn : n ≤ m)
    (h : Contact R T A B n) : Contact R T A B m := by
  obtain ⟨ha, hb, hj, hs⟩ := h
  have hk : n + ((m-n).toNat : Int) = m := by omega
  refine ⟨by omega, by omega, hj, ?_⟩
  rw [← hk, physicalState_advance A n _ ha, physicalState_advance B n _ hb, hs]

theorem contact_of_center (R T A B : Nat) (n : Int)
    (ha : (birth A).n ≤ n) (hb : (birth B).n ≤ n)
    (hj : windowId R T A = windowId R T B)
    (hx : (physicalState A n).x = (physicalState B n).x) :
    Contact R T A B n := by
  refine ⟨ha, hb, hj, ?_⟩
  have hn := physicalState_clock A n ha
  have hm := physicalState_clock B n hb
  cases hA : physicalState A n
  cases hB : physicalState B n
  simp only [hA, hB] at hx hn hm ⊢
  congr <;> omega

/-- A useful finite counting lemma, with no duplicate-free hypothesis. -/
theorem filter_len_mono {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ a ∈ xs, f a = true → g a = true) :
    (xs.filter f).length ≤ (xs.filter g).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hi := ih (fun b hb => h b (by simp [hb]))
    by_cases hf : f a = true
    · have hg := h a (by simp) hf
      simp [hf, hg, hi]
    · by_cases hg : g a = true <;> simp [hf, hg] <;> omega

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ a ∈ xs, f a ≤ g a) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hi := ih (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun a => f a + g a)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul {α : Type} (xs : List α) (c : Nat) (f : α → Nat) :
    (xs.map (fun a => c * f a)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.mul_add]

theorem filter_length_indicator {α : Type} (xs : List α) (f : α → Bool) :
    (xs.filter f).length = (xs.map (fun a => if f a then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h : f a <;> simp [h, ih, Nat.add_comm]

theorem sum_map_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum =
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons b ys ih => simpa only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add] using ih
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← sum_map_add]

/-- Counting a Boolean initial interval: no search oracle or choice. -/
theorem antitone_count_spec (f : Nat → Bool)
    (hf : ∀ i j : Nat, i ≤ j → f j = true → f i = true)
    (H i : Nat) :
    i < ((List.range H).filter f).length ↔ i < H ∧ f i = true := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases h : f H = true
    · have he : (List.range H).filter f = List.range H := by
        apply List.filter_eq_self.mpr
        intro j hj
        exact hf j H (by have := List.mem_range.mp hj; omega) h
      rw [he]
      simp only [List.length_range, List.filter_cons, h, if_true, List.filter_nil,
        List.length_cons, List.length_nil]
      constructor
      · intro hi
        exact ⟨by omega, hf i H (by omega) h⟩
      · intro hi
        omega
    · have hfalse : f H = false := by cases h' : f H <;> simp_all
      simp only [List.filter_cons, hfalse, Bool.false_eq_true, if_false,
        List.filter_nil, List.length_nil, Nat.add_zero]
      rw [ih]
      constructor
      · intro hi
        exact ⟨by omega, hi.2⟩
      · intro hi
        have hiH : i ≠ H := fun e => h (e ▸ hi.2)
        exact ⟨by omega, hi.2⟩

/-- Strictly smaller root IDs are higher-priority. Rank includes self. -/
def cohort (R : Nat) (select : Nat → Bool) : List Nat :=
  (roots R).filter select

def rankList (R T A : Nat) (select : Nat → Bool) (n : Int) : List Nat :=
  (roots R).filter (fun B => select B && decide (B ≤ A ∧ Contact R T A B n))

def rank (R T A : Nat) (select : Nat → Bool) (n : Int) : Nat :=
  (rankList R T A select n).length

theorem rank_mono (R T A : Nat) (select : Nat → Bool) (n m : Int)
    (h : n ≤ m) : rank R T A select n ≤ rank R T A select m := by
  unfold rank rankList
  apply filter_len_mono
  intro B _ hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
  exact ⟨hb.1, hb.2.1, contact_mono R T A B n m h hb.2.2⟩

def rankOK (R T M A : Nat) (select : Nat → Bool) (i : Nat) : Bool :=
  decide (rank R T A select ((birth A).n + (i : Int)) ≤ M)

theorem rankOK_antitone (R T M A : Nat) (select : Nat → Bool)
    (i j : Nat) (h : i ≤ j) (hj : rankOK R T M A select j = true) :
    rankOK R T M A select i = true := by
  simp only [rankOK, decide_eq_true_eq] at hj ⊢
  exact Nat.le_trans (rank_mono R T A select _ _ (by omega)) hj

def rankDeath (R T M : Nat) (select : Nat → Bool) (A : Nat) : Nat :=
  if select A then
    ((List.range (observeAge R T A + T)).filter (rankOK R T M A select)).length
  else 0

theorem rankDeath_spec (R T M A i : Nat) (select : Nat → Bool) :
    i < rankDeath R T M select A ↔
      select A = true ∧ i < observeAge R T A + T ∧
        rank R T A select ((birth A).n + (i : Int)) ≤ M := by
  by_cases h : select A = true
  · simp only [rankDeath, h, if_true, true_and]
    rw [antitone_count_spec _ (rankOK_antitone R T M A select)]
    simp [rankOK]
  · have hf : select A = false := by cases he : select A <;> simp_all
    simp [rankDeath, hf]

theorem list_max_mem (xs : List Nat) (h : xs ≠ []) :
    ∃ a ∈ xs, ∀ b ∈ xs, b ≤ a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases he : xs = []
    · subst xs
      exact ⟨x, by simp, by simp⟩
    · obtain ⟨a, ha, hmax⟩ := ih he
      by_cases hx : x ≤ a
      · refine ⟨a, by simp [ha], ?_⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hx
        · exact hmax b hb
      · refine ⟨x, by simp, ?_⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Nat.le_refl _
        · have := hmax b hb
          omega

/-- This is a real irreversible capped policy, not a cap on a relaxed
terminal map. All times, including pre-window births, are covered. -/
theorem rankDeath_fullCapped (R T M : Nat) (select : Nat → Bool) :
    FullCapped (rankDeath R T M select) R T M := by
  intro J x n
  let f := fun A => physicalLiveAt (rankDeath R T M select) R T A n &&
    decide (windowId R T A = J ∧ (orbit A (physicalAge A n)).x = x)
  change ((roots R).filter f).length ≤ M
  by_cases he : (roots R).filter f = []
  · simp [he]
  · obtain ⟨A, hA, hmax⟩ := list_max_mem ((roots R).filter f) he
    have ha := (List.mem_filter.mp hA).2
    dsimp [f] at ha
    simp only [Bool.and_eq_true, physicalLiveAt, decide_eq_true_eq] at ha
    have hbirth := ha.1.1
    have hspec := (rankDeath_spec R T M A (physicalAge A n) select).mp ha.1.2.2
    have hclock : (birth A).n + (physicalAge A n : Int) = n := by
      unfold physicalAge
      omega
    rw [hclock] at hspec
    apply Nat.le_trans (filter_len_mono (roots R) f
      (fun B => select B && decide (B ≤ A ∧ Contact R T A B n)) ?_) hspec.2.2
    intro B hB hf
    have hm : B ∈ (roots R).filter f := List.mem_filter.mpr ⟨hB, hf⟩
    have hle := hmax B hm
    dsimp [f] at hf
    simp only [Bool.and_eq_true, physicalLiveAt, decide_eq_true_eq] at hf
    have hs := (rankDeath_spec R T M B (physicalAge B n) select).mp hf.1.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hs.1, hle, ?_⟩
    apply contact_of_center R T A B n hbirth hf.1.1 (ha.2.1.trans hf.2.1.symm)
    exact ha.2.2.trans hf.2.2.symm

/-- Observation clock: all canonical births in the window have happened. -/
theorem observeStart_ge_birth (R T A : Nat) (hT : 6 ≤ T)
    (hR : R ≤ A) (h6 : A % 6 = 0) : (birth A).n ≤ observeStart R T A := by
  let L := slabLo R
  let W := windowWidth T
  let J := (A-L)/W
  have hL : L ≤ A := by dsimp [L, slabLo]; omega
  have hd := Nat.div_add_mod (A-L) W
  change W*J+(A-L)%W = A-L at hd
  rw [Nat.mul_comm W J] at hd
  have hbase : L+J*W ≤ A := by omega
  change 3-(A : Int)/2 ≤ 3-((L+J*W : Nat) : Int)/2
  omega

theorem rankDeath_observed_iff (R T M A u : Nat) (select : Nat → Bool)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0) (hu : u < T) :
    liveAt (rankDeath R T M select) R T A u = true ↔
      select A = true ∧ rank R T A select (observeStart R T A + (u : Int)) ≤ M := by
  have hb := observeStart_ge_birth R T A hT hR h6
  have hc : (birth A).n + ((observeAge R T A + u : Nat) : Int) =
      observeStart R T A + (u : Int) := by
    unfold observeAge
    omega
  simp only [liveAt, decide_eq_true_eq, rankDeath_spec, hc]
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · intro h
    exact ⟨h.1, by omega, h.2⟩

/-- Count distinct, higher-priority contacts, not the diagonal. -/
def strictRank (R T A : Nat) (select : Nat → Bool) (n : Int) : Nat :=
  ((roots R).filter (fun B => select B && decide (B < A ∧ Contact R T A B n))).length

theorem rank_le_strict_add_one_list (xs : List Nat) (A : Nat) (f : Nat → Bool)
    (hn : xs.Nodup) :
    (xs.filter (fun B => f B && decide (B ≤ A))).length ≤
      (xs.filter (fun B => f B && decide (B < A))).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : x = A
    · subst x
      have eqf : xs.filter (fun B => f B && decide (B ≤ A)) =
          xs.filter (fun B => f B && decide (B < A)) := by
        apply List.filter_congr
        intro b hb
        have hne : b ≠ A := fun e => hn'.1 (e ▸ hb)
        by_cases hlt : b < A
        · simp [hlt, Nat.le_of_lt hlt]
        · have hle : ¬ b ≤ A := by omega
          simp [hlt, hle]
      rw [List.filter_cons, List.filter_cons, eqf]
      cases h : f A <;> simp [h]
    · have hi := ih hn'.2
      by_cases hlt : x < A
      · have hle := Nat.le_of_lt hlt
        cases h : f x <;> simp [List.filter_cons, hlt, hle, h] <;> omega
      · have hle : ¬ x ≤ A := by omega
        simp [List.filter_cons, hlt, hle, hi]

theorem rank_le_strict_add_one (R T A : Nat) (select : Nat → Bool) (n : Int) :
    rank R T A select n ≤ strictRank R T A select n + 1 := by
  have hnd : (roots R).Nodup := by
    unfold roots
    exact (List.filter_sublist (p := fun A => decide (R ≤ A ∧ A % 6 = 0))).nodup
      List.nodup_range
  have h := rank_le_strict_add_one_list (roots R) A
    (fun B => select B && decide (Contact R T A B n)) hnd
  have h1 : rankList R T A select n =
      (roots R).filter (fun B => (select B && decide (Contact R T A B n)) && decide (B ≤ A)) := by
    unfold rankList
    apply List.filter_congr
    intro B _
    by_cases hb : B ≤ A <;> by_cases hc : Contact R T A B n <;> simp [hb, hc]
  have h2 : (roots R).filter (fun B => select B && decide (B < A ∧ Contact R T A B n)) =
      (roots R).filter (fun B => (select B && decide (Contact R T A B n)) && decide (B < A)) := by
    apply List.filter_congr
    intro B _
    by_cases hb : B < A <;> by_cases hc : Contact R T A B n <;> simp [hb, hc]
  simpa only [rank, strictRank, h1, h2] using h

/-- Every lost selected root-tick is charged to at least M distinct
higher-priority full-cohort contacts at that tick. No discarded token
needs to be reactivated. -/
theorem rankDeath_pointwise_loss (R T M A u : Nat) (select : Nat → Bool)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0) (hu : u < T)
    (hs : select A = true) :
    M * (if liveAt (rankDeath R T M select) R T A u then 0 else 1) ≤
      strictRank R T A select (observeStart R T A + (u : Int)) := by
  by_cases h : liveAt (rankDeath R T M select) R T A u = true
  · simp [h]
  · have hn : ¬ rank R T A select (observeStart R T A + (u : Int)) ≤ M :=
      fun hr => h ((rankDeath_observed_iff R T M A u select hT hR h6 hu).mpr ⟨hs, hr⟩)
    have hr := rank_le_strict_add_one R T A select (observeStart R T A + (u : Int))
    have hf : liveAt (rankDeath R T M select) R T A u = false := by
      cases he : liveAt (rankDeath R T M select) R T A u <;> simp_all
    simp [hf]
    omega

/-- First-contact weight in integer ticks. The contact predicate is
monotone, so this is exactly T minus the clipped first contact offset. -/
def contactTicks (R T A B : Nat) : Nat :=
  ((List.range T).filter
    (fun u : Nat => decide (Contact R T A B (observeStart R T A + (u : Int))))).length

def firstContactOffset (R T A B : Nat) : Nat :=
  ((List.range T).filter
    (fun u : Nat => !decide (Contact R T A B (observeStart R T A + (u : Int))))).length

theorem firstContact_spec (R T A B u : Nat) (hu : u < T) :
    firstContactOffset R T A B ≤ u ↔
      Contact R T A B (observeStart R T A + (u : Int)) := by
  have hant : ∀ i j : Nat, i ≤ j →
      (!decide (Contact R T A B (observeStart R T A + (j : Int)))) = true →
      (!decide (Contact R T A B (observeStart R T A + (i : Int)))) = true := by
    intro i j hij hj
    by_cases hi : Contact R T A B (observeStart R T A + (i : Int))
    · have h := contact_mono R T A B (observeStart R T A + (i : Int)) (observeStart R T A + (j : Int)) (by omega) hi
      simp [h] at hj
    · simp [hi]
  have h := antitone_count_spec _ hant T u
  change u < firstContactOffset R T A B ↔ _ at h
  by_cases hc : Contact R T A B (observeStart R T A + (u : Int))
  · simp [hc] at h ⊢
    omega
  · simp [hc, hu] at h ⊢
    omega

theorem filter_complement_length {α : Type} (xs : List α) (f : α → Bool) :
    (xs.filter f).length + (xs.filter (fun a => !f a)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : f a <;> simp [List.filter_cons, h] <;> omega

theorem contactTicks_add_offset (R T A B : Nat) :
    contactTicks R T A B + firstContactOffset R T A B = T := by
  unfold contactTicks firstContactOffset
  rw [filter_complement_length, List.length_range]

#print axioms NegativeMIN.rankDeath_fullCapped
#print axioms NegativeMIN.rankDeath_pointwise_loss
#print axioms NegativeMIN.firstContact_spec
#print axioms NegativeMIN.contactTicks_add_offset

/-- Total pair weight over the fixed selected cohort, each unordered
pair counted once by its larger root ID. -/
def pairWeight (R T : Nat) (select : Nat → Bool) : Nat :=
  ((cohort R select).map (fun A =>
    ((cohort R select).map (fun B =>
      if B < A then contactTicks R T A B else 0)).sum)).sum

theorem strictRank_sum (R T A : Nat) (select : Nat → Bool) (n : Int) :
    strictRank R T A select n =
      ((cohort R select).map (fun B => if B < A ∧ Contact R T A B n then 1 else 0)).sum := by
  calc
    strictRank R T A select n =
        ((cohort R select).filter (fun B => decide (B < A ∧ Contact R T A B n))).length := by
      unfold strictRank cohort
      rw [List.filter_filter]
      apply congrArg List.length
      apply List.filter_congr
      intro B _
      by_cases hs : select B = true <;> by_cases h : B < A ∧ Contact R T A B n <;> simp [hs, h]
    _ = _ := by rw [filter_length_indicator]; simp only [decide_eq_true_eq]

theorem strictRank_integral (R T A : Nat) (select : Nat → Bool) :
    ((List.range T).map (fun u : Nat =>
      strictRank R T A select (observeStart R T A + (u : Int)))).sum =
      ((cohort R select).map (fun B =>
        if B < A then contactTicks R T A B else 0)).sum := by
  have h : ((List.range T).map (fun u : Nat =>
      strictRank R T A select (observeStart R T A + (u : Int)))).sum =
      ((List.range T).map (fun u : Nat => ((cohort R select).map
        (fun B => if B < A ∧ Contact R T A B (observeStart R T A + (u : Int))
          then 1 else 0)).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro u _
    exact strictRank_sum R T A select _
  rw [h, sum_map_swap]
  congr 1
  apply List.map_congr_left
  intro B _
  by_cases hb : B < A
  · simp only [hb, true_and, if_true, contactTicks]
    rw [filter_length_indicator]
    congr 1
    apply List.map_congr_left
    intro u _
    by_cases hc : Contact R T A B (observeStart R T A + (u : Int)) <;> simp [hc]
  · simp only [hb, false_and, if_false]
    generalize List.range T = xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons, List.sum_cons, Nat.zero_add, ih]

/-- Integrated first-contact inequality for a single selected root. -/
theorem rankDeath_root_loss (R T M A : Nat) (select : Nat → Bool)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0) (hs : select A = true) :
    M * (T - life (rankDeath R T M select) R T A) ≤
      ((cohort R select).map (fun B => if B < A then contactTicks R T A B else 0)).sum := by
  let f := fun u : Nat => liveAt (rankDeath R T M select) R T A u
  have hcount := life_integral (rankDeath R T M select) R T A
  change ((List.range T).filter f).length = _ at hcount
  have hcompl := filter_complement_length (List.range T) f
  rw [List.length_range, hcount] at hcompl
  have heq : T - life (rankDeath R T M select) R T A =
      ((List.range T).map (fun u => if f u then 0 else 1)).sum := by
    have hsub : T - life (rankDeath R T M select) R T A = ((List.range T).filter (fun a => !f a)).length := by omega
    rw [hsub, filter_length_indicator]
    congr 1
    apply List.map_congr_left
    intro u _
    cases h : f u <;> simp [h]
  rw [heq, ← sum_map_mul, ← strictRank_integral]
  apply sum_map_le
  intro u hu
  exact rankDeath_pointwise_loss R T M A u select hT hR h6 (List.mem_range.mp hu) hs

def cohortLiveTicks (R T M : Nat) (select : Nat → Bool) : Nat :=
  ((cohort R select).map (life (rankDeath R T M select) R T)).sum

theorem cohortLive_eq_live (R T M : Nat) (select : Nat → Bool) :
    cohortLiveTicks R T M select = liveTicks (rankDeath R T M select) R T := by
  unfold cohortLiveTicks cohort liveTicks
  generalize (roots R) = xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : select a
    · have hz : life (rankDeath R T M select) R T a = 0 := by simp [life, rankDeath, h]
      simp [List.filter_cons, h, hz, ih]
    · simp [List.filter_cons, h, ih]

theorem cohort_loss_identity (R T M : Nat) (select : Nat → Bool) :
    cohortLiveTicks R T M select +
      ((cohort R select).map (fun A => T - life (rankDeath R T M select) R T A)).sum =
        (cohort R select).length * T := by
  unfold cohortLiveTicks
  rw [← sum_map_add]
  generalize cohort R select = xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := life_le (rankDeath R T M select) R T a
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul, ← ih]
    omega

/-- Exact finite survival lower bound using weighted first contacts.
It is an unconditional inequality for any fixed cohort of actual roots. -/
theorem rankDeath_integrated_loss (R T M : Nat) (select : Nat → Bool)
    (hT : 6 ≤ T) :
    M * ((cohort R select).length * T -
      liveTicks (rankDeath R T M select) R T) ≤ pairWeight R T select := by
  have heq := cohort_loss_identity R T M select
  rw [cohortLive_eq_live] at heq
  have hsub : (cohort R select).length * T -
      liveTicks (rankDeath R T M select) R T =
      ((cohort R select).map (fun A => T - life (rankDeath R T M select) R T A)).sum := by omega
  rw [hsub, ← sum_map_mul]
  unfold pairWeight
  apply sum_map_le
  intro A hA
  simp only [cohort, roots, List.mem_filter, decide_eq_true_eq] at hA
  exact rankDeath_root_loss R T M A select hT hA.1.2.1 hA.1.2.2 hA.2

#print axioms NegativeMIN.rankDeath_integrated_loss

/-! Additive cost priority, and exact optimal simultaneous retention.
The finite counting result below uses no probabilistic distribution model. -/

def Precedes (score : Nat → Nat) (a b : Nat) : Prop :=
  score a < score b ∨ (score a = score b ∧ a ≤ b)

instance (score : Nat → Nat) (a b : Nat) : Decidable (Precedes score a b) := by
  unfold Precedes
  infer_instance

theorem precedes_total (score : Nat → Nat) (a b : Nat) :
    Precedes score a b ∨ Precedes score b a := by
  unfold Precedes
  omega

theorem precedes_trans (score : Nat → Nat) (a b c : Nat)
    (hab : Precedes score a b) (hbc : Precedes score b c) :
    Precedes score a c := by
  unfold Precedes at *
  omega

theorem precedes_antisymm (score : Nat → Nat) (a b : Nat)
    (hab : Precedes score a b) (hba : Precedes score b a) : a = b := by
  unfold Precedes at *
  omega

theorem extreme_mem (xs : List Nat) (rel : Nat → Nat → Prop)
    (htotal : ∀ a b, rel a b ∨ rel b a)
    (htrans : ∀ a b c, rel a b → rel b c → rel a c) (hne : xs ≠ []) :
    ∃ a ∈ xs, ∀ b ∈ xs, rel b a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases he : xs = []
    · subst xs
      refine ⟨x, by simp, ?_⟩
      intro b hb
      have he : b = x := by simpa using hb
      subst b
      exact (htotal x x).elim id id
    · obtain ⟨a, ha, hmax⟩ := ih he
      rcases htotal x a with hx | hx
      · refine ⟨a, by simp [ha], ?_⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hx
        · exact hmax b hb
      · refine ⟨x, by simp, ?_⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact (htotal b b).elim id id
        · exact htrans b a x (hmax b hb) hx

theorem filter_len_exception {α : Type} [DecidableEq α] (xs : List α)
    (f g : α → Bool) (a : α) (hn : xs.Nodup)
    (h : ∀ b ∈ xs, f b = true → b ≠ a → g b = true) :
    (xs.filter f).length ≤ (xs.filter g).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp hn
    by_cases he : x = a
    · subst x
      have hsub := filter_len_mono xs f g (fun b hb hf =>
        h b (by simp [hb]) hf (fun he => hnd.1 (he ▸ hb)))
      cases hf : f a <;> cases hg : g a <;> simp [hf, hg] <;> omega
    · have hs := ih hnd.2 (fun b hb => h b (by simp [hb]))
      by_cases hf : f x = true
      · have hg := h x (by simp) hf he
        simp [hf, hg]
        omega
      · cases hg : g x <;> simp [hf, hg] <;> omega

def localRank (xs : List Nat) (score : Nat → Nat) (a : Nat) : Nat :=
  (xs.filter (fun b => decide (Precedes score b a))).length

def rankClip (xs : List Nat) (score : Nat → Nat) (M : Nat) : List Nat :=
  xs.filter (fun a => decide (localRank xs score a ≤ M))

/-- Every rank from 1 through the fiber size is represented, expressed
as an exact cardinality of a clipped list. -/
theorem rankClip_length (xs : List Nat) (score : Nat → Nat) (M : Nat)
    (hn : xs.Nodup) : (rankClip xs score M).length = min M xs.length := by
  let good := rankClip xs score M
  have hsize : good.length ≤ xs.length := List.length_filter_le _ _
  have hcap : good.length ≤ M := by
    by_cases hz : good = []
    · simp [hz]
    · obtain ⟨a, ha, hmax⟩ := extreme_mem good (Precedes score)
        (precedes_total score) (precedes_trans score) hz
      have har : localRank xs score a ≤ M := by
        have hh := (List.mem_filter.mp ha).2
        simpa using hh
      apply Nat.le_trans (filter_len_mono xs _ _ ?_) har
      intro b hb hgb
      have hp := hmax b (List.mem_filter.mpr ⟨hb, hgb⟩)
      simpa using hp
  have hupper : good.length ≤ min M xs.length := Nat.le_min.mpr ⟨hcap, hsize⟩
  apply Nat.le_antisymm hupper
  by_cases hall : ∀ a ∈ xs, localRank xs score a ≤ M
  · have he : good = xs := by
      unfold good rankClip
      apply List.filter_eq_self.mpr
      intro a ha
      simpa using hall a ha
    rw [he]
    exact Nat.min_le_right _ _
  · let bad := xs.filter (fun a => decide (M < localRank xs score a))
    have hbad : bad ≠ [] := by
      intro hz
      apply hall
      intro a ha
      have h := List.filter_eq_nil_iff.mp hz a ha
      simp only [decide_eq_true_eq] at h
      omega
    obtain ⟨a, ha, hmin⟩ := extreme_mem bad (fun a b => Precedes score b a)
      (fun a b => precedes_total score b a)
      (fun a b c h1 h2 => precedes_trans score c b a h2 h1) hbad
    have har : M < localRank xs score a := by
      have hh := (List.mem_filter.mp ha).2
      simpa using hh
    have hsub := filter_len_exception xs (fun b => decide (Precedes score b a))
      (fun b => decide (localRank xs score b ≤ M)) a hn (by
        intro b hb hp hne
        have hp' : Precedes score b a := by simpa using hp
        by_cases hr : localRank xs score b ≤ M
        · simpa using hr
        · have hb' : b ∈ bad := by
            apply List.mem_filter.mpr
            exact ⟨hb, by simp; omega⟩
          exact False.elim (hne (precedes_antisymm score b a hp' (hmin b hb'))))
    change localRank xs score a ≤ good.length + 1 at hsub
    omega

/-- Additive nonnegative cost of the actual completed ticks.
A zero cost may be assigned to an idle tick. -/
def pathCost (inc : State → Nat) (s : State) : Nat → Nat
  | 0 => 0
  | k+1 => pathCost inc s k + inc (evolve s k)

theorem pathCost_add (inc : State → Nat) (s : State) (a b : Nat) :
    pathCost inc s (a+b) = pathCost inc s a + pathCost inc (evolve s a) b := by
  induction b with
  | zero => simp [pathCost]
  | succ b ih =>
    change pathCost inc s (a+b) + inc (evolve s (a+b)) =
      pathCost inc s a + (pathCost inc (evolve s a) b + inc (evolve (evolve s a) b))
    rw [ih, evolve_add]
    omega

theorem pathCost_mono (inc : State → Nat) (s : State) (a b : Nat) (h : a ≤ b) :
    pathCost inc s a ≤ pathCost inc s b := by
  have he : a + (b-a) = b := by omega
  have hc := pathCost_add inc s a (b-a)
  rw [he] at hc
  omega

def physicalCost (inc : State → Nat) (A : Nat) (n : Int) : Nat :=
  pathCost inc (birth A) (physicalAge A n)

theorem physicalCost_advance (inc : State → Nat) (A : Nat) (n : Int) (k : Nat)
    (hb : (birth A).n ≤ n) :
    physicalCost inc A (n+(k : Int)) =
      physicalCost inc A n + pathCost inc (physicalState A n) k := by
  have ha : physicalAge A (n+(k : Int)) = physicalAge A n + k := by
    unfold physicalAge
    omega
  simp only [physicalCost, ha, pathCost_add, physicalState, orbit]

theorem contact_priority_mono (inc : State → Nat) (R T A B : Nat) (n m : Int)
    (hn : n ≤ m) (hc : Contact R T A B n)
    (hp : Precedes (fun a => physicalCost inc a n) B A) :
    Precedes (fun a => physicalCost inc a m) B A := by
  have hk : n+((m-n).toNat : Int) = m := by omega
  have ha := physicalCost_advance inc A n (m-n).toNat hc.1
  have hb := physicalCost_advance inc B n (m-n).toNat hc.2.1
  rw [hk, hc.2.2.2] at ha
  rw [hk] at hb
  simp only [Precedes] at hp ⊢
  omega

def costRank (inc : State → Nat) (R T A : Nat) (n : Int) : Nat :=
  ((roots R).filter (fun B => decide (Contact R T A B n ∧
    Precedes (fun a => physicalCost inc a n) B A))).length

theorem costRank_mono (inc : State → Nat) (R T A : Nat) (n m : Int)
    (h : n ≤ m) : costRank inc R T A n ≤ costRank inc R T A m := by
  unfold costRank
  apply filter_len_mono
  intro B _ hb
  simp only [decide_eq_true_eq] at hb ⊢
  exact ⟨contact_mono R T A B n m h hb.1,
    contact_priority_mono inc R T A B n m h hb.1 hb.2⟩

def cheapRankOK (inc : State → Nat) (R T M budget A i : Nat) : Bool :=
  decide (pathCost inc (birth A) i ≤ budget ∧
    costRank inc R T A ((birth A).n + (i : Int)) ≤ M)

theorem cheapRankOK_antitone (inc : State → Nat) (R T M budget A i j : Nat)
    (h : i ≤ j) (hj : cheapRankOK inc R T M budget A j = true) :
    cheapRankOK inc R T M budget A i = true := by
  simp only [cheapRankOK, decide_eq_true_eq] at hj ⊢
  exact ⟨Nat.le_trans (pathCost_mono inc (birth A) i j h) hj.1,
    Nat.le_trans (costRank_mono inc R T A _ _ (by omega)) hj.2⟩

def cheapRankDeath (inc : State → Nat) (R T M budget A : Nat) : Nat :=
  ((List.range (observeAge R T A + T)).filter
    (cheapRankOK inc R T M budget A)).length

theorem cheapRankDeath_spec (inc : State → Nat) (R T M budget A i : Nat) :
    i < cheapRankDeath inc R T M budget A ↔
      i < observeAge R T A + T ∧ pathCost inc (birth A) i ≤ budget ∧
        costRank inc R T A ((birth A).n + (i : Int)) ≤ M := by
  unfold cheapRankDeath
  rw [antitone_count_spec _ (cheapRankOK_antitone inc R T M budget A)]
  simp [cheapRankOK]

/-- Cheapness and rank characterize actual irreversible survival at any
physical tick in the window, including all pre-observation births. -/
theorem cheapRankDeath_phys_iff (inc : State → Nat) (R T M budget A : Nat) (n : Int)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0)
    (hb : (birth A).n ≤ n) (he : n < observeStart R T A + (T : Int)) :
    physicalLiveAt (cheapRankDeath inc R T M budget) R T A n = true ↔
      physicalCost inc A n ≤ budget ∧ costRank inc R T A n ≤ M := by
  have hstart := observeStart_ge_birth R T A hT hR h6
  have ha : physicalAge A n < observeAge R T A + T := by
    unfold physicalAge observeAge
    omega
  have hclock : (birth A).n + (physicalAge A n : Int) = n := by
    unfold physicalAge
    omega
  simp only [physicalLiveAt, decide_eq_true_eq, hb, he, true_and,
    cheapRankDeath_spec, ha, hclock, physicalCost]

/-- The full (uncapped) cheap fiber at a physical tick. -/
def cheapFiber (inc : State → Nat) (R T budget J x : Nat) (n : Int) : List Nat :=
  (roots R).filter (fun A => decide ((birth A).n ≤ n ∧
    n < observeStart R T A + (T : Int) ∧ windowId R T A = J ∧
    (physicalState A n).x = x ∧ physicalCost inc A n ≤ budget))

theorem contact_same_window_end (R T A B : Nat) (h : windowId R T A = windowId R T B) :
    observeStart R T A = observeStart R T B := by
  unfold observeStart
  rw [h]

theorem cheapFiber_localRank (inc : State → Nat) (R T budget J x A : Nat) (n : Int)
    (hA : A ∈ cheapFiber inc R T budget J x n) :
    localRank (cheapFiber inc R T budget J x n) (fun a => physicalCost inc a n) A =
      costRank inc R T A n := by
  have ha := (List.mem_filter.mp hA).2
  simp only [decide_eq_true_eq] at ha
  unfold localRank cheapFiber costRank
  rw [List.filter_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro B _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨contact_of_center R T A B n ha.1 h.2.1
      (ha.2.2.1.trans h.2.2.2.1.symm) (ha.2.2.2.1.trans h.2.2.2.2.1.symm), h.1⟩
  · intro h
    have hc := h.1
    have hobs := contact_same_window_end R T A B hc.2.2.1
    have hx := congrArg State.x hc.2.2.2
    have hcost : physicalCost inc B n ≤ physicalCost inc A n := by
      have hp := h.2
      simp only [Precedes] at hp
      omega
    refine ⟨h.2, hc.2.1, ?_, hc.2.2.1.symm.trans ha.2.2.1,
      hx.symm.trans ha.2.2.2.1, Nat.le_trans hcost ha.2.2.2.2⟩
    rw [← hobs]
    exact ha.2.1

theorem cheapRankDeath_fiber_eq (inc : State → Nat) (R T M budget J x : Nat) (n : Int)
    (hT : 6 ≤ T) :
    physicalFiber (cheapRankDeath inc R T M budget) R T J x n =
      rankClip (cheapFiber inc R T budget J x n) (fun a => physicalCost inc a n) M := by
  unfold physicalFiber rankClip
  change _ = (((roots R).filter (fun A => decide ((birth A).n ≤ n ∧
    n < observeStart R T A + (T : Int) ∧ windowId R T A = J ∧
    (physicalState A n).x = x ∧ physicalCost inc A n ≤ budget))).filter
      (fun a => decide (localRank (cheapFiber inc R T budget J x n)
        (fun a => physicalCost inc a n) a ≤ M)))
  rw [List.filter_filter]
  apply List.filter_congr
  intro A hA
  have hr := hA
  simp only [roots, List.mem_filter, decide_eq_true_eq] at hr
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    have hp := h.1
    simp only [physicalLiveAt, decide_eq_true_eq] at hp
    have hc := (cheapRankDeath_phys_iff inc R T M budget A n hT hr.2.1 hr.2.2 hp.1 hp.2.1).mp h.1
    have hmem : A ∈ cheapFiber inc R T budget J x n :=
      List.mem_filter.mpr ⟨hA, by simp only [decide_eq_true_eq]; exact
        ⟨hp.1, hp.2.1, h.2.1, h.2.2, hc.1⟩⟩
    refine ⟨?_, hp.1, hp.2.1, h.2.1, h.2.2, hc.1⟩
    rw [cheapFiber_localRank inc R T budget J x A n hmem]
    exact hc.2
  · intro h
    have hmem : A ∈ cheapFiber inc R T budget J x n :=
      List.mem_filter.mpr ⟨hA, by simpa only [decide_eq_true_eq] using h.2⟩
    have hk := h.1
    rw [cheapFiber_localRank inc R T budget J x A n hmem] at hk
    refine ⟨(cheapRankDeath_phys_iff inc R T M budget A n hT hr.2.1 hr.2.2
      h.2.1 h.2.2.1).mpr ⟨h.2.2.2.2.2, hk⟩, h.2.2.2.1, h.2.2.2.2.1⟩

theorem roots_nodup (R : Nat) : (roots R).Nodup := by
  unfold roots
  exact (List.filter_sublist (p := fun A => decide (R ≤ A ∧ A % 6 = 0))).nodup List.nodup_range

/-- Exact optimal count in EVERY cheap physical fiber. Past deletions
do not reduce this count, despite birth, merge and budget deaths. -/
theorem cheapRankDeath_exact (inc : State → Nat) (R T M budget J x : Nat) (n : Int)
    (hT : 6 ≤ T) :
    (physicalFiber (cheapRankDeath inc R T M budget) R T J x n).length =
      min M (cheapFiber inc R T budget J x n).length := by
  rw [cheapRankDeath_fiber_eq inc R T M budget J x n hT, rankClip_length]
  unfold cheapFiber
  exact List.filter_sublist.nodup (roots_nodup R)

theorem cheapRankDeath_fullCapped (inc : State → Nat) (R T M budget : Nat)
    (hT : 6 ≤ T) : FullCapped (cheapRankDeath inc R T M budget) R T M := by
  intro J x n
  rw [cheapRankDeath_exact inc R T M budget J x n hT]
  exact Nat.min_le_left _ _

/-- Uniform budget overshoot: charges include the deletion-causing
event, so budget alone is insufficient without the one-tick increment. -/
theorem cheapRankDeath_budget (inc : State → Nat) (R T M budget A delta : Nat)
    (hinc : ∀ s, inc s ≤ delta) :
    pathCost inc (birth A) (prefixAge (cheapRankDeath inc R T M budget) R T A)
      ≤ budget + delta := by
  let d := prefixAge (cheapRankDeath inc R T M budget) R T A
  by_cases hd : d = 0
  · change pathCost inc (birth A) d ≤ _
    simp [hd, pathCost]
  · have hlt : d-1 < cheapRankDeath inc R T M budget A := by
      unfold d prefixAge at *
      omega
    have hs := (cheapRankDeath_spec inc R T M budget A (d-1)).mp hlt
    have he : d = (d-1)+1 := by omega
    have hh := hinc (evolve (birth A) (d-1))
    change pathCost inc (birth A) d ≤ _
    calc
      pathCost inc (birth A) d = pathCost inc (birth A) (d-1) +
          inc (evolve (birth A) (d-1)) := by
        have hstep : pathCost inc (birth A) ((d-1)+1) =
            pathCost inc (birth A) (d-1) + inc (evolve (birth A) (d-1)) := rfl
        rw [← he] at hstep
        exact hstep
      _ ≤ budget + delta := by omega

#print axioms NegativeMIN.rankClip_length
#print axioms NegativeMIN.contact_priority_mono
#print axioms NegativeMIN.cheapRankDeath_exact
#print axioms NegativeMIN.cheapRankDeath_fullCapped
#print axioms NegativeMIN.cheapRankDeath_budget

/-! Connect the generic budget policy to the exact narrow/medium charges
in ScaledLiveEstimate. No auxiliary surrogate cost is used. -/

theorem range_find_le (f : Nat → Bool) (b p : Nat) (hb : p < b) (hp : f p = true) :
    ∃ q : Nat, q ≤ p ∧ (List.range b).find? f = some q := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hpb : p < b
    · obtain ⟨q, hq, he⟩ := ih hpb
      refine ⟨q, hq, ?_⟩
      rw [List.range_succ, List.find?_append, he]
      rfl
    · have heq : p = b := by omega
      subst p
      cases he : (List.range b).find? f with
      | none =>
        refine ⟨b, by omega, ?_⟩
        simp [List.range_succ, List.find?_append, he, hp]
      | some q =>
        have hq := List.mem_range.mp (List.mem_of_find?_eq_some he)
        refine ⟨q, by omega, ?_⟩
        rw [List.range_succ, List.find?_append, he]
        rfl

theorem leastOddFactor_le (n p : Nat) (hp : oddPrime p = true)
    (hdiv : n % p = 0) (hpn : p ≤ n) :
    leastOddFactor n ≤ p := by
  obtain ⟨q, hq, he⟩ := range_find_le
    (fun r => oddPrime r && decide (n % r = 0)) (n+1) p (by omega) (by simp [hp, hdiv])
  unfold leastOddFactor
  rw [he]
  exact hq

theorem qmin_le_winner (s : State) (hw : winner s ≠ 0) : qmin s.x ≤ winner s := by
  have he := winner_sound s hw
  have hb := winner_le s
  have h3 := eligible_three_le s.x (s.n+1) (winner s) he
  unfold qmin
  by_cases hpar : (s.n+1) % 2 = 0
  · simp only [eligible, Bool.and_eq_true, if_pos hpar, decide_eq_true_eq] at he
    exact Nat.le_trans (Nat.min_le_right _ _) (leastOddFactor_le _ _ he.1 he.2.1 hb)
  · simp only [eligible, Bool.and_eq_true, if_neg hpar, decide_eq_true_eq] at he
    have hbound : winner s ≤ s.x-1 := by
      by_cases h : s.x-1 < winner s
      · rw [Nat.mod_eq_of_lt h] at he
        omega
      · omega
    exact Nat.le_trans (Nat.min_le_left _ _) (leastOddFactor_le _ _ he.1 he.2.2.1 hbound)

def narrowInc (z Y0 : Nat) (s : State) : Nat :=
  if z < winner s ∧ winner s < Y0 then 1 else 0

def mediumInc (Y0 Y1 : Nat) (s : State) : Nat :=
  if Y0 ≤ winner s ∧ winner s < Y1 ∧ (winner s)^3 ≤ (2*qmin s.x)^5
    then 2*qmin s.x else 0

def weightedInc (z Y0 Y1 wN wQ : Nat) (s : State) : Nat :=
  wN*narrowInc z Y0 s + wQ*mediumInc Y0 Y1 s

theorem weightedInc_le (z Y0 Y1 wN wQ : Nat) (s : State) (hY : 0 < Y0) :
    weightedInc z Y0 Y1 wN wQ s ≤ wN + wQ*(2*Y1) := by
  have hn : narrowInc z Y0 s ≤ 1 := by unfold narrowInc; split <;> omega
  have hm : mediumInc Y0 Y1 s ≤ 2*Y1 := by
    unfold mediumInc
    split
    next h =>
      have hw : winner s ≠ 0 := by omega
      have hq := qmin_le_winner s hw
      omega
    next _ => omega
  unfold weightedInc
  have h1 := Nat.mul_le_mul_left wN hn
  have h2 := Nat.mul_le_mul_left wQ hm
  simp only [Nat.mul_one] at h1
  omega

theorem pathCost_sum (inc : State → Nat) (s : State) (k : Nat) :
    pathCost inc s k = ((List.range k).map (fun i => inc (evolve s i))).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [pathCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, ih]

theorem weightedCost_root (deathAge : Nat → Nat) (R T A z Y0 Y1 wN wQ : Nat) :
    pathCost (weightedInc z Y0 Y1 wN wQ) (birth A) (prefixAge deathAge R T A) =
      wN * ((List.range (prefixAge deathAge R T A)).filter (fun i =>
        let p := winner (orbit A i)
        decide (z < p ∧ p < Y0))).length +
      wQ * ((List.range (prefixAge deathAge R T A)).map (fun i =>
        let s := orbit A i
        let p := winner s
        let q := qmin s.x
        if Y0 ≤ p ∧ p < Y1 ∧ p^3 ≤ (2*q)^5 then 2*q else 0)).sum := by
  rw [pathCost_sum]
  simp only [weightedInc, ← orbit]
  rw [sum_map_add, sum_map_mul, sum_map_mul, filter_length_indicator]
  simp only [narrowInc, mediumInc, decide_eq_true_eq]

theorem weightedCost_sum (deathAge : Nat → Nat) (R T z Y0 Y1 wN wQ : Nat) :
    ((roots R).map (fun A =>
      pathCost (weightedInc z Y0 Y1 wN wQ) (birth A) (prefixAge deathAge R T A))).sum =
        wN*narrowCount deathAge R T z Y0 + wQ*mediumCharge deathAge R T Y0 Y1 := by
  unfold narrowCount mediumCharge
  rw [← sum_map_mul, ← sum_map_mul, ← sum_map_add]
  congr 1
  apply List.map_congr_left
  intro A _
  exact weightedCost_root deathAge R T A z Y0 Y1 wN wQ

theorem sum_const_nat {α : Type} (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length*c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

/-- Actual aggregate prefix expense, including the killing event. -/
theorem cheapRankDeath_weightedBudget (R T M budget z Y0 Y1 wN wQ : Nat)
    (hY : 0 < Y0) :
    let d := cheapRankDeath (weightedInc z Y0 Y1 wN wQ) R T M budget
    wN*narrowCount d R T z Y0 + wQ*mediumCharge d R T Y0 Y1 ≤
      (roots R).length*(budget + wN + wQ*(2*Y1)) := by
  dsimp only
  let d := cheapRankDeath (weightedInc z Y0 Y1 wN wQ) R T M budget
  change wN*narrowCount d R T z Y0 + wQ*mediumCharge d R T Y0 Y1 ≤ _
  rw [← weightedCost_sum, ← sum_const_nat]
  apply sum_map_le
  intro A _
  have h := cheapRankDeath_budget (weightedInc z Y0 Y1 wN wQ) R T M budget A
    (wN+wQ*(2*Y1)) (fun s => weightedInc_le z Y0 Y1 wN wQ s hY)
  change pathCost (weightedInc z Y0 Y1 wN wQ) (birth A) (prefixAge d R T A) ≤ _ at h
  omega

#print axioms NegativeMIN.qmin_le_winner
#print axioms NegativeMIN.weightedCost_sum
#print axioms NegativeMIN.cheapRankDeath_weightedBudget

end NegativeMIN
