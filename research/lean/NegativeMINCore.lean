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

end NegativeMIN
