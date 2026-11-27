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
  simp only [weightedInc]
  rw [sum_map_add, sum_map_mul, sum_map_mul]
  have hn : ((List.range (prefixAge deathAge R T A)).map
      (fun i => narrowInc z Y0 (evolve (birth A) i))).sum =
        ((List.range (prefixAge deathAge R T A)).filter (fun i =>
          decide (z < winner (orbit A i) ∧ winner (orbit A i) < Y0))).length := by
    rw [filter_length_indicator]
    congr 1
    apply List.map_congr_left
    intro i _
    unfold narrowInc orbit
    by_cases h : z < winner (evolve (birth A) i) ∧ winner (evolve (birth A) i) < Y0 <;>
      simp [h]
  rw [hn]
  rfl

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

/-! Exact integrated clipping over the actual observation fibers. -/
def uniqueKeys {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a::as => if a ∈ as then uniqueKeys as else a::uniqueKeys as

theorem mem_uniqueKeys {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ uniqueKeys xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [uniqueKeys]
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [uniqueKeys, hx, if_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro h
        rcases h with rfl | h
        · exact hx
        · exact h
    · simp [uniqueKeys, hx, ih]

theorem uniqueKeys_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (uniqueKeys xs).Nodup := by
  induction xs with
  | nil => simp [uniqueKeys]
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp [uniqueKeys, hx, ih]
    · simp [uniqueKeys, hx, ih, mem_uniqueKeys]

theorem indicator_key_sum {α : Type} [DecidableEq α] (keys : List α) (k : α)
    (hn : keys.Nodup) :
    (keys.map (fun x => if k = x then 1 else 0)).sum =
      if k ∈ keys then 1 else 0 := by
  induction keys with
  | nil => simp
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : k = x
    · subst x
      simp [hn'.1, ih hn'.2]
    · simp [he, ih hn'.2]

theorem sum_fiber_counts {α β : Type} [DecidableEq β]
    (xs : List α) (keys : List β) (key : α → β) (hn : keys.Nodup)
    (hcover : ∀ a ∈ xs, key a ∈ keys) :
    (keys.map (fun k => (xs.filter (fun a => decide (key a = k))).length)).sum = xs.length := by
  have he : (keys.map (fun k => (xs.filter (fun a => decide (key a = k))).length)).sum =
      (keys.map (fun k => (xs.map (fun a => if key a = k then 1 else 0)).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro k _
    rw [filter_length_indicator]
    simp only [decide_eq_true_eq]
  rw [he, sum_map_swap]
  have heq : xs.map (fun a => (keys.map (fun k => if key a = k then 1 else 0)).sum) =
      xs.map (fun _ => 1) := by
    apply List.map_congr_left
    intro a ha
    rw [indicator_key_sum keys (key a) hn]
    simp [hcover a ha]
  rw [heq, sum_const_nat, Nat.mul_one]

def obsKey (R T A u : Nat) : Nat × Nat :=
  (windowId R T A, (observedState R T A u).x)

def obsKeys (R T u : Nat) : List (Nat × Nat) :=
  uniqueKeys ((roots R).map (fun A => obsKey R T A u))

theorem obsKeys_cover (R T A u : Nat) (h : A ∈ roots R) :
    obsKey R T A u ∈ obsKeys R T u := by
  unfold obsKeys
  apply (mem_uniqueKeys _ _).mpr
  exact List.mem_map.mpr ⟨A, h, rfl⟩

def obsLiveFiber (deathAge : Nat → Nat) (R T u : Nat) (key : Nat × Nat) : List Nat :=
  ((roots R).filter (fun A => liveAt deathAge R T A u)).filter
    (fun A => decide (obsKey R T A u = key))

def obsCheapFiber (inc : State → Nat) (R T budget u : Nat) (key : Nat × Nat) : List Nat :=
  ((roots R).filter (fun A => decide
    (pathCost inc (birth A) (observeAge R T A + u) ≤ budget))).filter
      (fun A => decide (obsKey R T A u = key))

def obsClock (R T J u : Nat) : Int :=
  3 - ((slabLo R + J * windowWidth T : Nat) : Int)/2 + (u : Int)

theorem obsClock_age (R T A J u : Nat) (hT : 6 ≤ T) (hR : R ≤ A)
    (h6 : A % 6 = 0) (hJ : windowId R T A = J) (hu : u < T) :
    (birth A).n ≤ obsClock R T J u ∧
      obsClock R T J u < observeStart R T A + (T : Int) ∧
      physicalAge A (obsClock R T J u) = observeAge R T A + u := by
  have hc : obsClock R T J u = observeStart R T A + (u : Int) := by
    unfold obsClock observeStart
    rw [hJ]
  have hb := observeStart_ge_birth R T A hT hR h6
  rw [hc]
  unfold physicalAge observeAge
  omega

theorem obsLiveFiber_eq (deathAge : Nat → Nat) (R T J x u : Nat)
    (hT : 6 ≤ T) (hu : u < T) :
    obsLiveFiber deathAge R T u (J,x) =
      physicalFiber deathAge R T J x (obsClock R T J u) := by
  unfold obsLiveFiber physicalFiber
  rw [List.filter_filter]
  apply List.filter_congr
  intro A hA
  have hr := hA
  simp only [roots, List.mem_filter, decide_eq_true_eq] at hr
  by_cases hj : windowId R T A = J
  · have hg := obsClock_age R T A J u hT hr.2.1 hr.2.2 hj hu
    simp [obsKey, hj, physicalLiveAt, liveAt, hg.1, hg.2.1, hg.2.2, observedState,
      Bool.and_comm]
  · simp [obsKey, hj]

theorem obsCheapFiber_eq (inc : State → Nat) (R T budget J x u : Nat)
    (hT : 6 ≤ T) (hu : u < T) :
    obsCheapFiber inc R T budget u (J,x) =
      cheapFiber inc R T budget J x (obsClock R T J u) := by
  unfold obsCheapFiber cheapFiber
  rw [List.filter_filter]
  apply List.filter_congr
  intro A hA
  have hr := hA
  simp only [roots, List.mem_filter, decide_eq_true_eq] at hr
  by_cases hj : windowId R T A = J
  · have hg := obsClock_age R T A J u hT hr.2.1 hr.2.2 hj hu
    simp [obsKey, hj, hg.1, hg.2.1, hg.2.2, observedState, physicalState, physicalCost,
      and_comm]
  · simp [obsKey, hj]

theorem obsCheapRank_exact (inc : State → Nat) (R T M budget u : Nat)
    (key : Nat × Nat) (hT : 6 ≤ T) (hu : u < T) :
    (obsLiveFiber (cheapRankDeath inc R T M budget) R T u key).length =
      min M (obsCheapFiber inc R T budget u key).length := by
  obtain ⟨J,x⟩ := key
  rw [obsLiveFiber_eq _ R T J x u hT hu, obsCheapFiber_eq inc R T budget J x u hT hu]
  exact cheapRankDeath_exact inc R T M budget J x (obsClock R T J u) hT

def obsBins (R T : Nat) : List (Nat × (Nat × Nat)) :=
  (List.range T).flatMap (fun u => (obsKeys R T u).map (fun k => (u,k)))

theorem sum_map_flatMap {α β : Type} (xs : List α) (g : α → List β) (f : β → Nat) :
    ((xs.flatMap g).map f).sum = (xs.map (fun x => ((g x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem liveTicks_eq_observed_sum (deathAge : Nat → Nat) (R T : Nat) :
    liveTicks deathAge R T =
      ((List.range T).map (fun u => ((roots R).filter
        (fun A => liveAt deathAge R T A u)).length)).sum := by
  unfold liveTicks
  have he : ((roots R).map (life deathAge R T)).sum =
      ((roots R).map (fun A => ((List.range T).map
        (fun u => if liveAt deathAge R T A u then 1 else 0)).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro A _
    rw [← filter_length_indicator, life_integral]
  rw [he, sum_map_swap]
  congr 1
  apply List.map_congr_left
  intro u _
  rw [filter_length_indicator]

theorem liveTicks_eq_bins (deathAge : Nat → Nat) (R T : Nat) :
    liveTicks deathAge R T =
      ((obsBins R T).map (fun b => (obsLiveFiber deathAge R T b.1 b.2).length)).sum := by
  rw [liveTicks_eq_observed_sum]
  unfold obsBins
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro u _
  simp only [List.map_map, Function.comp_def]
  symm
  unfold obsLiveFiber
  apply sum_fiber_counts
  · exact uniqueKeys_nodup _
  · intro a ha
    exact obsKeys_cover R T a u (List.mem_filter.mp ha).1

def cheapMasses (inc : State → Nat) (R T budget : Nat) : List Nat :=
  (obsBins R T).map (fun b => (obsCheapFiber inc R T budget b.1 b.2).length)

theorem cheapRankDeath_live_exact (inc : State → Nat) (R T M budget : Nat)
    (hT : 6 ≤ T) :
    liveTicks (cheapRankDeath inc R T M budget) R T =
      ((cheapMasses inc R T budget).map (min M)).sum := by
  rw [liveTicks_eq_bins]
  unfold cheapMasses
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b hb
  have hmem := List.mem_flatMap.mp hb
  obtain ⟨u, hu, hku⟩ := hmem
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hku
  subst b
  exact obsCheapRank_exact inc R T M budget u k hT (List.mem_range.mp hu)

#print axioms NegativeMIN.liveTicks_eq_bins
#print axioms NegativeMIN.cheapRankDeath_live_exact

/-! Moment lower bounds without Mathlib imports. The finite inequality
is a proof of survival for the exact policy, not a bound on the moments. -/

def moment2 (xs : List Nat) : Nat := (xs.map (fun m => m*m)).sum

theorem clip_pointwise (M K m : Nat) (hMK : M ≤ K) :
    M*K*m ≤ K*K*min M m + M*(m*m) := by
  by_cases hm : m ≤ K
  · have hclip : M*m ≤ K*min M m := by
      by_cases h : m ≤ M
      · rw [Nat.min_eq_right h]
        exact Nat.mul_le_mul_right m hMK
      · rw [Nat.min_eq_left (by omega : M ≤ m), Nat.mul_comm K M]
        exact Nat.mul_le_mul_left M hm
    calc
      M*K*m = K*(M*m) := by ac_rfl
      _ ≤ K*(K*min M m) := Nat.mul_le_mul_left K hclip
      _ ≤ K*K*min M m + M*(m*m) := by rw [← Nat.mul_assoc]; omega
  · have h : M*K*m ≤ M*m*m :=
      Nat.mul_le_mul_right m (Nat.mul_le_mul_left M (by omega : K ≤ m))
    rw [Nat.mul_assoc M m m] at h
    omega

theorem clip_moment_lower (xs : List Nat) (M K : Nat) (hMK : M ≤ K) :
    M*K*xs.sum ≤ K*K*(xs.map (min M)).sum + M*moment2 xs := by
  have h := sum_map_le xs (fun m => (M*K)*m)
    (fun m => (K*K)*min M m + M*(m*m)) (fun m _ => clip_pointwise M K m hMK)
  rw [sum_map_mul, sum_map_add, sum_map_mul, sum_map_mul] at h
  have hid : xs.map (fun m : Nat => m) = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  simpa only [moment2, hid] using h

/-- A simple explicit threshold version of the moment criterion,
valid even when the total untruncated pair loss bound exceeds the
cohort mass. No positive denominator division is hidden. -/
theorem clip_moment_half (xs : List Nat) (M K : Nat) (hMK : M ≤ K)
    (hK : 0 < K) (hQ : 2*moment2 xs ≤ K*xs.sum) :
    M*xs.sum ≤ 2*K*(xs.map (min M)).sum := by
  have h := clip_moment_lower xs M K hMK
  have h1 := Nat.mul_le_mul_left M hQ
  have h2 := Nat.mul_le_mul_left 2 h
  have ha : 2*(M*K*xs.sum) = 2*(K*(M*xs.sum)) := by ac_rfl
  have hb : M*(2*moment2 xs) = 2*(M*moment2 xs) := by ac_rfl
  have hc : M*(K*xs.sum) = K*(M*xs.sum) := by ac_rfl
  have hd : 2*(K*K*(xs.map (min M)).sum) =
      K*(2*K*(xs.map (min M)).sum) := by ac_rfl
  rw [Nat.mul_add, ha, hd] at h2
  rw [hb, hc] at h1
  have hlast : K*(M*xs.sum) ≤ K*(2*K*(xs.map (min M)).sum) := by omega
  exact Nat.le_of_mul_le_mul_left hlast hK

/-- The policy is constructive; only the stated actual moment bound
is an external hypothesis. -/
theorem cheapRankDeath_moment_lower (inc : State → Nat) (R T M budget K : Nat)
    (hT : 6 ≤ T) (hMK : M ≤ K) (hK : 0 < K)
    (hQ : 2*moment2 (cheapMasses inc R T budget) ≤ K*(cheapMasses inc R T budget).sum) :
    M*(cheapMasses inc R T budget).sum ≤
      2*K*liveTicks (cheapRankDeath inc R T M budget) R T := by
  rw [cheapRankDeath_live_exact inc R T M budget hT]
  exact clip_moment_half _ M K hMK hK hQ

#print axioms NegativeMIN.clip_moment_lower
#print axioms NegativeMIN.cheapRankDeath_moment_lower

/-- End-to-end finite extraction via the actual cheap moments. The only
analytic input is the ORIGINAL scaled live estimate on the constructed
policy; the moment and budget surplus are explicit quantitative premises. -/
theorem twin_lower_of_cheap_moments
    (R T M budget K B0 z Y0 Y1 D wN wQ err : Nat)
    (hT : 6 ≤ T) (hY : 0 < Y0) (hMK : M ≤ K) (hK : 0 < K)
    (hQ : 2*moment2 (cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget) ≤
      K*(cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget).sum)
    (hEst : ScaledLiveEstimate
      (cheapRankDeath (weightedInc z Y0 Y1 wN wQ) R T M budget)
      R T M B0 z Y0 Y1 D wN wQ err) :
    D*M*(cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget).sum -
      2*K*((roots R).length*(budget+wN+wQ*(2*Y1))+err)
      ≤ 2*K*(D*B0*M*T*twinCount R T) := by
  let inc := weightedInc z Y0 Y1 wN wQ
  let d := cheapRankDeath inc R T M budget
  have hl := cheapRankDeath_moment_lower inc R T M budget K hT hMK hK hQ
  have hc := cheapRankDeath_weightedBudget R T M budget z Y0 Y1 wN wQ hY
  change wN*narrowCount d R T z Y0 + wQ*mediumCharge d R T Y0 Y1 ≤ _ at hc
  have he : D*liveTicks d R T ≤ D*B0*M*T*twinCount R T +
      (roots R).length*(budget+wN+wQ*(2*Y1))+err := by
    unfold ScaledLiveEstimate at hEst
    change D*liveTicks d R T ≤ D*B0*M*T*twinCount R T + wN*narrowCount d R T z Y0 + wQ*mediumCharge d R T Y0 Y1 + err at hEst
    omega
  have h1 := Nat.mul_le_mul_left D hl
  have h2 := Nat.mul_le_mul_left (2*K) he
  have hcomm : D*(2*K*liveTicks d R T) = 2*K*(D*liveTicks d R T) := by ac_rfl
  change D*(M*(cheapMasses inc R T budget).sum) ≤ D*(2*K*liveTicks d R T) at h1
  rw [hcomm] at h1
  have h3 := Nat.le_trans h1 h2
  change D*M*(cheapMasses inc R T budget).sum -
    2*K*((roots R).length*(budget+wN+wQ*(2*Y1))+err) ≤ _
  rw [← Nat.mul_assoc] at h3
  simp only [Nat.mul_add] at h3 ⊢
  omega

theorem twin_above_of_cheap_moments
    (R T M budget K B0 z Y0 Y1 D wN wQ err B : Nat)
    (hT : 6 ≤ T) (hY : 0 < Y0) (hMK : M ≤ K) (hK : 0 < K)
    (hlarge : B+3*T+6 < R)
    (hQ : 2*moment2 (cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget) ≤
      K*(cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget).sum)
    (hEst : ScaledLiveEstimate
      (cheapRankDeath (weightedInc z Y0 Y1 wN wQ) R T M budget)
      R T M B0 z Y0 Y1 D wN wQ err)
    (hSurplus : 2*K*((roots R).length*(budget+wN+wQ*(2*Y1))+err) <
      D*M*(cheapMasses (weightedInc z Y0 Y1 wN wQ) R T budget).sum) :
    ∃ x : Nat, B < x ∧ TwinCenter x := by
  have ht := twin_lower_of_cheap_moments R T M budget K B0 z Y0 Y1 D wN wQ err
    hT hY hMK hK hQ hEst
  have hpos : 0 < twinCount R T := by
    by_cases hz : twinCount R T = 0
    · simp only [hz, Nat.mul_zero] at ht
      omega
    · omega
  unfold twinCount at hpos
  generalize he : twinSites R T = xs at hpos
  cases xs with
  | nil => simp at hpos
  | cons x xs =>
    have hm : x ∈ twinSites R T := by rw [he]; simp
    simp only [twinSites, List.mem_filter, decide_eq_true_eq] at hm
    have hh := hm.2.1
    exact ⟨x, by omega, hm.2.2⟩

#print axioms NegativeMIN.twin_lower_of_cheap_moments
#print axioms NegativeMIN.twin_above_of_cheap_moments

/-! Actual repeat geometry and primorial wall. These are independent
of any assertion of small average cost or small collision moments. -/

theorem winner_source_pin (s : State) (hw : winner s ≠ 0) :
    ∃ k c : Int, (s.x : Int) = (winner s : Int)*k+c ∧ (c = -1 ∨ c = 1) := by
  let p := winner s
  have he := winner_sound s hw
  change eligible s.x (s.n+1) p = true at he
  by_cases hpar : (s.n+1) % 2 = 0
  · simp only [eligible, Bool.and_eq_true, if_pos hpar, decide_eq_true_eq] at he
    have h := Nat.div_add_mod (s.x+1) p
    rw [he.2.1, Nat.add_zero] at h
    have hc := congrArg (fun t : Nat => (t : Int)) h
    simp only [Int.natCast_mul, Int.natCast_add] at hc
    change (p : Int)*(((s.x+1)/p : Nat) : Int) = (s.x : Int)+1 at hc
    refine ⟨((s.x+1)/p : Nat), -1, ?_, Or.inl rfl⟩
    change (s.x : Int) = (p : Int)*(((s.x+1)/p : Nat) : Int)+(-1)
    omega
  · simp only [eligible, Bool.and_eq_true, if_neg hpar, decide_eq_true_eq] at he
    have h := Nat.div_add_mod (s.x-1) p
    rw [he.2.2.1, Nat.add_zero] at h
    have hc := congrArg (fun t : Nat => (t : Int)) h
    simp only [Int.natCast_mul] at hc
    have hx := he.2.1
    change (p : Int)*(((s.x-1)/p : Nat) : Int) = ((s.x-1 : Nat) : Int) at hc
    have hsub : ((s.x-1 : Nat) : Int) = (s.x : Int)-1 := by omega
    rw [hsub] at hc
    refine ⟨((s.x-1)/p : Nat), 1, ?_, Or.inr rfl⟩
    change (s.x : Int) = (p : Int)*(((s.x-1)/p : Nat) : Int)+1
    omega

/-- Two actual sources of the same p>=5 have separation at least
2p-2 once the first event has moved. This excludes the p=3 exception. -/
theorem repeat_pin_gap (a b p k l c e : Int)
    (hp : 5 ≤ p) (ho : p%2 = 1) (ha : a%2 = 0) (hb : b%2 = 0)
    (hc : c = -1 ∨ c = 1) (he : e = -1 ∨ e = 1)
    (h1 : a = p*k+c) (h2 : b = p*l+e) (hm : p-1 ≤ a-b) :
    2*p-2 ≤ a-b := by
  have hd : a-b = p*(k-l)+(c-e) := by rw [Int.mul_sub]; omega
  have hce : -2 ≤ c-e ∧ c-e ≤ 2 := by omega
  have hmod : (a-b)%2 = 0 := by omega
  rw [hd, Int.add_emod, Int.mul_emod, ho] at hmod
  have ht : (k-l)%2 = 0 := by
    rcases hc with rfl | rfl <;> rcases he with rfl | rfl <;> omega
  have hpos : 0 < k-l := by
    by_cases hz : 0 < k-l
    · exact hz
    · have hle := Int.mul_le_mul_of_nonneg_left (show k-l ≤ 0 by omega)
        (show 0 ≤ p by omega)
      simp only [Int.mul_zero] at hle
      omega
  have htwo : 2 ≤ k-l := by omega
  have hmul := Int.mul_le_mul_of_nonneg_left htwo (show 0 ≤ p by omega)
  rw [Int.mul_comm p 2] at hmul
  omega

theorem orbit_center_mono (A i j : Nat) (h : i ≤ j) :
    (orbit A j).x ≤ (orbit A i).x := by
  have he : i+(j-i)=j := by omega
  have hs := evolve_add (birth A) i (j-i)
  rw [he] at hs
  change orbit A j = evolve (orbit A i) (j-i) at hs
  rw [hs]
  exact evolve_center_le _ _

theorem actual_repeat_gap (A i j p : Nat) (hA : A%2 = 0) (hij : i<j)
    (hp : 5 ≤ p) (h1 : winner (orbit A i)=p) (h2 : winner (orbit A j)=p) :
    2*(p-1) ≤ (orbit A i).x - (orbit A j).x := by
  let a := orbit A i
  let b := orbit A j
  have ha : a.x%2=0 := evolve_even (birth A) i hA
  have hb : b.x%2=0 := evolve_even (birth A) j hA
  have hp' := eligible_three_le a.x (a.n+1) (winner a)
    (winner_sound a (by change winner (orbit A i) ≠ 0; omega))
  change winner a=p at h1
  change winner b=p at h2
  obtain ⟨k,c,hac,hc⟩ := winner_source_pin a (by omega)
  obtain ⟨l,e,hbc,he⟩ := winner_source_pin b (by omega)
  rw [h1] at hac hp'
  rw [h2] at hbc
  have hg := tick_gain_exact a
  rw [h1] at hg
  have hmono := orbit_center_mono A (i+1) j (by omega)
  change b.x ≤ (tick a).x at hmono
  have hgap := repeat_pin_gap (a.x : Int) (b.x : Int) (p : Int) k l c e
    (by omega) (by omega) (by omega) (by omega) hc he hac hbc (by omega)
  change 2*(p-1) ≤ a.x-b.x
  omega

theorem repeat_relay_gain (A i j p : Nat) (hA : A%2=0) (hij : i<j)
    (hp : 5≤p) (h1 : winner (orbit A i)=p) (h2 : winner (orbit A j)=p) :
    p-1 ≤ (orbit A (i+1)).x - (orbit A j).x := by
  have hg := actual_repeat_gap A i j p hA hij hp h1 h2
  have ht := tick_gain_exact (orbit A i)
  rw [h1] at ht
  change p-1 ≤ (tick (orbit A i)).x-(orbit A j).x
  omega

theorem even_small_pin_impossible (r p k c : Int)
    (hp : 3≤p) (hr : 0≤r) (hre : r%2=0) (hc : c=-1 ∨ c=1)
    (hpin : r=p*k+c) : p-1≤r := by
  by_cases hk : 1≤k
  · have h := Int.mul_le_mul_of_nonneg_left hk (show 0≤p by omega)
    rw [Int.mul_one] at h
    omega
  · by_cases hz : k=0
    · rw [hz, Int.mul_zero, Int.zero_add] at hpin
      omega
    · have h := Int.mul_le_mul_of_nonneg_left (show k≤ -1 by omega) (show 0≤p by omega)
      rw [Int.mul_neg, Int.mul_one] at h
      omega

theorem winner_le_cell_remainder (s : State) (Q : Nat)
    (hQ : 0<Q) (hQe : Q%2=0) (he : s.x%2=0)
    (hw : winner s≠0) (hd : Q % winner s=0) :
    winner s-1 ≤ s.x%Q := by
  let p := winner s
  obtain ⟨k,c,hpin,hc⟩ := winner_source_pin s hw
  have hprime := eligible_three_le s.x (s.n+1) p (winner_sound s hw)
  have hq := Nat.div_add_mod Q p
  change Q%p=0 at hd
  rw [hd,Nat.add_zero] at hq
  have hx := Nat.div_add_mod s.x Q
  have hpar := congrArg (fun a : Nat => a%2) hx
  rw [Nat.add_mod, Nat.mul_mod, hQe, Nat.zero_mul, Nat.zero_mod, Nat.zero_add] at hpar
  have hrem : (s.x%Q)%2=0 := by omega
  have hqi := congrArg (fun a : Nat => (a : Int)) hq
  have hxi := congrArg (fun a : Nat => (a : Int)) hx
  simp only [Int.natCast_mul,Int.natCast_add] at hqi hxi
  let t : Int := k - ((Q/p : Nat) : Int)*((s.x/Q : Nat) : Int)
  have hres : (s.x%Q : Nat) = (s.x%Q : Nat) := rfl
  have hres' : ((s.x%Q : Nat) : Int) = (p : Int)*t+c := by
    change ((s.x%Q : Nat) : Int) = (p : Int)*(k-((Q/p : Nat) : Int)*((s.x/Q : Nat) : Int))+c
    rw [Int.mul_sub, ← Int.mul_assoc, hqi]
    change (s.x : Int) = (p : Int)*k+c at hpin
    omega
  have hg := even_small_pin_impossible ((s.x%Q : Nat) : Int) (p : Int) t c
    (by omega) (by omega) (by omega) hc hres'
  change p-1≤s.x%Q
  omega

theorem tick_wall (s : State) (Q : Nat) (hQ : 0<Q) (hQe : Q%2=0)
    (he : s.x%2=0) (hd : winner s=0 ∨ Q % winner s=0) :
    (tick s).x/Q=s.x/Q := by
  rcases hd with h | h
  · simp [tick,h]
  · by_cases hw : winner s=0
    · simp [tick,hw]
    · have hrem := winner_le_cell_remainder s Q hQ hQe he hw h
      have hx := Nat.div_add_mod s.x Q
      have hr := Nat.mod_lt s.x hQ
      have hcoord : (tick s).x = (s.x%Q-(winner s-1))+Q*(s.x/Q) := by
        have hg := tick_gain_exact s
        omega
      rw [hcoord,Nat.add_mul_div_left _ _ hQ,Nat.div_eq_of_lt (by omega : s.x%Q-(winner s-1)<Q)]
      simp

theorem evolve_wall (s : State) (Q k : Nat) (hQ : 0<Q) (hQe : Q%2=0)
    (he : s.x%2=0)
    (hd : ∀ i : Nat, i<k → winner (evolve s i)=0 ∨ Q%winner (evolve s i)=0) :
    (evolve s k).x/Q=s.x/Q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpre := ih (fun i hi => hd i (by omega))
    have ht := tick_wall (evolve s k) Q hQ hQe (evolve_even s k he) (hd k (by omega))
    exact ht.trans hpre

theorem evolve_wall_gain (s : State) (Q k : Nat) (hQ : 0<Q) (hQe : Q%2=0)
    (he : s.x%2=0)
    (hd : ∀ i : Nat, i<k → winner (evolve s i)=0 ∨ Q%winner (evolve s i)=0) :
    gain s (evolve s k)<Q := by
  have hw := evolve_wall s Q k hQ hQe he hd
  have hx := Nat.div_add_mod s.x Q
  have hy := Nat.div_add_mod (evolve s k).x Q
  rw [hw] at hy
  have hr := Nat.mod_lt s.x hQ
  unfold gain
  omega

#print axioms NegativeMIN.actual_repeat_gap
#print axioms NegativeMIN.repeat_relay_gain
#print axioms NegativeMIN.evolve_wall_gain


/-- A repeated p>=5 cannot be relayed solely by divisors of an even
modulus Q<=p-1. This conclusion is about actual firing ages. -/
theorem repeat_forces_escape (A i j p Q : Nat) (hA : A%2=0)
    (hij : i<j) (hp : 5≤p) (h1 : winner (orbit A i)=p)
    (h2 : winner (orbit A j)=p) (hQ : 0<Q) (hQe : Q%2=0)
    (hsmall : Q≤p-1) :
    ∃ r : Nat, i<r ∧ r<j ∧ winner (orbit A r)≠0 ∧ Q%winner (orbit A r)≠0 := by
  classical
  by_cases hex : ∃ r : Nat, i<r ∧ r<j ∧ winner (orbit A r)≠0 ∧ Q%winner (orbit A r)≠0
  · exact hex
  · exfalso
    let s := orbit A (i+1)
    let k := j-(i+1)
    have hs (t : Nat) : orbit A (i+1+t) = evolve s t :=
      evolve_add (birth A) (i+1) t
    have hd : ∀ t : Nat, t<k → winner (evolve s t)=0 ∨ Q%winner (evolve s t)=0 := by
      intro t ht
      rw [← hs]
      by_cases h0 : winner (orbit A (i+1+t))=0
      · exact Or.inl h0
      · by_cases hdiv : Q%winner (orbit A (i+1+t))=0
        · exact Or.inr hdiv
        · exact False.elim (hex ⟨i+1+t, by omega, by dsimp [k] at ht; omega, h0, hdiv⟩)
    have h := evolve_wall_gain s Q k hQ hQe (evolve_even (birth A) (i+1) hA) hd
    have hk : i+1+k=j := by dsimp [k]; omega
    have hh := hs k
    rw [hk] at hh
    rw [← hh] at h
    have hg := repeat_relay_gain A i j p hA hij hp h1 h2
    change (orbit A (i+1)).x-(orbit A j).x<Q at h
    omega

/-- Early interruption bound for an actual firing. Here k is the
age immediately before the tick. -/
theorem winner_le_age (A k : Nat) (he : A%2=0) :
    winner (orbit A k) ≤ 2*(k+1)+7 := by
  have hg := canonical_gain_bound A (k+1) he
  have hm := evolve_center_le (birth A) k
  have ht := tick_gain_exact (orbit A k)
  change (orbit A k).x ≤ A at hm
  change ((A-(tick (orbit A k)).x : Nat) : Int) ≤ _ at hg
  omega

/-- Any full-capped policy obeying the same uniform prefix budget is
dominated in cumulative observation time by cheapRankDeath. -/
theorem cheapRankDeath_optimal (inc : State → Nat) (R T M budget : Nat)
    (hT : 6≤T) (deathAge : Nat → Nat)
    (hcap : FullCapped deathAge R T M)
    (hb : ∀ A ∈ roots R, pathCost inc (birth A) (prefixAge deathAge R T A) ≤ budget) :
    liveTicks deathAge R T ≤ liveTicks (cheapRankDeath inc R T M budget) R T := by
  rw [liveTicks_eq_bins, cheapRankDeath_live_exact inc R T M budget hT]
  unfold cheapMasses
  simp only [List.map_map, Function.comp_def]
  apply sum_map_le
  intro b hb'
  obtain ⟨u,hu,hku⟩ := List.mem_flatMap.mp hb'
  obtain ⟨k,_,hk⟩ := List.mem_map.mp hku
  subst b
  obtain ⟨J,x⟩ := k
  have ht := List.mem_range.mp hu
  apply Nat.le_min.mpr
  constructor
  · rw [obsLiveFiber_eq deathAge R T J x u hT ht]
    exact hcap J x (obsClock R T J u)
  · unfold obsLiveFiber obsCheapFiber
    rw [List.filter_filter,List.filter_filter]
    apply filter_len_mono
    intro A hA ha
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ha ⊢
    refine ⟨ha.1,?_⟩
    have hl := ha.2
    unfold liveAt at hl
    simp only [decide_eq_true_eq] at hl
    have hle : observeAge R T A+u ≤ prefixAge deathAge R T A := by
      unfold prefixAge
      omega
    exact Nat.le_trans (pathCost_mono inc (birth A) _ _ hle) (hb A hA)

#print axioms NegativeMIN.repeat_forces_escape
#print axioms NegativeMIN.winner_le_age
#print axioms NegativeMIN.cheapRankDeath_optimal

/-! Exact individualized budget optimization. At a live pre-tick
state, reserve the cost of the NEXT tick. The offset is fixed per
root and does not change the physical transition. This pays for
the killing tick without overshoot. -/

def payScore (inc : State → Nat) (offset : Nat → Nat) (A : Nat) (n : Int) : Nat :=
  physicalCost inc A (n+1) + offset A

theorem pay_priority_mono (inc : State → Nat) (offset : Nat → Nat)
    (R T A B : Nat) (n m : Int) (hn : n ≤ m)
    (hc : Contact R T A B n)
    (hp : Precedes (fun a => payScore inc offset a n) B A) :
    Precedes (fun a => payScore inc offset a m) B A := by
  have hc' := contact_mono R T A B n (n+1) (by omega) hc
  have hk : n+1+((m-n).toNat : Int) = m+1 := by omega
  have ha := physicalCost_advance inc A (n+1) (m-n).toNat hc'.1
  have hb := physicalCost_advance inc B (n+1) (m-n).toNat hc'.2.1
  rw [hk, hc'.2.2.2] at ha
  rw [hk] at hb
  simp only [Precedes, payScore] at hp ⊢
  omega

def payRank (inc : State → Nat) (offset : Nat → Nat) (R T A : Nat) (n : Int) : Nat :=
  ((roots R).filter (fun B => decide (Contact R T A B n ∧
    Precedes (fun a => payScore inc offset a n) B A))).length

theorem payRank_mono (inc : State → Nat) (offset : Nat → Nat) (R T A : Nat) (n m : Int)
    (h : n ≤ m) : payRank inc offset R T A n ≤ payRank inc offset R T A m := by
  unfold payRank
  apply filter_len_mono
  intro B _ hb
  simp only [decide_eq_true_eq] at hb ⊢
  exact ⟨contact_mono R T A B n m h hb.1,
    pay_priority_mono inc offset R T A B n m h hb.1 hb.2⟩

def payOK (inc : State → Nat) (offset : Nat → Nat) (R T M budget A i : Nat) : Bool :=
  decide (pathCost inc (birth A) (i+1) + offset A ≤ budget ∧
    payRank inc offset R T A ((birth A).n + (i : Int)) ≤ M)

theorem payOK_antitone (inc : State → Nat) (offset : Nat → Nat) (R T M budget A i j : Nat)
    (h : i ≤ j) (hj : payOK inc offset R T M budget A j = true) :
    payOK inc offset R T M budget A i = true := by
  simp only [payOK, decide_eq_true_eq] at hj ⊢
  exact ⟨by have hh := pathCost_mono inc (birth A) (i+1) (j+1) (by omega); omega,
    Nat.le_trans (payRank_mono inc offset R T A _ _ (by omega)) hj.2⟩

def payDeath (inc : State → Nat) (offset : Nat → Nat) (R T M budget A : Nat) : Nat :=
  ((List.range (observeAge R T A + T)).filter
    (payOK inc offset R T M budget A)).length

theorem payDeath_spec (inc : State → Nat) (offset : Nat → Nat) (R T M budget A i : Nat) :
    i < payDeath inc offset R T M budget A ↔
      i < observeAge R T A + T ∧ pathCost inc (birth A) (i+1) + offset A ≤ budget ∧
        payRank inc offset R T A ((birth A).n + (i : Int)) ≤ M := by
  unfold payDeath
  rw [antitone_count_spec _ (payOK_antitone inc offset R T M budget A)]
  simp [payOK]

/-- Cheapness and rank characterize actual irreversible survival at any
physical tick in the window, including all pre-observation births. -/
theorem payDeath_phys_iff (inc : State → Nat) (offset : Nat → Nat) (R T M budget A : Nat) (n : Int)
    (hT : 6 ≤ T) (hR : R ≤ A) (h6 : A % 6 = 0)
    (hb : (birth A).n ≤ n) (he : n < observeStart R T A + (T : Int)) :
    physicalLiveAt (payDeath inc offset R T M budget) R T A n = true ↔
      payScore inc offset A n ≤ budget ∧ payRank inc offset R T A n ≤ M := by
  have hstart := observeStart_ge_birth R T A hT hR h6
  have ha : physicalAge A n < observeAge R T A + T := by
    unfold physicalAge observeAge
    omega
  have hclock : (birth A).n + (physicalAge A n : Int) = n := by
    unfold physicalAge
    omega
  have hs : physicalAge A (n+1) = physicalAge A n + 1 := by
    unfold physicalAge
    omega
  simp only [physicalLiveAt, decide_eq_true_eq, hb, he, true_and,
    payDeath_spec, ha, hclock, payScore, physicalCost, hs]

/-- The full (uncapped) cheap fiber at a physical tick. -/
def payFiber (inc : State → Nat) (offset : Nat → Nat) (R T budget J x : Nat) (n : Int) : List Nat :=
  (roots R).filter (fun A => decide ((birth A).n ≤ n ∧
    n < observeStart R T A + (T : Int) ∧ windowId R T A = J ∧
    (physicalState A n).x = x ∧ payScore inc offset A n ≤ budget))

theorem payFiber_localRank (inc : State → Nat) (offset : Nat → Nat) (R T budget J x A : Nat) (n : Int)
    (hA : A ∈ payFiber inc offset R T budget J x n) :
    localRank (payFiber inc offset R T budget J x n) (fun a => payScore inc offset a n) A =
      payRank inc offset R T A n := by
  have ha := (List.mem_filter.mp hA).2
  simp only [decide_eq_true_eq] at ha
  unfold localRank payFiber payRank
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
    have hcost : payScore inc offset B n ≤ payScore inc offset A n := by
      have hp := h.2
      simp only [Precedes] at hp
      omega
    refine ⟨h.2, hc.2.1, ?_, hc.2.2.1.symm.trans ha.2.2.1,
      hx.symm.trans ha.2.2.2.1, Nat.le_trans hcost ha.2.2.2.2⟩
    rw [← hobs]
    exact ha.2.1

theorem payDeath_fiber_eq (inc : State → Nat) (offset : Nat → Nat) (R T M budget J x : Nat) (n : Int)
    (hT : 6 ≤ T) :
    physicalFiber (payDeath inc offset R T M budget) R T J x n =
      rankClip (payFiber inc offset R T budget J x n) (fun a => payScore inc offset a n) M := by
  unfold physicalFiber rankClip
  change _ = (((roots R).filter (fun A => decide ((birth A).n ≤ n ∧
    n < observeStart R T A + (T : Int) ∧ windowId R T A = J ∧
    (physicalState A n).x = x ∧ payScore inc offset A n ≤ budget))).filter
      (fun a => decide (localRank (payFiber inc offset R T budget J x n)
        (fun a => payScore inc offset a n) a ≤ M)))
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
    have hc := (payDeath_phys_iff inc offset R T M budget A n hT hr.2.1 hr.2.2 hp.1 hp.2.1).mp h.1
    have hmem : A ∈ payFiber inc offset R T budget J x n :=
      List.mem_filter.mpr ⟨hA, by simp only [decide_eq_true_eq]; exact
        ⟨hp.1, hp.2.1, h.2.1, h.2.2, hc.1⟩⟩
    refine ⟨?_, hp.1, hp.2.1, h.2.1, h.2.2, hc.1⟩
    rw [payFiber_localRank inc offset R T budget J x A n hmem]
    exact hc.2
  · intro h
    have hmem : A ∈ payFiber inc offset R T budget J x n :=
      List.mem_filter.mpr ⟨hA, by simpa only [decide_eq_true_eq] using h.2⟩
    have hk := h.1
    rw [payFiber_localRank inc offset R T budget J x A n hmem] at hk
    refine ⟨(payDeath_phys_iff inc offset R T M budget A n hT hr.2.1 hr.2.2
      h.2.1 h.2.2.1).mpr ⟨h.2.2.2.2.2, hk⟩, h.2.2.2.1, h.2.2.2.2.1⟩

theorem payDeath_exact (inc : State → Nat) (offset : Nat → Nat) (R T M budget J x : Nat) (n : Int)
    (hT : 6 ≤ T) :
    (physicalFiber (payDeath inc offset R T M budget) R T J x n).length =
      min M (payFiber inc offset R T budget J x n).length := by
  rw [payDeath_fiber_eq inc offset R T M budget J x n hT, rankClip_length]
  unfold payFiber
  exact List.filter_sublist.nodup (roots_nodup R)

theorem payDeath_fullCapped (inc : State → Nat) (offset : Nat → Nat) (R T M budget : Nat)
    (hT : 6 ≤ T) : FullCapped (payDeath inc offset R T M budget) R T M := by
  intro J x n
  rw [payDeath_exact inc offset R T M budget J x n hT]
  exact Nat.min_le_left _ _

/-- Completed prefix expense (including death-causing tick) is
bounded by the individual allowance. No uniform increment bound. -/
theorem payDeath_budget (inc : State → Nat) (offset : Nat → Nat)
    (R T M budget A : Nat) :
    pathCost inc (birth A) (prefixAge (payDeath inc offset R T M budget) R T A)
      ≤ budget - offset A := by
  let d := prefixAge (payDeath inc offset R T M budget) R T A
  by_cases hd : d=0
  · change pathCost inc (birth A) d ≤ _
    simp [hd, pathCost]
  · have hlt : d-1 < payDeath inc offset R T M budget A := by
      unfold d prefixAge at *
      omega
    have hs := (payDeath_spec inc offset R T M budget A (d-1)).mp hlt
    have he : d-1+1=d := by omega
    rw [he] at hs
    change pathCost inc (birth A) d ≤ _
    omega

def obsPayFiber (inc : State → Nat) (offset : Nat → Nat) (R T budget u : Nat) (key : Nat × Nat) : List Nat :=
  ((roots R).filter (fun A => decide
    (pathCost inc (birth A) (observeAge R T A + u + 1) + offset A ≤ budget))).filter
      (fun A => decide (obsKey R T A u = key))

theorem obsPayFiber_eq (inc : State → Nat) (offset : Nat → Nat) (R T budget J x u : Nat)
    (hT : 6 ≤ T) (hu : u < T) :
    obsPayFiber inc offset R T budget u (J,x) =
      payFiber inc offset R T budget J x (obsClock R T J u) := by
  unfold obsPayFiber payFiber
  rw [List.filter_filter]
  apply List.filter_congr
  intro A hA
  have hr := hA
  simp only [roots, List.mem_filter, decide_eq_true_eq] at hr
  by_cases hj : windowId R T A = J
  · have hg := obsClock_age R T A J u hT hr.2.1 hr.2.2 hj hu
    have hs : physicalAge A (obsClock R T J u + 1) = observeAge R T A + u + 1 := by
      have hb := hg.1
      have he := hg.2.2
      unfold physicalAge at *
      omega
    simp [obsKey, hj, hg.1, hg.2.1, hg.2.2, hs, observedState, physicalState, payScore, physicalCost]
  · simp [obsKey, hj]

theorem obsPayRank_exact (inc : State → Nat) (offset : Nat → Nat) (R T M budget u : Nat)
    (key : Nat × Nat) (hT : 6 ≤ T) (hu : u < T) :
    (obsLiveFiber (payDeath inc offset R T M budget) R T u key).length =
      min M (obsPayFiber inc offset R T budget u key).length := by
  obtain ⟨J,x⟩ := key
  rw [obsLiveFiber_eq _ R T J x u hT hu, obsPayFiber_eq inc offset R T budget J x u hT hu]
  exact payDeath_exact inc offset R T M budget J x (obsClock R T J u) hT

def payMasses (inc : State → Nat) (offset : Nat → Nat) (R T budget : Nat) : List Nat :=
  (obsBins R T).map (fun b => (obsPayFiber inc offset R T budget b.1 b.2).length)

theorem payDeath_live_exact (inc : State → Nat) (offset : Nat → Nat) (R T M budget : Nat)
    (hT : 6 ≤ T) :
    liveTicks (payDeath inc offset R T M budget) R T =
      ((payMasses inc offset R T budget).map (min M)).sum := by
  rw [liveTicks_eq_bins]
  unfold payMasses
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b hb
  have hmem := List.mem_flatMap.mp hb
  obtain ⟨u, hu, hku⟩ := hmem
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hku
  subst b
  exact obsPayRank_exact inc offset R T M budget u k hT (List.mem_range.mp hu)

theorem payDeath_optimal (inc : State → Nat) (offset : Nat → Nat) (R T M budget : Nat)
    (hT : 6≤T) (deathAge : Nat → Nat)
    (hcap : FullCapped deathAge R T M)
    (hb : ∀ A ∈ roots R, pathCost inc (birth A) (prefixAge deathAge R T A) + offset A ≤ budget) :
    liveTicks deathAge R T ≤ liveTicks (payDeath inc offset R T M budget) R T := by
  rw [liveTicks_eq_bins, payDeath_live_exact inc offset R T M budget hT]
  unfold payMasses
  simp only [List.map_map, Function.comp_def]
  apply sum_map_le
  intro b hb'
  obtain ⟨u,hu,hku⟩ := List.mem_flatMap.mp hb'
  obtain ⟨k,_,hk⟩ := List.mem_map.mp hku
  subst b
  obtain ⟨J,x⟩ := k
  have ht := List.mem_range.mp hu
  apply Nat.le_min.mpr
  constructor
  · rw [obsLiveFiber_eq deathAge R T J x u hT ht]
    exact hcap J x (obsClock R T J u)
  · unfold obsLiveFiber obsPayFiber
    rw [List.filter_filter,List.filter_filter]
    apply filter_len_mono
    intro A hA ha
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ha ⊢
    refine ⟨ha.1,?_⟩
    have hl := ha.2
    unfold liveAt at hl
    simp only [decide_eq_true_eq] at hl
    have hle : observeAge R T A+u+1 ≤ prefixAge deathAge R T A := by
      unfold prefixAge
      omega
    have hcost := pathCost_mono inc (birth A) _ _ hle
    have hbudget := hb A hA
    omega


theorem member_le_sum (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have hh := ih h
      omega

def totalExpense (inc : State → Nat) (R T : Nat) (d : Nat → Nat) : Nat :=
  ((roots R).map (fun A => pathCost inc (birth A) (prefixAge d R T A))).sum

def individualOffset (inc : State → Nat) (R T : Nat) (d : Nat → Nat) (A : Nat) : Nat :=
  totalExpense inc R T d - pathCost inc (birth A) (prefixAge d R T A)

theorem individualOffset_eq (inc : State → Nat) (R T : Nat) (d : Nat → Nat) (A : Nat)
    (hA : A ∈ roots R) :
    pathCost inc (birth A) (prefixAge d R T A) + individualOffset inc R T d A =
      totalExpense inc R T d := by
  have h := member_le_sum ((roots R).map (fun B => pathCost inc (birth B) (prefixAge d R T B)))
    (pathCost inc (birth A) (prefixAge d R T A)) (List.mem_map.mpr ⟨A,hA,rfl⟩)
  unfold individualOffset totalExpense
  omega

/-- Every existing admissible policy has an individualized reserve
policy that dominates its lifetime at no greater aggregate expense.
In fact each individual completed prefix expense is no larger. -/
theorem payDeath_dominates (inc : State → Nat) (R T M : Nat)
    (hT : 6≤T) (d : Nat → Nat) (hc : FullCapped d R T M) :
    let e := payDeath inc (individualOffset inc R T d) R T M (totalExpense inc R T d)
    FullCapped e R T M ∧ liveTicks d R T ≤ liveTicks e R T ∧
      totalExpense inc R T e ≤ totalExpense inc R T d := by
  dsimp only
  refine ⟨payDeath_fullCapped inc _ R T M _ hT, ?_, ?_⟩
  · apply payDeath_optimal inc _ R T M _ hT d hc
    intro A hA
    exact Nat.le_of_eq (individualOffset_eq inc R T d A hA)
  · unfold totalExpense
    apply sum_map_le
    intro A hA
    have h := payDeath_budget inc (individualOffset inc R T d) R T M (totalExpense inc R T d) A
    have he := individualOffset_eq inc R T d A hA
    change pathCost inc (birth A) (prefixAge (payDeath inc (individualOffset inc R T d) R T M (totalExpense inc R T d)) R T A) ≤ pathCost inc (birth A) (prefixAge d R T A)
    omega

#print axioms NegativeMIN.payDeath_fullCapped
#print axioms NegativeMIN.payDeath_budget
#print axioms NegativeMIN.payDeath_live_exact
#print axioms NegativeMIN.payDeath_dominates

/-! A sharper integer moment inequality, with no division or
real-number imports. It is the cross-multiplied Cauchy bound. -/

def clipDen (M m : Nat) : Nat := (M-1)*m+m*m

theorem nat_two_mul_le_squares (a b : Nat) : 2*a*b ≤ a*a+b*b := by
  by_cases h : a ≤ b
  · have e : b-a+a=b := by omega
    have h1 : (b-a)*a+a*a=b*a := by rw [← Nat.add_mul,e]
    have h2 : (b-a)*b+a*b=b*b := by rw [← Nat.add_mul,e]
    have h3 := Nat.mul_le_mul_left (b-a) h
    rw [Nat.mul_comm b a] at h1
    rw [Nat.mul_assoc] 
    omega
  · have e : a-b+b=a := by omega
    have h1 : (a-b)*b+b*b=a*b := by rw [← Nat.add_mul,e]
    have h2 : (a-b)*a+b*a=a*a := by rw [← Nat.add_mul,e]
    have h3 := Nat.mul_le_mul_left (a-b) (by omega : b≤a)
    rw [Nat.mul_comm b a] at h2
    rw [Nat.mul_assoc]
    omega

theorem clipDen_lower (M m : Nat) (hm : 0<m) : M*m ≤ clipDen M m := by
  unfold clipDen
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right m (by omega)

theorem clipDen_large (M m : Nat) (h : M<m) : 2*M*m ≤ clipDen M m := by
  unfold clipDen
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right m (by omega)

theorem clip_cross (M a b : Nat) (hM : 0<M) :
    2*M*a*b ≤ min M a*clipDen M b + min M b*clipDen M a := by
  by_cases ha0 : a=0
  · simp [ha0, clipDen]
  by_cases hb0 : b=0
  · simp [hb0, clipDen]
  by_cases ha : a≤M
  · rw [Nat.min_eq_right ha]
    by_cases hb : b≤M
    · rw [Nat.min_eq_right hb]
      have h1 := Nat.mul_le_mul_left a (clipDen_lower M b (by omega))
      have h2 := Nat.mul_le_mul_left b (clipDen_lower M a (by omega))
      have e1 : a*(M*b)=M*a*b := by ac_rfl
      have e2 : b*(M*a)=M*a*b := by ac_rfl
      rw [e1] at h1
      rw [e2] at h2
      have e : 2*M*a*b = M*a*b+M*a*b := by rw [show 2=1+1 by rfl, Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.one_mul]
      rw [e]
      omega
    · have h := Nat.mul_le_mul_left a (clipDen_large M b (by omega))
      have e : a*(2*M*b)=2*M*a*b := by ac_rfl
      rw [e] at h
      omega
  · by_cases hb : b≤M
    · rw [Nat.min_eq_right hb]
      have h := Nat.mul_le_mul_left b (clipDen_large M a (by omega))
      have e : b*(2*M*a)=2*M*a*b := by ac_rfl
      rw [e] at h
      omega
    · rw [Nat.min_eq_left (by omega : M≤a), Nat.min_eq_left (by omega : M≤b)]
      have h := Nat.mul_le_mul_left M (nat_two_mul_le_squares a b)
      have e : M*(2*a*b)=2*M*a*b := by ac_rfl
      rw [e,Nat.mul_add] at h
      unfold clipDen
      simp only [Nat.mul_add]
      omega

theorem sum_self_map (xs : List Nat) : (xs.map (fun m : Nat => m)).sum=xs.sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem clip_cross_row (xs : List Nat) (M a : Nat) (hM : 0<M) :
    2*M*a*xs.sum ≤ min M a*(xs.map (clipDen M)).sum +
      (xs.map (min M)).sum*clipDen M a := by
  have h := sum_map_le xs (fun b => 2*M*a*b)
    (fun b => min M a*clipDen M b + min M b*clipDen M a)
    (fun b _ => clip_cross M a b hM)
  have hr : (xs.map (fun b => min M b*clipDen M a)).sum =
      clipDen M a*(xs.map (min M)).sum := by
    have he : xs.map (fun b => min M b*clipDen M a) =
        xs.map (fun b => clipDen M a*min M b) := by
      apply List.map_congr_left
      intro b _
      exact Nat.mul_comm _ _
    rw [he, sum_map_mul]
  rw [sum_map_mul,sum_self_map,sum_map_add,sum_map_mul,hr] at h
  rwa [Nat.mul_comm (clipDen M a)] at h

theorem clip_sharp (xs : List Nat) (M : Nat) (hM : 0<M) :
    M*xs.sum*xs.sum ≤ (xs.map (min M)).sum*((M-1)*xs.sum+moment2 xs) := by
  have h := sum_map_le xs (fun a => 2*M*a*xs.sum)
    (fun a => min M a*(xs.map (clipDen M)).sum+
      (xs.map (min M)).sum*clipDen M a)
    (fun a _ => clip_cross_row xs M a hM)
  have hl : (xs.map (fun a => 2*M*a*xs.sum)).sum = 2*(M*xs.sum*xs.sum) := by
    have he : xs.map (fun a => 2*M*a*xs.sum) = xs.map (fun a => (2*M*xs.sum)*a) := by
      apply List.map_congr_left
      intro a _
      ac_rfl
    rw [he,sum_map_mul,sum_self_map]
    ac_rfl
  have hr : (xs.map (fun a => min M a*(xs.map (clipDen M)).sum)).sum =
      (xs.map (min M)).sum*(xs.map (clipDen M)).sum := by
    have he : xs.map (fun a => min M a*(xs.map (clipDen M)).sum) =
        xs.map (fun a => (xs.map (clipDen M)).sum*min M a) := by
      apply List.map_congr_left
      intro a _
      exact Nat.mul_comm _ _
    rw [he,sum_map_mul,Nat.mul_comm]
  have hd : (xs.map (clipDen M)).sum=(M-1)*xs.sum+moment2 xs := by
    unfold clipDen moment2
    rw [sum_map_add,sum_map_mul,sum_self_map]
  rw [hl,sum_map_add,hr,sum_map_mul,hd] at h
  omega

theorem payDeath_sharp_moment (inc : State → Nat) (offset : Nat → Nat)
    (R T M budget : Nat) (hT : 6≤T) (hM : 0<M) :
    let xs := payMasses inc offset R T budget
    M*xs.sum*xs.sum ≤ liveTicks (payDeath inc offset R T M budget) R T *
      ((M-1)*xs.sum+moment2 xs) := by
  dsimp only
  rw [payDeath_live_exact inc offset R T M budget hT]
  exact clip_sharp _ M hM

#print axioms NegativeMIN.clip_sharp
#print axioms NegativeMIN.payDeath_sharp_moment

/-! Running maximum and reflected-debt identities for exact signed
net prefix reward. These one-path statements are the kernel-checked
basis of the merging-forest optimizer, not its unproved asymptotics. -/
def runningPeak (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | k+1 => max (runningPeak f k) (f (k+1))

def recordDebt (f : Nat → Int) (k : Nat) : Int :=
  runningPeak f k-f k

def recordProfit (f : Nat → Int) (k : Nat) : Int :=
  runningPeak f (k+1)-runningPeak f k

theorem runningPeak_ge (f : Nat → Int) (k : Nat) : f k≤runningPeak f k := by
  cases k with
  | zero => exact Int.le_refl _
  | succ k => exact Int.le_max_right _ _

theorem recordDebt_nonneg (f : Nat → Int) (k : Nat) : 0≤recordDebt f k := by
  have h := runningPeak_ge f k
  unfold recordDebt
  omega

theorem recordProfit_nonneg (f : Nat → Int) (k : Nat) : 0≤recordProfit f k := by
  unfold recordProfit
  change 0≤max (runningPeak f k) (f (k+1))-runningPeak f k
  have h := Int.le_max_left (runningPeak f k) (f (k+1))
  omega

theorem recordDebt_succ (f : Nat → Int) (k : Nat) :
    recordDebt f (k+1) = max 0 (recordDebt f k-(f (k+1)-f k)) := by
  unfold recordDebt
  simp only [runningPeak]
  by_cases h : runningPeak f k ≤ f (k+1)
  · rw [Int.max_eq_right h, Int.max_eq_left (by omega : runningPeak f k-f k-(f (k+1)-f k)≤0)]
    omega
  · rw [Int.max_eq_left (by omega : f (k+1)≤runningPeak f k),
      Int.max_eq_right (by omega : 0≤runningPeak f k-f k-(f (k+1)-f k))]
    omega

theorem recordProfit_eq (f : Nat → Int) (k : Nat) :
    recordProfit f k = max 0 (f (k+1)-f k-recordDebt f k) := by
  unfold recordProfit recordDebt
  simp only [runningPeak]
  by_cases h : runningPeak f k ≤ f (k+1)
  · rw [Int.max_eq_right h, Int.max_eq_right (by omega : 0≤f (k+1)-f k-(runningPeak f k-f k))]
    omega
  · rw [Int.max_eq_left (by omega : f (k+1)≤runningPeak f k),
      Int.max_eq_left (by omega : f (k+1)-f k-(runningPeak f k-f k)≤0)]
    omega

theorem runningPeak_ge_of_le (f : Nat → Int) (i k : Nat) (h : i≤k) :
    f i≤runningPeak f k := by
  induction k with
  | zero =>
    have hi : i=0 := by omega
    rw [hi]
    exact runningPeak_ge f 0
  | succ k ih =>
    by_cases he : i=k+1
    · subst i; exact runningPeak_ge f (k+1)
    · exact Int.le_trans (ih (by omega)) (Int.le_max_left _ _)

def bestPrefix (f : Nat → Int) : Nat → Nat
  | 0 => 0
  | k+1 => if runningPeak f k≤f (k+1) then k+1 else bestPrefix f k

theorem bestPrefix_le (f : Nat → Int) (k : Nat) : bestPrefix f k≤k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    simp only [bestPrefix]
    split <;> omega

theorem bestPrefix_peak (f : Nat → Int) (k : Nat) :
    f (bestPrefix f k)=runningPeak f k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bestPrefix,runningPeak]
    split
    next h => rw [Int.max_eq_right h]
    next h => rw [ih,Int.max_eq_left (by omega : f (k+1)≤runningPeak f k)]

theorem recordProfit_sum (f : Nat → Int) (k : Nat) :
    ((List.range k).map (recordProfit f)).sum = runningPeak f k-f 0 := by
  induction k with
  | zero => simp [runningPeak]
  | succ k ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.add_zero,ih,recordProfit]
    omega

/-- A debt-free state is exactly a nonpositive charge excess on every
previous suffix. This is a local-in-time rather than a total-cost test. -/
theorem recordDebt_zero_iff (f : Nat → Int) (k : Nat) :
    recordDebt f k=0 ↔ ∀ i : Nat, i≤k → f i≤f k := by
  constructor
  · intro h i hi
    have h1 := runningPeak_ge_of_le f i k hi
    unfold recordDebt at h
    omega
  · intro h
    have hi := bestPrefix_le f k
    have he := bestPrefix_peak f k
    have hh := h (bestPrefix f k) hi
    have hg := runningPeak_ge f k
    unfold recordDebt
    omega

theorem recordDebt_suffix_upper (f : Nat → Int) (k : Nat) (b : Int)
    (h : ∀ i : Nat, i≤k → f i-f k≤b) :
    recordDebt f k≤b := by
  have he := bestPrefix_peak f k
  have hh := h (bestPrefix f k) (bestPrefix_le f k)
  unfold recordDebt
  omega

def rootNet (inc : State → Nat) (D R T A k : Nat) : Int :=
  (D : Int)*(min T (k-observeAge R T A) : Nat) -
    (pathCost inc (birth A) k : Int)

theorem rootNet_zero (inc : State → Nat) (D R T A : Nat) :
    rootNet inc D R T A 0=0 := by simp [rootNet,pathCost]

def observedReward (R T A k : Nat) : Nat :=
  if observeAge R T A≤k ∧ k<observeAge R T A+T then 1 else 0

theorem observation_increment (R T A k : Nat) :
    min T (k+1-observeAge R T A) =
      min T (k-observeAge R T A)+observedReward R T A k := by
  unfold observedReward
  split <;> omega

theorem rootNet_increment (inc : State → Nat) (D R T A k : Nat) :
    rootNet inc D R T A (k+1)-rootNet inc D R T A k =
      (D : Int)*(observedReward R T A k : Nat)-(inc (orbit A k) : Int) := by
  unfold rootNet
  rw [observation_increment]
  simp only [Int.natCast_add,Int.mul_add,pathCost,orbit]
  omega

def peakTruncate (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) (A : Nat) : Nat :=
  bestPrefix (rootNet inc D R T A) (prefixAge d R T A)

theorem peakTruncate_le (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) (A : Nat) :
    peakTruncate inc D R T d A≤d A := by
  have h := bestPrefix_le (rootNet inc D R T A) (prefixAge d R T A)
  unfold peakTruncate prefixAge at *
  omega

theorem peakTruncate_fullCapped (inc : State → Nat) (D R T M : Nat)
    (d : Nat → Nat) (hc : FullCapped d R T M) :
    FullCapped (peakTruncate inc D R T d) R T M := by
  intro J x n
  apply Nat.le_trans _ (hc J x n)
  unfold physicalFiber
  apply filter_len_mono
  intro A _ h
  simp only [Bool.and_eq_true,physicalLiveAt,decide_eq_true_eq] at h ⊢
  have hp := peakTruncate_le inc D R T d A
  exact ⟨⟨h.1.1,h.1.2.1,by omega⟩,h.2⟩

theorem peakTruncate_prefix (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) (A : Nat) :
    prefixAge (peakTruncate inc D R T d) R T A=peakTruncate inc D R T d A := by
  have h := bestPrefix_le (rootNet inc D R T A) (prefixAge d R T A)
  simp only [peakTruncate,prefixAge] at h ⊢
  omega

theorem peakTruncate_net (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) (A : Nat) :
    rootNet inc D R T A (prefixAge (peakTruncate inc D R T d) R T A)=
      ((List.range (prefixAge d R T A)).map (recordProfit (rootNet inc D R T A))).sum := by
  rw [peakTruncate_prefix,peakTruncate,bestPrefix_peak (rootNet inc D R T A),recordProfit_sum,rootNet_zero,Int.sub_zero]

/-- Integer-weighted signed net prefix objective of an actual policy. -/
def policyNet (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) : Int :=
  ((roots R).map (fun A => rootNet inc D R T A (prefixAge d R T A))).sum

theorem peakTruncate_policyNet (inc : State → Nat) (D R T : Nat) (d : Nat → Nat) :
    policyNet inc D R T (peakTruncate inc D R T d)=
      ((roots R).map (fun A => ((List.range (prefixAge d R T A)).map
        (recordProfit (rootNet inc D R T A))).sum)).sum := by
  unfold policyNet
  congr 1
  apply List.map_congr_left
  intro A _
  exact peakTruncate_net inc D R T d A

#print axioms NegativeMIN.recordDebt_zero_iff
#print axioms NegativeMIN.peakTruncate_fullCapped
#print axioms NegativeMIN.peakTruncate_policyNet

/-! Stable priority for reflected debt. A tie can arise when two
different debts are both repaid. A fixed ID tie-break alone can
then resurrect a discarded root. Reverse chronological debt
history solves this; a variable radix avoids any growth assumption. -/
def digitBase (xs : List Nat) (digit : Nat → Nat → Nat) (t : Nat) : Nat :=
  1+(xs.map (fun a => digit a t)).sum

def digitPlace (xs : List Nat) (digit : Nat → Nat → Nat) : Nat → Nat
  | 0 => 1
  | t+1 => digitPlace xs digit t * digitBase xs digit t

def historyCode (xs : List Nat) (digit : Nat → Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => digit a 0
  | t+1 => digit a (t+1)*digitPlace xs digit (t+1)+historyCode xs digit a t

theorem digit_lt_base (xs : List Nat) (digit : Nat → Nat → Nat) (a t : Nat)
    (ha : a∈xs) : digit a t < digitBase xs digit t := by
  have h := member_le_sum (xs.map (fun b => digit b t)) (digit a t) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  unfold digitBase
  omega

theorem digitPlace_pos (xs : List Nat) (digit : Nat → Nat → Nat) (t : Nat) :
    0<digitPlace xs digit t := by
  induction t with
  | zero => decide
  | succ t ih =>
    simp only [digitPlace]
    apply Nat.mul_pos ih
    unfold digitBase
    omega

theorem historyCode_bound (xs : List Nat) (digit : Nat → Nat → Nat) (a t : Nat)
    (ha : a∈xs) : historyCode xs digit a t<digitPlace xs digit (t+1) := by
  induction t with
  | zero =>
    simpa [historyCode,digitPlace] using digit_lt_base xs digit a 0 ha
  | succ t ih =>
    have hd := digit_lt_base xs digit a (t+1) ha
    have hm := Nat.mul_le_mul_right (digitPlace xs digit (t+1))
      (show digit a (t+1)+1≤digitBase xs digit (t+1) by omega)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (digitBase xs digit (t+1))] at hm
    change digit a (t+1)*digitPlace xs digit (t+1)+historyCode xs digit a t <
      digitPlace xs digit (t+1)*digitBase xs digit (t+1)
    omega

theorem historyCode_digit_le (xs : List Nat) (digit : Nat → Nat → Nat) (a b t : Nat)
    (ha : a∈xs) (h : historyCode xs digit b t≤historyCode xs digit a t) :
    digit b t≤digit a t := by
  cases t with
  | zero => exact h
  | succ t =>
    by_contra hn
    have hb := historyCode_bound xs digit a t ha
    have hm := Nat.mul_le_mul_right (digitPlace xs digit (t+1))
      (show digit a (t+1)+1≤digit b (t+1) by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    change digit b (t+1)*digitPlace xs digit (t+1)+historyCode xs digit b t ≤
      digit a (t+1)*digitPlace xs digit (t+1)+historyCode xs digit a t at h
    omega

theorem historyCode_priority_step (xs : List Nat) (digit : Nat → Nat → Nat)
    (a b t : Nat)
    (h : Precedes (fun c => historyCode xs digit c t) b a)
    (hd : digit b (t+1)≤digit a (t+1)) :
    Precedes (fun c => historyCode xs digit c (t+1)) b a := by
  have hm := Nat.mul_le_mul_right (digitPlace xs digit (t+1)) hd
  simp only [Precedes,historyCode] at h ⊢
  omega

def epoch (R : Nat) : Int := 3-(R : Int)
def absoluteTick (R t : Nat) : Int := epoch R+(t : Int)
def absoluteAge (R : Nat) (n : Int) : Nat := (n-epoch R).toNat

theorem epoch_le_birth (R A : Nat) (hA : A∈roots R) : epoch R≤(birth A).n := by
  simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq] at hA
  unfold epoch birth
  omega

theorem absoluteTick_age (R : Nat) (n : Int) (hn : epoch R≤n) :
    absoluteTick R (absoluteAge R n)=n := by
  unfold absoluteTick absoluteAge
  omega

theorem observation_reward_clock (R T A : Nat) (n : Int)
    (hT : 6≤T) (hA : A∈roots R) (hb : (birth A).n≤n) :
    observedReward R T A (physicalAge A n)=
      if observeStart R T A≤n ∧ n<observeStart R T A+(T : Int) then 1 else 0 := by
  have ha := hA
  simp only [roots,List.mem_filter,decide_eq_true_eq] at ha
  have hstart := observeStart_ge_birth R T A hT ha.2.1 ha.2.2
  unfold observedReward
  have he : (observeAge R T A≤physicalAge A n ∧
      physicalAge A n<observeAge R T A+T) ↔
      observeStart R T A≤n ∧ n<observeStart R T A+(T : Int) := by
    unfold observeAge physicalAge
    omega
  by_cases h : observeStart R T A≤n ∧ n<observeStart R T A+(T : Int)
  · simp [h,he.mpr h]
  · simp [h,fun hh => h (he.mp hh)]

def debtDigit (inc : State → Nat) (D R T A t : Nat) : Nat :=
  (recordDebt (rootNet inc D R T A) (physicalAge A (absoluteTick R t))).toNat

theorem contact_debt_step (inc : State → Nat) (D R T A B t : Nat)
    (hT : 6≤T) (hA : A∈roots R) (hB : B∈roots R)
    (hc : Contact R T A B (absoluteTick R t))
    (hd : debtDigit inc D R T B t≤debtDigit inc D R T A t) :
    debtDigit inc D R T B (t+1)≤debtDigit inc D R T A (t+1) := by
  let n := absoluteTick R t
  let a := physicalAge A n
  let b := physicalAge B n
  let f := rootNet inc D R T A
  let g := rootNet inc D R T B
  have hclock : absoluteTick R (t+1)=n+1 := by unfold n absoluteTick; omega
  have ha : physicalAge A (absoluteTick R (t+1))=a+1 := by
    have h := hc.1
    rw [hclock]
    unfold a physicalAge
    change (birth A).n≤n at h
    omega
  have hb : physicalAge B (absoluteTick R (t+1))=b+1 := by
    have h := hc.2.1
    rw [hclock]
    unfold b physicalAge
    change (birth B).n≤n at h
    omega
  have hra := observation_reward_clock R T A n hT hA hc.1
  have hrb := observation_reward_clock R T B n hT hB hc.2.1
  have hs := contact_same_window_end R T A B hc.2.2.1
  rw [hs] at hra
  change observedReward R T A a = _ at hra
  change observedReward R T B b = _ at hrb
  have hrew := hra.trans hrb.symm
  have hx := hc.2.2.2
  change orbit A a=orbit B b at hx
  have hfa := rootNet_increment inc D R T A a
  have hgb := rootNet_increment inc D R T B b
  change f (a+1)-f a = _ at hfa
  change g (b+1)-g b = _ at hgb
  rw [hrew,hx] at hfa
  have hstep := hfa.trans hgb.symm
  have hda := recordDebt_nonneg f a
  have hdb := recordDebt_nonneg g b
  change (recordDebt g b).toNat≤(recordDebt f a).toNat at hd
  have hle : recordDebt g b≤recordDebt f a := by omega
  unfold debtDigit
  rw [ha,hb]
  change (recordDebt g (b+1)).toNat≤(recordDebt f (a+1)).toNat
  rw [recordDebt_succ,recordDebt_succ, hstep]
  have hmax : max 0 (recordDebt g b-(g (b+1)-g b))≤
      max 0 (recordDebt f a-(g (b+1)-g b)) := by
    by_cases h : recordDebt g b-(g (b+1)-g b)≤0
    · rw [Int.max_eq_left h]
      exact Int.le_max_left _ _
    · have h' : 0≤recordDebt f a-(g (b+1)-g b) := by omega
      rw [Int.max_eq_right (by omega : 0≤recordDebt g b-(g (b+1)-g b)),Int.max_eq_right h']
      omega
  omega

def debtScore (inc : State → Nat) (D R T A t : Nat) : Nat :=
  historyCode (roots R) (debtDigit inc D R T) A t

theorem debtScore_priority_step (inc : State → Nat) (D R T A B t : Nat)
    (hT : 6≤T) (hA : A∈roots R) (hB : B∈roots R)
    (hc : Contact R T A B (absoluteTick R t))
    (hp : Precedes (fun c => debtScore inc D R T c t) B A) :
    Precedes (fun c => debtScore inc D R T c (t+1)) B A := by
  have hle : debtScore inc D R T B t≤debtScore inc D R T A t := by
    simp only [Precedes] at hp
    omega
  have hd := historyCode_digit_le (roots R) (debtDigit inc D R T) A B t hA hle
  exact historyCode_priority_step (roots R) (debtDigit inc D R T) A B t hp
    (contact_debt_step inc D R T A B t hT hA hB hc hd)

def debtRank (inc : State → Nat) (D R T A t : Nat) : Nat :=
  ((roots R).filter (fun B => decide (Contact R T A B (absoluteTick R t) ∧
    Precedes (fun c => debtScore inc D R T c t) B A))).length

theorem debtRank_step (inc : State → Nat) (D R T A t : Nat)
    (hT : 6≤T) (hA : A∈roots R) :
    debtRank inc D R T A t≤debtRank inc D R T A (t+1) := by
  unfold debtRank
  apply filter_len_mono
  intro B hB h
  simp only [decide_eq_true_eq] at h ⊢
  exact ⟨contact_mono R T A B _ _ (by unfold absoluteTick; omega) h.1,
    debtScore_priority_step inc D R T A B t hT hA hB h.1 h.2⟩

theorem debtRank_mono (inc : State → Nat) (D R T A i j : Nat)
    (hT : 6≤T) (hA : A∈roots R) (hij : i≤j) :
    debtRank inc D R T A i≤debtRank inc D R T A j := by
  induction j with
  | zero => have h : i=0 := by omega; rw [h]; exact Nat.le_refl _
  | succ j ih =>
    by_cases h : i=j+1
    · rw [h]
    · exact Nat.le_trans (ih (by omega)) (debtRank_step inc D R T A j hT hA)

#print axioms NegativeMIN.historyCode_digit_le
#print axioms NegativeMIN.contact_debt_step
#print axioms NegativeMIN.debtRank_mono

end NegativeMIN
