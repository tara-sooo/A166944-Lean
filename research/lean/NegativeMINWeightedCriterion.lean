import NegativeMINCore
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Exact real-scale target (Mathlib adapter; awaiting pinned Mathlib check)

This file preserves the concrete exponents in 5a22180 §§4–7, used again
in 2fdbf53 and 26ad4ea. The verified integer core is separate.
No theorem is admitted here. The two analytic propositions below are
explicit research obligations, NOT established hypotheses of the final goal.
-/
set_option autoImplicit false
noncomputable section
namespace NegativeMIN

theorem oddPrime_iff_mathlib (p : Nat) :
    oddPrime p = true ↔ p.Prime ∧ 3 ≤ p := by
  constructor
  · intro h
    have hb := oddPrime_bounds p h
    refine ⟨Nat.prime_def_lt'.2 ⟨by omega, ?_⟩, hb.1⟩
    intro m hm hlt hdvd
    exact oddPrime_no_small_divisor p m h hm hlt (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨hp, h3⟩
    have ho := hp.mod_two_eq_one_iff_ne_two.2 (by omega)
    simp only [oddPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨h3, ho⟩, ?_⟩
    intro m hm
    by_cases hlt : m < 2
    · exact Or.inl hlt
    · exact Or.inr (fun hz => (Nat.prime_def_lt'.1 hp).2 m (by omega)
        (List.mem_range.mp hm) (Nat.dvd_of_mod_eq_zero hz))

def TwinPrimeInfinitude : Prop :=
  ∀ B : Nat, ∃ p : Nat, B < p ∧ p.Prime ∧ (p - 2).Prime

theorem twinPrimeInfinitude_of_unboundedCenters
    (h : UnboundedTwinCenters) : TwinPrimeInfinitude := by
  intro B
  obtain ⟨x, hx, ht⟩ := h B
  refine ⟨x + 1, by omega, (oddPrime_iff_mathlib _).1 ht.2.2 |>.1, ?_⟩
  have hp := (oddPrime_iff_mathlib _).1 ht.2.1 |>.1
  simpa only [show x + 1 - 2 = x - 1 by omega] using hp

def L (R : Nat) : ℝ := Real.log (R : ℝ)
def scale (R : Nat) : ℝ := (L R) ^ (-(1/4 : ℝ))
def horizon (R : Nat) : Nat :=
  Nat.floor ((Nat.ceil (Real.sqrt (2 * (R : ℝ) + 1)) : ℝ) *
    Real.exp (-((L R) ^ (1/2 : ℝ))))
def capacity (R : Nat) : Nat := Nat.floor ((L R) ^ (21/10 : ℝ))
def y0 (R : Nat) : Nat := Nat.ceil (Real.exp ((L R) ^ (9/20 : ℝ)))
def y1 (R : Nat) : Nat := Nat.ceil (Real.exp ((L R) ^ (17/20 : ℝ)))
def z (R : Nat) : Nat := max 7 (Nat.floor (Real.sqrt (Real.log (L R))))
def smallPeriod (R : Nat) : Nat :=
  2 * ((List.range (z R + 1)).filter oddPrime).prod
def relayBudget (R : Nat) : Nat :=
  Nat.floor (((1/10 : ℝ) * Real.log (L R)) /
    (Real.log (2 * ((smallPeriod R : ℝ) + 1)) + 2 * Real.log (2 * Real.log (L R))))
def windowOverlap (R : Nat) : Nat :=
  let T := horizon R
  let W := windowWidth T
  (3*T+6+W-1)/W+2

def eta (R : Nat) (deathAge : Nat → Nat) : ℝ :=
  (liveTicks deathAge R (horizon R) : ℝ) / ((roots R).length : ℝ) /
    (horizon R : ℝ)

def prefixMean (R : Nat) (deathAge : Nat → Nat) : ℝ :=
  Real.exp (-((L R) ^ (3/5 : ℝ))) / ((relayBudget R : ℝ) + 1) *
    ((narrowCount deathAge R (horizon R) (z R) (y0 R) : ℝ) /
      ((roots R).length : ℝ)) +
    (mediumCharge deathAge R (horizon R) (y0 R) (y1 R) : ℝ) /
      ((roots R).length : ℝ) / (horizon R : ℝ)

def twinMass (R : Nat) : ℝ :=
  (windowOverlap R : ℝ) * (capacity R : ℝ) *
    (twinCount R (horizon R) : ℝ) / ((roots R).length : ℝ)

def LittleOScale (f : Nat → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ R0 : Nat, ∀ R : Nat, R0 ≤ R →
    |f R| ≤ eps * scale R

/-- OPEN: equations (14)–(15), with the explicit exponents above.
Uniform across actual irreversible policies, including pre-window capping. -/
def WeightedEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ err : Nat → ℝ, LittleOScale err ∧
    ∃ R0 : Nat, ∀ R : Nat, R0 ≤ R → ∀ deathAge : Nat → Nat,
      FullCapped deathAge R (horizon R) (capacity R) →
        eta R deathAge ≤ twinMass R + C * prefixMean R deathAge + err R

/-- OPEN: cheap cumulative survival on an unbounded set of genuine slabs.
The prefix cost is averaged over ALL original roots, including discarded ones. -/
def CheapSurvival : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ good : Nat → Prop, ∃ policy : Nat → Nat → Nat,
    (∀ B : Nat, ∃ R : Nat, B ≤ R ∧ good R) ∧
    (∀ R : Nat, good R → FullCapped (policy R) R (horizon R) (capacity R)) ∧
    (∀ R : Nat, good R → c * scale R ≤ eta R (policy R)) ∧
    (∀ eps : ℝ, 0 < eps → ∃ R0 : Nat, ∀ R : Nat, R0 ≤ R → good R →
        |prefixMean R (policy R)| ≤ eps * scale R)

/-- Elementary asymptotic geometry, still to be discharged in Mathlib. -/
def ScaleGeometry : Prop :=
  ∀ B : Nat, ∃ R0 : Nat, ∀ R : Nat, R0 ≤ R →
    B + 3 * horizon R + 6 < R ∧ 0 < scale R

/-- The exact research target, not an axiom and not a proved theorem. -/
def ExactWeightedCriterion : Prop :=
  WeightedEstimate → CheapSurvival → TwinPrimeInfinitude

/-- Candidate real-scale extraction, with its elementary geometry obligation
explicit. The unchanged exact target above must still be closed. -/
theorem exactWeightedCriterion_of_geometry
    (hg : ScaleGeometry) : ExactWeightedCriterion := by
  intro he hs
  apply twinPrimeInfinitude_of_unboundedCenters
  intro B
  obtain ⟨C, hC, err, hErr, R0, hEst⟩ := he
  obtain ⟨c, hc, good, policy, hUnbounded, hCap, hLow, hCheap⟩ := hs
  let eps : ℝ := c / (4 * (C + 1))
  have hden : 0 < 4 * (C + 1) := by linarith
  have heps : 0 < eps := div_pos hc hden
  obtain ⟨R1, hErr1⟩ := hErr (c / 4) (by linarith)
  obtain ⟨R2, hCheap2⟩ := hCheap eps heps
  obtain ⟨R3, hGeo⟩ := hg B
  obtain ⟨R, hR, hGood⟩ := hUnbounded (max (max R0 R1) (max R2 R3))
  have h0 : R0 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have h1 : R1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have h2 : R2 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have h3 : R3 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hloc := (hGeo R h3).1
  have hScale := (hGeo R h3).2
  have hup := hEst R h0 (policy R) (hCap R hGood)
  have hlo := hLow R hGood
  have hcost : prefixMean R (policy R) ≤ eps * scale R :=
    le_trans (le_abs_self _) (hCheap2 R h2 hGood)
  have herr : err R ≤ (c/4) * scale R :=
    le_trans (le_abs_self _) (hErr1 R h1)
  have heq : (C + 1) * eps = c / 4 := by
    dsimp [eps]
    field_simp [ne_of_gt hden, show C + 1 ≠ 0 by linarith]
  have hce : C * eps ≤ c/4 := by linarith
  have hcst := mul_le_mul_of_nonneg_left hcost hC
  have hce' := mul_le_mul_of_nonneg_right hce hScale.le
  have hcst' : C * prefixMean R (policy R) ≤ (c/4) * scale R := by
    rw [← mul_assoc] at hcst
    exact le_trans hcst hce'
  have hpos : 0 < c * scale R := mul_pos hc hScale
  have hnz : twinCount R (horizon R) ≠ 0 := by
    intro hz
    simp [twinMass, hz] at hup
    linarith
  unfold twinCount at hnz
  generalize hl : twinSites R (horizon R) = xs at hnz
  cases xs with
  | nil => simp at hnz
  | cons x xs =>
    have hm : x ∈ twinSites R (horizon R) := by rw [hl]; simp
    simp only [twinSites, List.mem_filter, decide_eq_true_eq] at hm
    have h := hm.2.1
    exact ⟨x, by omega, hm.2.2⟩

#print axioms NegativeMIN.oddPrime_iff_mathlib
#print axioms NegativeMIN.twinPrimeInfinitude_of_unboundedCenters
#print axioms NegativeMIN.exactWeightedCriterion_of_geometry
end NegativeMIN
