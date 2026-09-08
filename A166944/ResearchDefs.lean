import Init.Data.Nat.Gcd
import Init.WF

/-!
# Ultra-lightweight A166944 recurrence definitions

This file mirrors the recurrence-side mathematical definitions from the pinned
Formal Conjectures source for OEIS A166944, but deliberately stays on the Lean
standard-library path.

Purpose: fast interactive proof search on Termux/Android. In particular, this
file does NOT import Mathlib, Mathlib prime definitions, Formal Conjectures, or
FormalConjecturesUtil.

The primality-side target is separated into `A166944/TargetDefs.lean` so that
early recurrence/invariant work does not pay that import cost.

Pinned upstream source:
google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75
FormalConjectures/OEIS/166944.lean
-/

namespace A166944Research

def a : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let prev := a (n + 1)
    let idx := n + 2
    if idx % 2 = 0 then prev + Nat.gcd idx prev
    else prev + Nat.gcd (idx - 2) prev

def d (n : Nat) : Nat := a n - a (n - 1)

def D (n : Nat) : Nat := a n - n

def B (n : Nat) : Nat := a n - (2 * n - 2)

/-- A state whose next event can be searched on the bounded horizon `s < j ≤ C`. -/
def IsMovingHorizonState (s C : Nat) : Prop :=
  2 ≤ s ∧ D s = C ∧ s < C

/- An exact recurrence transition for the D-coordinate at index n. -/
def IsDTransition (n C C' : Nat) : Prop :=
  2 ≤ n ∧
    C' + 1 = C +
      (if n % 2 = 0 then Nat.gcd n (C - 1)
      else Nat.gcd (n - 2) (C + 1))

/- A genuine recurrence path from a previous record to a larger increment.
   The cap applies only to strict intermediate indices; the endpoint is delta. -/
def IsCappedDPath (p s M delta : Nat) : Prop :=
  p < s ∧ d s = delta ∧ M < delta ∧
    (∀ j : Nat, p < j → j < s → d j ≤ M) ∧
    (∀ j : Nat, p < j → j ≤ s →
      IsDTransition j (D (j - 1)) (D j))

/-- One first-event transition, including the unit tail and the next state. -/
def IsMovingHorizonStep (s C r C' : Nat) : Prop :=
  IsMovingHorizonState s C ∧ s < r ∧ r ≤ C ∧ 1 < d r ∧
    (∀ j : Nat, s < j → j < r → d j = 1) ∧
    D (r - 1) = C ∧ C' = D r ∧ C + 2 ≤ C' ∧
    IsMovingHorizonState r C'

/-- A finite chain of first-event transitions. -/
def HasMovingHorizonChain (s C : Nat) : Nat → Prop
  | 0 => IsMovingHorizonState s C
  | Nat.succ q =>
      ∃ r C', IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonChain r C' q

/- A finite old-event prefix with named endpoint, slack cap, and no
   fundamental state. E and T record event sizes and gap-plus-one terms. -/
def HasMovingHorizonCappedOldPath (M s C sf Cf E T : Nat) : Nat → Prop
  | 0 =>
      s = sf ∧ C = Cf ∧ IsMovingHorizonState s C ∧ C - s ≤ M ∧
        B s ≠ 2 ∧ E = 0 ∧ T = 0
  | Nat.succ q =>
      IsMovingHorizonState s C ∧ C - s ≤ M ∧ B s ≠ 2 ∧
        ∃ r C' E' T', IsMovingHorizonStep s C r C' ∧ d r ≤ M ∧
          C' - r ≤ M ∧ B r ≠ 2 ∧ E = E' + d r ∧
          T = T' + (r - s + 1) ∧
          HasMovingHorizonCappedOldPath M r C' sf Cf E' T' q

/-- A finite close-old segment with explicit envelope excess and Nat sums. -/
def HasMovingHorizonCloseChain (P s C X E T : Nat) : Nat → Prop
  | 0 => IsMovingHorizonState s C ∧ B s + 2 = 2 * P + X ∧ E = 0 ∧ T = 0
  | Nat.succ q =>
      ∃ r C' X' E' T', IsMovingHorizonStep s C r C' ∧
        d r ≤ P ∧ r - s ≤ d r + 2 ∧
        B s + 2 = 2 * P + X ∧ B r + 2 = 2 * P + X' ∧
        E = E' + d r ∧ T = T' + (r - s + 1) ∧
        HasMovingHorizonCloseChain P r C' X' E' T' q

/- A quotient-only projection of consecutive regenerated record steps with a
   fixed quotient c. -/
def HasSameQuotientRegenerationChain (P c : Nat) : Nat → Prop
  | 0 => True
  | Nat.succ q =>
      ∃ e : Nat, P < e ∧ e * (c + 1) + 1 = P * (c + 2) ∧
        HasSameQuotientRegenerationChain e c q

/-- A candidate last nontrivial increment before `m`; this is only a predicate.
Existence is proved separately when the endpoint and earlier increment permit it.
-/
def IsLastNontrivialBefore (rho m : Nat) : Prop :=
  2 ≤ rho ∧ rho < m ∧ 1 < d rho ∧
    ∀ j : Nat, rho < j → j ≤ m → d j = 1

/-- A finite ordered chain of nontrivial increments; this predicate asserts no
existence beyond the explicit chain supplied to a theorem using it. -/
def HasNontrivialChain (start finish : Nat) : Nat → Prop
  | 0 => start ≤ finish
  | Nat.succ s =>
      ∃ r : Nat, start < r ∧ r ≤ finish ∧ 1 < d r ∧
        HasNontrivialChain r finish s

def IsDifferenceRecord (R : Nat) : Prop :=
  ∃ n : Nat, 2 ≤ n ∧ d n = R ∧ ∀ k : Nat, 2 ≤ k → k < n → d k < R

/- A history envelope asserted only on indices before `s`. -/
def HasHistoryEnvelopeBefore (s : Nat) : Prop :=
  ∀ k M : Nat, 2 ≤ k → k < s →
    (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ M) →
      a k + 4 ≤ 2 * k + 2 * M

/-- `P` is an attained running maximum through `k`.
The occurrence is intentionally existential; the first occurrence is extracted
by a separate theorem so that it can be used as a strict difference record. -/
def IsAttainedPreviousMaximum (P k : Nat) : Prop :=
  (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ P) ∧
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P

end A166944Research
