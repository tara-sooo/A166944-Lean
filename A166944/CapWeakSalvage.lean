import A166944.Isqrt

/-!
# Salvage: the three true lemmas from the capweak attempt

These are the parts of the abandoned `C <= 2*M` weakening that are **true
independently of the false premise**. Kept here so they can be lifted into the
tree; nothing here mentions `C <= 2*M`.

* `sq_expand`    -- the binomial square, core-only
* `sq_scale`, `two_mul_sq`, `four_sq`, `square_mono`, `lt_of_sq_lt_sq`
                 -- small square helpers used by `numeric_core`'s consumers
* `numeric_core` -- the numeric slack, threshold exactly `M >= 143`
* `window_helper`-- the window bound, from cap (B) and `2*M <= C+2` only

The tactic idioms are documented in `REPORT.md`. Summary: `ring`, `nlinarith`,
`linear_combination`, `set`, `by_contra`, `gcongr`, `positivity` are all absent;
`ac_rfl` **is** present but is not a `ring` (no distributivity), so every
polynomial identity here is done as `rw`-into-distributive-form then `omega`.
-/

namespace A166944Research

/-- **`sq_expand`**: the binomial square, distributively.  `ac_rfl` cannot do
this (it has no distributivity), and `ring`/`nlinarith` are absent, so the
`rw` chain into `a*b + a*b + b*b` form is what makes the goal linear for
`omega`. -/
theorem sq_expand (a b : Nat) : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  omega

/-- **`sq_scale`**: a product square is the product of squares. -/
theorem sq_scale (c d : Nat) : (c*d)*(c*d) = (c*c)*(d*d) := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-- **`two_mul_sq`**: `(2*q)^2 = 4*q^2`. -/
theorem two_mul_sq (q : Nat) : (2*q)*(2*q) = 4*(q*q) := by
  rw [Nat.two_mul q, sq_expand q q]
  omega

/-- **`four_sq`**: `(4*t)^2 = 16*t^2`. -/
theorem four_sq (t : Nat) : (4*t)*(4*t) = 16*(t*t) := by
  rw [sq_scale 4 t, show (4 : Nat) * 4 = 16 from by decide]

/-- **`square_mono`**: squaring is monotone on `Nat`. -/
theorem square_mono {a b : Nat} (h : a <= b) : a*a <= b*b :=
  Nat.mul_self_le_mul_self h

/-- **`lt_of_sq_lt_sq`**: strict monotonicity of squaring.  The core closure has
no `Nat.lt_of_mul_self_lt_mul_self`; this is trichotomy plus the monotone
`Nat.mul_self_le_mul_self`. -/
theorem lt_of_sq_lt_sq {a b : Nat} (h : a*a < b*b) : a < b := by
  by_cases hab : a < b
  · exact hab
  · exfalso
    have hba : b <= a := by omega
    have hs : b*b <= a*a := Nat.mul_self_le_mul_self hba
    omega

/-- **`numeric_core`**: the numeric slack.  The threshold `143` is exact:
`16*(8*143+4) = 18368 < 18496 = 136*136`, while at `M = 142` one has
`18240 > 18225`, so the inequality fails.  (The original `b_tight` used `968`;
this is a strict improvement of the numeric constant.) -/
theorem numeric_core (M : Nat) (hM : 143 <= M) : 16 * (8*M + 4) < (M - 7) * (M - 7) := by
  have hMsub : M = 143 + (M - 143) := by omega
  have h136 : M - 7 = 136 + (M - 143) := by omega
  have hsq : (M - 7) * (M - 7) = 18496 + 272*(M - 143) + (M - 143)*(M - 143) := by
    rw [h136, sq_expand 136 (M - 143)]
    rw [show (136 : Nat) * 136 = 18496 from by decide]
    rw [show 2 * (136 * (M - 143)) = 272 * (M - 143) from by omega]
  have hl : 16 * (8*M + 4) = 18368 + 128*(M - 143) := by
    rw [hMsub]
    omega
  rw [hsq, hl]
  have hk : 0 <= (M - 143) * (M - 143) := Nat.zero_le _
  omega

/-- **`window_helper`**: cap (B) plus the lower horizon cap put `M-7` inside
`4*(C-s)`.  The truncated subtraction is the trap; distributing the `4` first
(`Nat.mul_sub_left_distrib`, unconditional for `Nat`) makes it linear. -/
theorem window_helper (M s C : Nat) (hM : 7 <= M) (h : 4*s + 1 <= 7*M)
    (hlo : 2*M <= C + 2) : M - 7 <= 4 * (C - s) := by
  have hsC : s <= C := by omega
  rw [Nat.mul_sub_left_distrib]
  omega

#print axioms sq_expand
#print axioms sq_scale
#print axioms two_mul_sq
#print axioms four_sq
#print axioms square_mono
#print axioms lt_of_sq_lt_sq
#print axioms numeric_core
#print axioms window_helper

end A166944Research

/-!
## Verified status (2026-11-16)

Core-only build matching CI: exit 0, 0 errors, 0 warnings, no `sorry`/`admit`/`axiom`.
Axiom audit: `square_mono` needs nothing; `sq_scale` and `four_sq` need only `propext`; the rest
need `propext` and `Quot.sound`. No new axiom anywhere.

These are the true parts of an ABANDONED attempt to weaken cap (A) from `C <= 3M+4` to
`C <= 2M`. That weakening is FALSE -- see `THE_MISSING_INPUT_CORRECTION.md` -- so no declaration
here mentions it. The lemmas are reusable on their own terms:
`numeric_core`'s threshold `143` is exact (at `142` the two sides are `18240` and `18225`), and it
beats `b_tight`'s current `968`.

Tactic facts established while proving these, worth knowing before the next attempt in this
closure: `ring`, `nlinarith`, `linear_combination`, `set`, `by_contra`, `gcongr`, `positivity`
are all ABSENT; `ac_rfl` IS present but is an AC normaliser, not a `ring` -- it will not expand a
square. The working binomial idiom is
`rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]; omega`, where the order matters:
without `Nat.add_mul` omega sees a product of compound atoms, and without `Nat.mul_comm b a` it
sees two distinct atoms it cannot equate. Beware `Nat.lt_of_mul_lt_mul_left`, which pulls in
`Classical.choice`.
-/
