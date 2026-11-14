import A166944.DNodes

/-!
# The first-hit map, as a divisibility statement

At a state `(s, C)` with `D s = C` the recurrence is quiet until the first index
where a `gcd` becomes nontrivial. `DNodes` records the *value* at such an index.
This file records the complementary half: a **sufficient** condition for the hit
to be *at or before* a given index, phrased purely as divisibility.

The shape is the one Shevelev uses (arXiv:0911.5478, eqns (3.7)-(3.10)) and the
one Rowland's Lemma 1 uses in the single-`gcd` case: at an odd index `j`,
if `j - 2` shares a factor with `C + 1`, then `j` cannot be a unit index, so the
first hit is at most `j`.

## What is and is not claimed

`odd_tail_not_dvd` and `even_tail_not_dvd` are the contrapositives of the unit
tail from `moving_horizon_first_hit_map`, so they need no new mathematics: they
restate "quiet" as "coprime".

`horizon_dvd_forces_hit` composes them: at an odd index `j` in the tail, a common
divisor `> 1` of `j - 2` and `C + 1` forces `j` to be at or after the hit. This
is the *upper* bound half of a first-hit formula.

The *lower* bound half -- "no hit strictly between `s` and `j`" -- is exactly the
minimality argument that Shevelev supplies with `q = spf (C + 1)` and that this
repository does **not** yet have. That is the transplant obligation, and this
file is careful not to assume it.
-/

namespace A166944Research

/-- Contrapositive of the odd half of the unit tail: if an odd index strictly
inside the tail has a nontrivial common divisor with `C + 1`, the hypothesis
that it is a unit index fails. -/
theorem odd_tail_not_dvd {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r)
    (hodd : j % 2 = 1) (hbad : Nat.gcd (j - 2) (C + 1) ≠ 1) : False := by
  have htail := (moving_horizon_first_hit_map hstep).elim
    (fun h => h.2.2.2 j hsj hjr) (fun h => h.2.2.2 j hsj hjr)
  exact hbad (htail.2 hodd)

/-- The even companion. -/
theorem even_tail_not_dvd {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r)
    (heven : j % 2 = 0) (hbad : Nat.gcd j (C - 1) ≠ 1) : False := by
  have htail := (moving_horizon_first_hit_map hstep).elim
    (fun h => h.2.2.2 j hsj hjr) (fun h => h.2.2.2 j hsj hjr)
  exact hbad (htail.1 heven)

/-- **The divisor form of the first hit, odd branch.**  At an odd index `j > s`
which is not the hit itself, any common divisor of `j - 2` and `C + 1` is `1`.
Equivalently: `j` is at or after the hit. -/
theorem odd_hit_le_of_dvd {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j)
    (hodd : j % 2 = 1) (hv2 : 2 ≤ v) (hvj : v ∣ j - 2) (hvC : v ∣ C + 1) :
    r ≤ j := by
  -- Suppose the hit is strictly after j; then j is an interior unit index.
  refine Nat.le_of_not_lt fun hlt => ?_
  have hjr : j < r := hlt
  have hdvd : v ∣ Nat.gcd (j - 2) (C + 1) := Nat.dvd_gcd hvj hvC
  have hne : Nat.gcd (j - 2) (C + 1) ≠ 1 := by
    intro h1
    have hdiv1 : v ∣ 1 := h1 ▸ hdvd
    have hle1 : v ≤ 1 := Nat.le_of_dvd (Nat.one_pos) hdiv1
    omega
  exact odd_tail_not_dvd hstep hsj hjr hodd hne

/-- **The divisor form of the first hit, even branch.** -/
theorem even_hit_le_of_dvd {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j)
    (heven : j % 2 = 0) (hv2 : 2 ≤ v) (hvj : v ∣ j) (hvC : v ∣ C - 1) :
    r ≤ j := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hjr : j < r := hlt
  have hdvd : v ∣ Nat.gcd j (C - 1) := Nat.dvd_gcd hvj hvC
  have hne : Nat.gcd j (C - 1) ≠ 1 := by
    intro h1
    have hdiv1 : v ∣ 1 := h1 ▸ hdvd
    have hle1 : v ≤ 1 := Nat.le_of_dvd (Nat.one_pos) hdiv1
    omega
  exact even_tail_not_dvd hstep hsj hjr heven hne

/-- **The hit lands on the first divisible index.**  Combining the two branches:
if `j` is an odd index in `(s, r]` style position whose `j - 2` shares a divisor
`v >= 2` with `C + 1`, then `r <= j`.  This is stated with the parity
hypothesis explicit, since the caller knows which branch it is in. -/
theorem first_hit_le_of_dvd {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j)
    (hodd : j % 2 = 1) (hv2 : 2 ≤ v) (hvj : v ∣ j - 2) (hvC : v ∣ C + 1) :
    r ≤ j :=
  odd_hit_le_of_dvd hstep hsj hodd hv2 hvj hvC

/-- The same statement in the horizon-only form: if `C + 1` has a divisor `v >= 2`
and `j - 2` is a multiple of `v`, the hit cannot be strictly after `j`. -/
theorem horizon_dvd_forces_hit {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j)
    (hodd : j % 2 = 1) (hv2 : 2 ≤ v) (hvC : v ∣ C + 1) (hvj : v ∣ j - 2) :
    r ≤ j :=
  odd_hit_le_of_dvd hstep hsj hodd hv2 hvj hvC

end A166944Research
