import A166944.WindowControlsS

/-!
# The frontier alone gives the window, with no bound on `S`

`QuietReturn.quiet_return_no_proper_factors` needs the window condition

    `2 * isqrt (C + 1) < C - s`

at a terminal state. Round 9 recorded that this is the tree's ONLY route from a replay to
statements about `C_f +- 1`, hence to the record spacing, hence to `S`.

Six previous rounds assumed that producing this window required bounding `S` from above. It does
not. This file proves that the frontier `travel <= M/2` ALONE produces the window at `S = 0`,
with `S` entirely unbounded.

## The arithmetic

In canonical coordinates `C_f = (2M-2) + S` and `s_f = (M+2) + travel`, so at `S = 0` the window
condition is

    ((M + 2) + travel) + 2 * isqrt (2 * M - 1) < 2 * M - 2.

With `travel <= M/2` the left side is at most `(M+2) + M/2 + 2*isqrt(2M-1)`, so it suffices that

    (M + 2) + M/2 + 2 * isqrt (2 * M - 1) < 2 * M - 2,
    i.e.   2 * isqrt (2M-1) < M/2 - 4,

and since the left side is an integer this is `2 * isqrt(2M-1) <= M/2 - 5`.  That is
`two_isqrt_bound`, proved for `M >= 200` (the true boundary is far lower; `200` gives `omega`
comfortable margin).

Any divisor of an odd number is odd. `C_f` is even at every state (`IsMovingHorizonState` plus
`D_mod_two_eq_zero_of_two_le`), so `C_f + 1` is odd and `isqrt` applied there is the honest
integer root.
-/

namespace A166944Research

/-- **`isqrt` is monotone.** -/
theorem isqrt_mono {a b : Nat} (h : a ≤ b) : isqrt a ≤ isqrt b := by
  by_cases hle : isqrt a ≤ isqrt b
  · exact hle
  · exfalso
    have hlt : isqrt b < isqrt a := by omega
    have h1 : isqrt a * isqrt a ≤ a := isqrt_sq_le a
    have h2 : isqrt b + 1 ≤ isqrt a := by omega
    have h3 : (isqrt b + 1) * (isqrt b + 1) ≤ isqrt a * isqrt a := Nat.mul_le_mul h2 h2
    have h4 : b < (isqrt b + 1) * (isqrt b + 1) := lt_succ_isqrt b
    omega

/-- **`(k - 5)^2` lower bound, isolated so `omega` never sees a product.**
For `k >= 96`, `k*k >= 91*k + 5*k` and hence `(k-5)^2 = k^2 - 10k + 25 >= 81k + 25 > 16k + 4`.
Proved in the shifted form that avoids expanding the square. -/
theorem square_shift_bound {k : Nat} (hk : 96 ≤ k) :
    16 * k + 4 < (k - 5) * (k - 5) := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
  subst hj
  have hjbig : 91 ≤ j := by omega
  have hsq : 16 * j + 84 < j * j := by
    have h1 : 91 * j ≤ j * j := Nat.mul_le_mul_right _ hjbig
    omega
  have hsub : (j + 5 - 5) = j := by omega
  rw [hsub]
  omega

/-- **The key numeric bound: `2 * isqrt (2M-1) <= M/2 - 5` for `M >= 200`.**
By contradiction: if `M/2 - 4 <= 2*isqrt(2M-1)` then squaring gives
`(M/2-4)^2 <= 4*(2M-1) = 8M - 4`; but `square_shift_bound` says `(M/2-5)^2 > 8M - 4` honestly
only for the shifted variable, so we chain through `(M/2-4) = (M/2-5) + 1`. -/
theorem two_isqrt_bound {M : Nat} (hM : 200 ≤ M) :
    2 * isqrt (2 * M - 1) ≤ M / 2 - 5 := by
  have h1 : isqrt (2 * M - 1) * isqrt (2 * M - 1) ≤ 2 * M - 1 := isqrt_sq_le _
  by_cases hle : 2 * isqrt (2 * M - 1) ≤ M / 2 - 5
  · exact hle
  · exfalso
    have h3 : M / 2 - 4 ≤ 2 * isqrt (2 * M - 1) := by omega
    have hmul := Nat.mul_le_mul h3 h3
    have hsq : (2 * isqrt (2 * M - 1)) * (2 * isqrt (2 * M - 1))
        = 4 * (isqrt (2 * M - 1) * isqrt (2 * M - 1)) := by
      rw [Nat.mul_mul_mul_comm]
    -- upper: (M/2-4)^2 <= 8M-4
    have hupper : (M / 2 - 4) * (M / 2 - 4) ≤ 8 * M - 4 := by
      have h4 : 4 * (isqrt (2 * M - 1) * isqrt (2 * M - 1)) ≤ 4 * (2 * M - 1) :=
        Nat.mul_le_mul_left 4 h1
      omega
    -- lower: 8M - 4 < (M/2-4)^2 by square_shift_bound at k = M/2 - 4 + 5 = M/2 + 1... 
    -- use k = M/2 - 5 + 5 = M/2 shifted: set j = M/2 - 5, then M/2 - 4 = j + 1
    have hkbig : 96 ≤ M / 2 := by omega
    have hshift : 8 * M - 4 < (M / 2 - 5) * (M / 2 - 5) := by
      have := square_shift_bound hkbig
      omega
    -- (M/2-4)^2 = (M/2-5)^2 + 2*(M/2-5) + 1 > (M/2-5)^2, so upper < lower contradiction
    have hmono : (M / 2 - 5) * (M / 2 - 5) ≤ (M / 2 - 4) * (M / 2 - 4) := by
      have hle3 : M / 2 - 5 ≤ M / 2 - 4 := by omega
      exact Nat.mul_le_mul hle3 hle3
    omega

/-- **THE SHORT-CIRCUIT.**  `travel <= M/2` and `M >= 200` give the window inequality at
`S = 0`, in additive form.  The proof is an explicit chain rather than `omega`, because `omega`
will not carry the relation `M = 2*k + r` into the goal. -/
theorem frontier_gives_window_at_zero {M travel : Nat} (hM : 200 ≤ M)
    (htrav : travel ≤ M / 2) :
    ((M + 2) + travel) + 2 * isqrt ((2 * M - 2) + 1) < (2 * M - 2) := by
  have hq : 2 * isqrt (2 * M - 1) ≤ M / 2 - 5 := two_isqrt_bound hM
  have hrw : (2 * M - 2) + 1 = 2 * M - 1 := by omega
  rw [hrw]
  -- The key sum: travel + 2*isqrt(2M-1) <= M/2 + (M/2 - 5) = M - 5
  have hsum : travel + 2 * isqrt (2 * M - 1) ≤ M - 5 := by omega
  -- so the left side is at most (M+2) + (M-5) = 2M - 3 < 2M - 2
  have hleft : ((M + 2) + travel) + 2 * isqrt (2 * M - 1) = (M + 2) + (travel + 2 * isqrt (2 * M - 1)) := by
    omega
  rw [hleft]
  omega

/-! ## Axiom audit -/

#print axioms isqrt_mono
#print axioms square_shift_bound
#print axioms two_isqrt_bound
#print axioms frontier_gives_window_at_zero

end A166944Research
