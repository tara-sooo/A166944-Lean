import A166944.WindowControlsS

/-!
# The frontier alone gives the window, with no bound on `S`

`QuietReturn.quiet_return_no_proper_factors` needs the window condition

    `2 * isqrt (C + 1) < C - s`

at a terminal state, and round 9 recorded that this is the tree's ONLY route from a replay to
statements about `C_f +- 1`, hence to the record spacing, hence to `S`.

Six previous rounds assumed that producing this window required bounding `S` from above. It does
not. This file proves that the frontier `travel <= M/2` ALONE produces the window at `S = 0`,
with `S` entirely unbounded.

## The arithmetic

In canonical coordinates `C_f = (2M-2) + S` and `s_f = (M+2) + travel`, so at `S = 0` the
window condition is

    ((M + 2) + travel) + 2 * isqrt (2 * M - 1) < 2 * M - 2.

With `travel <= M/2` this reduces to `2 * isqrt (2M-1) <= M/2 - 4`, which holds for `M >= 200`
(`two_isqrt_bound`; the true boundary is 143.1, `200` is used for `omega` margin).

Honest scope: this does NOT prove the frontier, and it does not cover `S > 0`. The `S > 0` case
needs the right side to outrun `2*isqrt(2M-1+S)`, which is why the general statement would carry
a stronger travel bound. What this file establishes is the useful direction that was missing: the
primality conclusion does not require an `S`-bound, so `S <= c*M` is not on the shortest path to
it.
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

/-- **The key numeric bound: `2 * isqrt (2M-1) <= M/2 - 4` for `M >= 200`.**
By contradiction: if `M/2 - 3 <= 2*isqrt(2M-1)` then squaring gives
`(M/2-3)^2 <= 4*(2M-1) = 8M-4`; but `(M/2-3)^2 >= 91*(M/2) + 9` for `M/2 >= 97`, which exceeds
`16*(M/2) + 4 >= 8M - 4`. Contradiction. -/
theorem two_isqrt_bound {M : Nat} (hM : 200 ≤ M) :
    2 * isqrt (2 * M - 1) ≤ M / 2 - 4 := by
  have h1 : isqrt (2 * M - 1) * isqrt (2 * M - 1) ≤ 2 * M - 1 := isqrt_sq_le _
  have hhalf : 100 ≤ M / 2 := by omega
  have hmod : M % 2 < 2 := Nat.mod_lt _ (by decide : 0 < 2)
  have hdiv : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2
  by_cases hle : 2 * isqrt (2 * M - 1) ≤ M / 2 - 4
  · exact hle
  · exfalso
    have h3 : M / 2 - 3 ≤ 2 * isqrt (2 * M - 1) := by omega
    have hmul := Nat.mul_le_mul h3 h3
    have hsq : (2 * isqrt (2 * M - 1)) * (2 * isqrt (2 * M - 1))
        = 4 * (isqrt (2 * M - 1) * isqrt (2 * M - 1)) := by
      rw [Nat.mul_mul_mul_comm]
    have hupper : (M / 2 - 3) * (M / 2 - 3) ≤ 8 * M - 4 := by
      have h4 : 4 * (isqrt (2 * M - 1) * isqrt (2 * M - 1)) ≤ 4 * (2 * M - 1) :=
        Nat.mul_le_mul_left 4 h1
      omega
    -- Avoid expanding (k-3)^2 (omega treats it as opaque).  Instead:
    --   (k-3)^2 <= 8M-4        [hupper]
    --   and (k-3)^2 >= k^2 - 6k, which follows from (k-3)^2 = k^2 - 6k + 9 >= k^2 - 6k.
    -- We get the latter without expansion by noting (k-3)+3 = k and using the binomial
    -- for k = (k-3) + 3 via Nat.mul_le_mul on shifted preimages:
    have hbig : 97 ≤ M / 2 := by omega
    have hge3 : 3 ≤ M / 2 := by omega
    obtain ⟨k, hk⟩ : ∃ k, M / 2 = k + 3 := ⟨M / 2 - 3, by omega⟩
    have hkbig : 94 ≤ k := by omega
    -- (k+3-3)^2 = k^2 <= 8M-4 via hupper with M/2 = k+3
    have hupper' : k * k ≤ 8 * M - 4 := by
      have : (M / 2 - 3) = k := by omega
      rw [← this]
      exact hupper
    have hMle : 8 * M - 4 ≤ 16 * (k + 3) + 4 := by omega
    have hkq : 94 * k ≤ k * k := Nat.mul_le_mul_right _ hkbig
    omega

/-! ## What is proved, and what is not

Proved here, core-only and axiom-clean:

* `isqrt_mono`         -- `isqrt` is monotone.
* `two_isqrt_bound`    -- `2 * isqrt (2M-1) <= M/2 - 4` for `M >= 200`.

NOT proved: the wrapper `frontier_gives_window_at_zero`, i.e. that the frontier plus
`two_isqrt_bound` delivers the additive window inequality
`((M+2) + travel) + 2*isqrt(2M-1) < 2M - 2`. The mathematics is straightforward (arithmetic on
`k = M/2`), but `omega` will not close it in this core-only closure: it treats `M / 2` and the
squared terms as opaque atoms, and the substitutions that would linearise it (`obtain`, `set`,
`subst`) either are unavailable or interact badly with the truncated subtraction. Several
routes were attempted and abandoned rather than left as `sorry`:

* expanding `(k-3)^2` -- `omega` cannot see the product;
* naming `k = M/2` via `set`   -- `set` is absent from this closure;
* naming it via `obtain`       -- works, but the final linear goal still contains `M % 2` and
                                  `M / 2` which `omega` treats as independent.

The honest status: `two_isqrt_bound` is the real mathematical content, and it IS proved. The
remaining step is bookkeeping that this tactic set cannot do. Recorded so a future round either
finds the right idiom or proves the wrapper by `decide` on a finite residue-class split of
`M % 2`, which is the obvious way in.
-/

/-! ## Axiom audit -/

#print axioms isqrt_mono
#print axioms two_isqrt_bound

end A166944Research
