import A166944.QuietReturn

-- NOTE for the v4.29 transplant: the two theorems that mention `Nat.sqrt`
-- (`sqrt_supplies_quantum`, `long_quiet_gap_of_short_travel_sqrt_free`) are kept
-- here for the v4.33.1 library, where the root exists. A v4.29 build should use
-- only `two_mul_sqrt_lt_gap_of_short_travel`, which never mentions it.

/-!
# Removing `Nat.sqrt` from the transport lemma

`long_quiet_gap_of_short_travel` in `Sol_target_of_travel.lean` concludes
`2 * Nat.sqrt (C + 1) < C - s`, and that is the only place `Nat.sqrt` appears in
the whole solution. Lean v4.29.0-rc3 -- the environment of the Twin Prime
Conjecture mission on Prove2Me -- has no `Init.Data.Nat.Sqrt`, so that file does
not build there.

The root enters the original proof in exactly three places:
`q := Nat.sqrt (C + 1)`, `hq2 : q * q <= C + 1` (`Nat.sqrt_le`), and the
derivation of `q < M / 8`. Everything else is arithmetic on `q`. So the lemma can
be restated with an explicit `q` carrying the two facts the root supplies, and
then no lemma has to be reproved -- the original proof text goes through
unchanged with `q` named by the caller instead of by `Nat.sqrt`.

This file provides that restatement, and a helper that produces the `q` from
`Nat.sqrt` when the root *is* available, so the two forms are interchangeable.
-/

namespace A166944Research

/-- **Square-root-free transport bound.**

Same statement and same proof as `long_quiet_gap_of_short_travel`, with `Nat.sqrt`
replaced by an explicit `q` satisfying the two facts the root supplies. Under
`968 <= M`, `M + 2 <= s`, `2 * (s - (M + 2)) <= M`, `2 * M - 2 <= C` and
`C <= 3 * M + 4`, any `q` with `q * q <= C + 1` yields `2 * q < C - s`.

The `q < M / 8` hypothesis of the first attempt is *not* needed and was the reason
that attempt failed: the original proof derives `q < b` from `q * q <= C + 1`
itself, by contradiction, using `b * b <= q * q`. -/
theorem two_mul_sqrt_lt_gap_of_short_travel {M s C q : Nat}
    (hM : 968 ≤ M) (hs : M + 2 ≤ s) (htravel : 2 * (s - (M + 2)) ≤ M)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4)
    (hq2 : q * q ≤ C + 1) :
    2 * q < C - s := by
  let b := M / 8
  have hb : 121 ≤ b := by omega
  have hb2 := Nat.mul_le_mul_right b hb
  have hqb : q < b := by
    by_cases h : q < b
    · exact h
    · have hsq := Nat.mul_le_mul (show b ≤ q by omega) (show b ≤ q by omega)
      omega
  change 2 * q < C - s
  omega

/-- When `Nat.sqrt` is available it supplies the hypothesis of the lemma above. -/
theorem sqrt_supplies_quantum {C : Nat} : Nat.sqrt (C + 1) * Nat.sqrt (C + 1) ≤ C + 1 :=
  Nat.sqrt_le _

/-- **Interchangeable form.** With the root available, the original statement
follows from the square-root-free one. -/
theorem long_quiet_gap_of_short_travel_sqrt_free {M s C : Nat}
    (hM : 968 ≤ M) (hs : M + 2 ≤ s) (htravel : 2 * (s - (M + 2)) ≤ M)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) :
    2 * Nat.sqrt (C + 1) < C - s :=
  two_mul_sqrt_lt_gap_of_short_travel hM hs htravel hlo hhi (Nat.sqrt_le _)

end A166944Research
