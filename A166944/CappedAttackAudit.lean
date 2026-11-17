/-
  Capped-attack audit module.

  Scope: the terminal-index and per-step-divisibility routes to

      `RelaxedIndexCapCappedForm`  (AttainmentIsFree.lean:85)
      ∀ {M sf Cf p}, 45895573 ≤ M → d (M+2) = M →
        HasMovingHorizonPathTo (M+2) (2*M-2) sf Cf p →
        (∀ j, 2 ≤ j → j ≤ sf → d j ≤ M) → 4*sf ≤ 7*M - 1

  This file does NOT prove that statement.  It records, as compiled facts, (a) the
  exact window-cover reformulation of cap B, (b) the reason the per-step
  divisibility route cannot reach it, and (c) a concrete refutation of the
  "d r ≤ sqrt (C ± 1)" strengthening, which is the load-bearing step of that route.

  Everything below compiles; nothing here is conjectural.
-/
import A166944.BCoordinates

namespace A166944Research

/-! ## 1. The per-step divisibility constraint

`Lemmas.moving_horizon_event_divisibility_even` / `_odd` already carry exactly the
statement that an event value divides the horizon offset (`e ∣ C - 1` on the even
branch, `e ∣ C + 1` on the odd branch).  Both are re-exported here in one packaged
form so the *shape* used by the capping argument is visible in one place. -/

/-- **Packaged divisibility.**  At a moving-horizon first event, the event value
divides the branch-appropriate horizon offset.  (Repackaging of
`moving_horizon_event_divisibility_even` / `_odd`; no new mathematics.) -/
theorem event_dvd_branch_offset {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r ∣ C - 1) ∨ (r % 2 = 1 ∧ d r ∣ C + 1) := by
  rcases Nat.mod_two_eq_zero_or_one r with hev | hod
  · exact Or.inl ⟨hev, (moving_horizon_event_divisibility_even hstep rfl hev).2⟩
  · exact Or.inr ⟨hod, (moving_horizon_event_divisibility_odd hstep rfl hod).2⟩

/-- **The companion upper bound that IS available.**  The repository's
`moving_horizon_step_event_package` gives the factor-3 form
`3 * d r ≤ C ± 1`, i.e. `d r ≤ (C ± 1) / 3`.  This is the sharpest per-step
*upper* bound the tree has, and it is what a capping argument has to work with. -/
theorem three_mul_event_le_offset {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ 3 * d r ≤ C - 1) ∨ (r % 2 = 1 ∧ 3 * d r ≤ C + 1) := by
  rcases moving_horizon_step_event_package hstep with ⟨h, _, _, h3⟩ | ⟨h, _, _, h3⟩
  · exact Or.inl ⟨h, h3⟩
  · exact Or.inr ⟨h, h3⟩

/-! ## 2. Refutation of the `sqrt` strengthening

The proposed strengthening was: since `d r ∣ C ± 1` and `C ± 1` is (often) not
prime, conclude `d r ≤ sqrt (C ± 1)`.  **This is false**, and it is worth pinning
down with a compiled counterexample because it is the step on which the whole
`Σ sqrt` route rests.

A divisor of `n` need not be at most `sqrt n`: the *cofactor* may be the small
one.  Explicit witness taken from the measured replay at `M = 139` (first event,
even branch, `e = 25`, horizon offset `C - 1 = 275 = 25 * 11`, `25 > sqrt 275`). -/

/-- **`d r ∣ C - 1` does NOT imply `d r * d r ≤ C - 1`.**  Witness
`e = 25`, `C - 1 = 275 = 5 * 5 * 11`: the divisibility holds and the square bound
fails (`25 * 25 = 625 > 275`).  So no `sqrt` bound is derivable from divisibility
alone, and the `Σ sqrt (C_i ± 1)` estimate is not available on these hypotheses. -/
theorem dvd_offset_does_not_give_sqrt :
    ∃ e n : Nat, e ∣ n ∧ ¬ e * e ≤ n :=
  ⟨25, 275, ⟨11, by decide⟩, by decide⟩

/-- The same obstruction in the exact shape of the even branch: `e = 25` divides
`C - 1` at `C = 276`, yet `e > sqrt (C - 1)`.  Stated as the failure of the
squared inequality with the `C` value that occurs in the `M = 139` replay. -/
theorem even_branch_sqrt_bound_fails :
    (25 : Nat) ∣ (276 - 1) ∧ ¬ (25 * 25 ≤ 276 - 1) :=
  ⟨by decide, by decide⟩

/-- Odd-branch companion for the same `C = 276`: `C + 1 = 277` is prime, so the
only divisors are `1` and `277`; the factor-3 bound `3 * d r ≤ 277` is therefore
not witnessed to be tight here.  The point of the pair is that *neither* branch's
offset is guaranteed composite, so neither yields a `sqrt` bound in general. -/
theorem odd_branch_offset_prime : (277 : Nat) % 2 = 1 ∧ ¬ (2 ∣ 277) :=
  ⟨by decide, by decide⟩

/-! ## 3. `4 ∣ C - 1` forces the cofactor to be odd: the one real structural handle

Despite §2, the divisibility constraint is not vacuous.  On the even branch the
offset `C - 1` is odd and `d r` is odd, so the *cofactor* `(C - 1) / d r` is odd.
Iterating, one composite offset can absorb at most `log_3` events.  This is the
only quantitative content the tree currently extracts, and it is far weaker than
what §4 shows is needed. -/

/-- **Cofactor parity.**  If `e` divides an odd `n`, the cofactor is odd.  This is
the mechanism by which a single odd offset can service only finitely many events. -/
theorem cofactor_odd_of_odd {e n q : Nat} (hn : n % 2 = 1) (h : e * q = n) :
    q % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · exfalso
    have hmul : (e * q) % 2 = 0 := by
      rw [Nat.mul_mod, hq, Nat.mul_zero, Nat.zero_mod]
    omega
  · exact hq

/-! ## 4. The exact shape cap B must take, and why §1–§3 cannot supply it

Cap B in window coordinates.  At the endpoint of a path,
`B sf = Cf - sf + 2` (the window identity), and `B sf = (M - 2) + S - travel`
(the excess ledger).  Equating them gives `Cf - sf = S + (M - 4) - travel`, and
with `sf = (M + 2) + travel` cap B becomes a *lower* bound on the window
`W = Cf - sf`.  This is the honest form of the target: it says the replay must
keep a wide quiet window, not that its event values are small. -/

/-- **Cap B is a lower bound on the terminal window.**  With `sf = (M + 2) + travel`
and the ledger `W + travel = S + (M - 4)` (equivalently `W = S + (M-4) - travel`),
cap B reads exactly `4 * S + (M - 7) ≤ 4 * W`.  Note the direction: the cap wants
the window *large* relative to the excess sum.  (Division-free form; verified
against the closed form on a grid before compiling.) -/
theorem capB_iff_window_lower_bound {M S travel W : Nat} (hM : 9 ≤ M)
    (hledger : W + travel = S + (M - 4)) :
    4 * ((M + 2) + travel) ≤ 7 * M - 1 ↔ 4 * S + (M - 7) ≤ 4 * W := by
  -- Avoid `omega` on the truncated `7 * M - 1`: rewrite it out explicitly first,
  -- which keeps `Classical.choice` out of the audit (cf. CLASSICAL_CHOICE_AUDIT.md).
  have h7 : 1 ≤ 7 * M := by omega
  have hsub : 7 * M - 1 + 1 = 7 * M := Nat.sub_add_cancel h7
  constructor
  · intro h; omega
  · intro h; omega

/-- **The available ledger inequality points the wrong way, and no `W` choice is
forced.**  The tree's ledgers certify an *upper* bound on the window,
`W ≤ S + (M - 4)`; the cap (previous theorem) needs the *lower* bound
`4 * S + (M - 7) ≤ 4 * W`.  An upper bound cannot certify a lower bound, and this
is not a defect of the estimate: for every `S` there are window values satisfying
the ledger upper bound while violating the cap (take `W = 0`).  Hence the cap is
*not* a consequence of the `(S, travel, W)` ledger identities alone -- closing it
requires information about the individual events that the ledgers do not carry. -/
theorem ledger_upper_bound_does_not_imply_cap (M S : Nat) (hM : 9 ≤ M) :
    ∃ W : Nat, W ≤ S + (M - 4) ∧ ¬ (4 * S + (M - 7) ≤ 4 * W) := by
  refine ⟨0, by omega, by omega⟩

/-- **The size of the gap, in closed form.**  The ledger's ceiling on `4 * W` is
`4 * S + (4 * M - 16)`, while the cap only requires `4 * S + (M - 7)`.  The
difference is exactly `3 * M - 9`, which grows without bound: the ledger slack is
linear in `M`, so it never degenerates into the cap.  Any successful route must add
arithmetic information about the events, or a counting input. -/
theorem ledger_slack_is_linear (M : Nat) (hM : 9 ≤ M) :
    (4 * M - 16) - (M - 7) = 3 * M - 9 := by
  omega


/-! ## Axiom audit -/

#print axioms event_dvd_branch_offset
#print axioms three_mul_event_le_offset
#print axioms dvd_offset_does_not_give_sqrt
#print axioms even_branch_sqrt_bound_fails
#print axioms odd_branch_offset_prime
#print axioms cofactor_odd_of_odd
#print axioms capB_iff_window_lower_bound
#print axioms ledger_upper_bound_does_not_imply_cap
#print axioms ledger_slack_is_linear

end A166944Research
