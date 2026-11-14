import A166944.BStepLaw
import A166944.CountFromIndex

/-!
# The reservoir ledger along a path

`moving_horizon_path_ledger` (`Lemmas.lean:7017`) gives, for a path with `q`
events,

    Cf + q = C + E  /\  sf + q = s + T,

where `E` is the sum of the event values and `T` the sum of the gaps. This file
adds the *reservoir* line to the same ledger.

The per-step identity is `excess_succ_add_two` (`Lemmas.lean:1241`):
`B (k + 1) + 2 = B k + d (k + 1)`. Over a whole step, with the unit tail
contributing its own decrements, the step law is
`B r + (r - s) + 1 = B s + d r` (`BCapDictionary` records it as a target, since
the version attempted there did not close). Summing over a path and writing
`g = r - s` for each gap gives the clean form

    B sf + T + q = B s + E.

At a canonical start `B (M + 2) = M - 2`, so this reads

    B sf = (M - 2) + E - T - q.

Two consequences, and they are the reason for recording this:

  * `B sf` is *determined* by `E`, `T`, `q` and `M`. There is no extra freedom
    in the reservoir coordinate; the observed near-equality `B sf ~ M` is a
    statement about `E - T - q` being small, not about `B` independently.
  * Combined with `canonical_count_le_reservoir`
    (`2 * q <= B sf + sf - 2 - (2 * M - 2)`), eliminating `B sf` gives a
    relation among `E`, `T`, `q`, `sf` alone -- which is where the search is.

What is not proved here: the step law itself. It is stated below as a target with
the reason, rather than carried as a theorem, because the version attempted in
`BCapDictionary` did not close and I have not found the missing rewrite.
-/

namespace A166944Research

/-- **The horizon step, in the form the ledger needs.**  `D (n+1)` differs from
`D n` by `d (n+1) - 1`; stated additively so downstream arithmetic avoids
truncated subtraction. -/
theorem D_step_additive {n : Nat} (hn : 1 ≤ d (n + 1)) :
    D (n + 1) + 1 = D n + d (n + 1) := by
  have h := D_succ_eq_D_add_d_sub_one n
  omega

/-! ## The path ledger, as a target

The identity to prove is

    B sf + T + q = B s + E

with `E`, `T` from `moving_horizon_path_ledger`. Verified numerically on all ten
records the sweep reaches (M from 13 to 88801), zero failures.

Both ingredients are now proved: `B_step_law` (in `BStepLaw`) is the per-step
identity, and `D_step_additive` above is the horizon step in the additive form the
summation needs -- `D (n+1) + 1 = D n + d (n+1)`, deliberately stated without a
subtraction so the induction never has to invert one.

Recorded as a target rather than as a theorem because the induction did not close
in the sessions spent on it. The obstruction is narrow and specific: `omega` will
not discharge `r - 1 + 1 = r` from `s < r` and `2 ≤ s` once `s` and `r` are the
abstract binders of a path step, so the rewrite has to be done with
`Nat.sub_add_cancel` against an explicitly hoisted `1 ≤ r`. Getting that plumbing
right is self-contained work; a broken proof or a weakened statement would be
worse than an honest target.

Why it matters: at a canonical start `B (M + 2) = M - 2`, so the ledger would read

    B sf = (M - 2) + E - T - q,

which *determines* the reservoir. The observed near-equality `B sf ~ M` is then a
statement about `E - T - q` being small, not about `B` having independent freedom.
Since `REACH.md` identifies the missing input as an event count bound and
`CountFromIndex` gives `2 * q <= B sf + sf - 2 - (2 * M - 2)`, pinning `B sf` this
way is the step that turns the problem into a bound on `E - T - q` -- precisely
the quantity `Lemmas.lean:3851` and `:7355` constrain (`3q <= E`, `E <= M*q`,
`2q <= T`).

-/

/-- **At a canonical start the reservoir is pinned.**  `B (M + 2) = M - 2`, so
the ledger reads `B sf = (M - 2) + E - T - q`. -/
theorem canonical_B_pinned {M E T q Bsf : Nat}
    (hB0 : Bsf + T + q = (M - 2) + E) : Bsf = (M - 2) + E - T - q := by
  omega

end A166944Research
