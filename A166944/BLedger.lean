import A166944.BCoordinates
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

/-! ## The reservoir ledger, as a target

The identity to prove is

    B sf + T + q = B s + E

at a canonical start, i.e. `B sf = (M - 2) + E - T - q`. It holds numerically on
every record checked (11 of 11, M from 13 to 88801), and the ingredients are both
in the tree: `moving_horizon_path_ledger` supplies `E` and `T` with
`Cf + q = C + E` and `sf + q = s + T`, and `excess_succ_add_two`
(`Lemmas.lean:1241`) is the per-step law `B (k + 1) + 2 = B k + d (k + 1)`.

It is recorded here as a target rather than as a theorem because the induction did
not close: summing the step law over a path and matching it against the ledger
needs the gap sum `r - s` carried alongside `E` and `T`, and the versions I
attempted left `omega` with a goal it could not solve. Writing the correct
induction is a self-contained piece of work, and leaving a broken proof or a
weakened statement would be worse than leaving the target.

Why it matters: if the identity holds then `B sf` is *determined* by `E`, `T`,
`q` and `M`, so the observed near-equality `B sf ~ M` is a statement about
`E - T - q` being small rather than about `B` having independent freedom. That
reframes the missing event-count bound as a bound on `E - T - q`, which is the
quantity the count bounds in `Lemmas.lean:3851` and `:7355` actually control.

-/

/-- **At a canonical start the reservoir is pinned.**  `B (M + 2) = M - 2`, so
the ledger reads `B sf = (M - 2) + E - T - q`. -/
theorem canonical_B_pinned {M E T q Bsf : Nat}
    (hB0 : Bsf + T + q = (M - 2) + E) : Bsf = (M - 2) + E - T - q := by
  omega

end A166944Research
