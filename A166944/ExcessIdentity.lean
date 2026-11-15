import A166944.BIntegrate
import A166944.RoomLedger

/-!
# Why the excess sum alone cannot give the travel bound

`RoomLedger` rewrites the travel bound into the excess coordinates:

    travel_iff_scaled_excess
        2 * (sf - (M + 2)) <= M  <->  2 * S + M <= 2 * B sf + 4

with `S = sum (d r - 1)`, and `BIntegrate` proves the reservoir ledger

    B_path_integrated
        B sf + (sf - s) = B s + S.

The obvious hope is that a bound on `S` alone might close the first inequality. It
cannot, and the reason is exact rather than heuristic: the two relations are not
independent, so substituting one into the other returns the original statement.
Concretely, from `B sf = (M - 2) + S - travel` the right-hand side of
`travel_iff_scaled_excess` becomes

    2 * B sf + 4 = 2 * ((M - 2) + S - travel) + 4 = 2 * M + 2 * S - 2 * travel,

so the inequality `2 * S + M <= 2 * M + 2 * S - 2 * travel` cancels to
`2 * travel <= M`. That is the bound we started from.

So the excess coordinate and the reservoir coordinate carry one piece of
information between them, and any bound on `S` has to be paired with an
*independent* statement about `B sf` or about the travel itself. This is the ninth
independent route to the conclusion recorded in `REACH.md`, and it closes the last
coordinate change: what remains is arithmetic about the increments `d r`.

## What is proved here

`excess_only_gives_identity` is the cancellation above, stated so that the
substitution route is not attempted again. It is a statement about `Nat`
arithmetic with the two ledgers as hypotheses, so it does not depend on any
unproved input.

Not stated as a theorem, because the failure is data rather than a proposition:
a bound of the form `S <= c * M` does not imply travel. The measured values are

    M = 355723   p = 57   S = 2388   travel = 1317

so `S <= 2 * M` holds with room to spare while `2 * travel = 2634 > M` would fail
at `M = 13` and `M = 43` (where `2 * travel` is 18 and 68 against 13 and 43). The
reason a bound on `S` is not enough is structural and is what this file proves:
`S` and `B sf` are linked by the reservoir ledger, so one bound has to be paired
with an independent statement.
-/

namespace A166944Research

/-- **Substituting the reservoir ledger into the scaled-excess form returns the
travel bound.**  With `B sf = (M - 2) + S - travel` the equivalence of
`RoomLedger.travel_iff_scaled_excess` carries no information beyond the travel
bound itself. -/
theorem excess_only_gives_identity {M S travel Bsf : Nat} (hM : 4 ≤ M)
    (hB : Bsf + travel = (M - 2) + S) :
    (2 * S + M ≤ 2 * Bsf + 4 ↔ 2 * travel ≤ M) := by
  constructor <;> intro h <;> omega

end A166944Research
