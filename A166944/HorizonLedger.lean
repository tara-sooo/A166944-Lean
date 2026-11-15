import A166944.ExcessSumInterval
import A166944.BIntegrate

/-!
# The terminal horizon as base plus accumulated excess

`BIntegrate.B_path_integrated` records the reservoir ledger with the excess sum
existentially quantified:

    exists S, B sf + (sf - s) = B s + S.

That suffices for the room and reservoir identities, but it leaves `S` unnamed, so
nothing downstream can state a bound on its size. `ExcessSumInterval` has the
telescoping identity in the abstract -- for any `e` and `D` with
`D (k+1) = D k + (e k - 1)` -- but it was never instantiated at a replay.

This file records the instantiation in the form the frontier needs: at a canonical
start, the terminal horizon is twice the record minus two, plus an excess `S`:

    Cf = (2 * M - 2) + S.

`S` is still existential -- naming it concretely would need an explicit sum over the
path's events, which is more machinery than any use here requires -- but the shape
is what a bound would attach to, and it is the shape the measurements describe.

## What is not claimed

Naming the shape does not bound `S`. This is a reformulation of the horizon in terms
of the accumulated excess, and reformulations have not moved this problem. It is
recorded because every existing statement about `Cf` was either a bound
(`Cf <= 3*M + 4`) or the dictionary (`B sf + sf = Cf + 2`), and neither exposes the
excess as the gap between `Cf` and `2*M - 2`.
-/

namespace A166944Research

/-- **The horizon ledger, as the frontier sees it.**  Along any moving-horizon path
the terminal horizon is the starting horizon plus an accumulated excess. -/
theorem horizon_eq_start_add_excess {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, Cf = C + S := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, hCf, _⟩ := hpath
      exact ⟨0, by omega⟩
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hC'⟩ := ih htail
      refine ⟨(d r - 1) + S', ?_⟩
      have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
      omega

/-- **At a canonical start.**  The gap between `Cf` and `2*M - 2` is an accumulated
excess. -/
theorem canonical_horizon_eq_base_add_excess {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    ∃ S : Nat, Cf = (2 * M - 2) + S :=
  horizon_eq_start_add_excess hpath

/-- **Contrapositive, in the form a refutation would use.**  If the horizon exceeds
`2M - 2` by more than `c`, the excess exceeds `c`. -/
theorem excess_gt_of_horizon_gt {M sf Cf p S c : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : Cf = (2 * M - 2) + S) (hbig : 2 * M - 2 + c < Cf) :
    c < S := by omega

/-! ## What a bound on the excess would give

The statements below are conditional on a bound for `S`. They are recorded in that
form because no bound on `S` is proved yet: the measurements show `S <= M/2` at
every record examined, but an observation is not a theorem, and stating the
consequence conditionally is what makes the observation usable the moment a proof
arrives.

The chain worth knowing: `S <= M/2` gives `Cf <= (5*M)/2 - 2`, which is strictly
sharper than the horizon cap `Cf <= 3*M + 4` that the development currently carries.
Feeding that into the count/reservoir inequality gives `p <= M/4 + 1`.

That last one is honest about its own limits. The event-count criterion the frontier
consolidates on is `48 * p * p + 1 < M`, which needs `p` to be about `sqrt(M)/7`
-- at `M = 45895573` that is below 980, while `M/4 + 1` allows 11 million. So a bound
on `S` of the measured strength constrains the horizon usefully and the count
uselessly. Both facts are recorded, because the second is as informative as the
first: it says the excess is not where the count bound will come from.
-/

/-- **A bound on the excess bounds the horizon.**  With `Cf = 2*M - 2 + S`, any
bound on `S` transfers to `Cf` immediately. -/
theorem horizon_le_of_excess_le {M Cf S c : Nat} (hS : Cf = (2 * M - 2) + S)
    (hbound : S ≤ c) :
    Cf ≤ 2 * M - 2 + c := by omega

/-- **The measured strength of the excess bound would improve the horizon cap.**
`S <= M/2` gives `Cf <= (5*M)/2 - 2`, against the `Cf <= 3*M + 4` in the tree. -/
theorem horizon_le_of_excess_le_half {M Cf S : Nat} (hM : 4 ≤ M)
    (hS : Cf = (2 * M - 2) + S) (hbound : 2 * S ≤ M) :
    2 * Cf ≤ 5 * M - 4 := by omega

/-- **And it bounds the event count -- weakly.**  Combining with the count/reservoir
inequality `2*p <= Cf - 2*M + 4` gives `p <= M/4 + 1`, which is far above the
`sqrt(M)/7` that the event-count criterion needs. Recorded so that the excess route
and the count route are not confused for one another. -/
theorem count_le_of_excess_le_half {M Cf p S : Nat} (hM : 4 ≤ M)
    (hS : Cf = (2 * M - 2) + S) (hbound : 2 * S ≤ M)
    (hcount : 2 * p ≤ Cf - 2 * M + 4) :
    4 * p ≤ M + 4 := by omega

/-- **The count bound this gives is not the one the frontier needs.**  At the
threshold, `M/4 + 1` exceeds `sqrt(M)/7` by four orders of magnitude. Stated as a
number so the gap is not mistaken for a small one. -/
theorem excess_route_count_bound_is_far_too_weak :
    48 * (45895573 / 4 + 1) * (45895573 / 4 + 1) + 1 > 45895573 := by decide

end A166944Research
