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

end A166944Research
