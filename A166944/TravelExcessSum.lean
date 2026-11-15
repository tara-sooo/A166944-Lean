import A166944.GapBound
import A166944.BIntegrate

/-!
# Travel is at most twice the accumulated excess

`GapBound` gives a per-step inequality `r - s <= 2 * d r`. Summing it along a path
gives

    sf - s <= 2 * (S + p),

where `S = sum (d r - 1)` is the accumulated excess that `BIntegrate` already uses
for the reservoir ledger and that `ExcessIdentity` already uses for the scaled
form of the travel bound. This file is the summed version, which the per-step
statement does not give because the number of steps is what has to be counted.

## Why the sum matters

`RelaxedCap` showed that the relaxed index cap forces `4 * p <= 3 * M + 3`, and the
cap itself is equivalent (at a canonical start) to `4 * travel <= 3 * M - 9`. Those
two together are the shape of the obstruction: what the cap needs is control of the
accumulated excess, not of any single step. The inequality below is the bridge --
it turns a bound on `S + p` into a bound on the travel, and `S + p` is the quantity
`REACH.md` names from the other direction.

Explicitly, with `sf - (M + 2) <= 2 * (S + p)`, a bound `S + p <= (3*M - 9)/8`
would give the relaxed cap `4 * sf <= 7 * M - 1` directly. Neither the bound itself
nor the cap is proved here; what is proved is that the accumulation is the right
place to look.

## How the induction works

The step from `(s,C)` to `(r,C')` splits the travel as `(r - s) + (sf - r)`. The
first term is at most `2 * d r` by `GapBound`; the second is at most
`2 * (S' + p)` by the induction hypothesis on the tail. Adding,
`2 * (d r + S' + p)`, and the new excess sum is `S' + (d r - 1)`, so
`S' + d r + p = (S' + (d r - 1)) + (p + 1)` -- the accumulated excess of the whole
path plus its step count.
-/

namespace A166944Research

/-- **Travel bounded by twice the accumulated excess.**  For every moving-horizon
path there is an excess sum `S`, the sum of `d r - 1` over the path's events, with
`sf - s <= 2 * (S + p)`. -/
theorem path_travel_le_two_mul_excess {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, sf - s ≤ 2 * (S + p) := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, _, _⟩ := hpath
      exact ⟨0, by omega⟩
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hS'⟩ := ih htail
      have hgap : r - s ≤ 2 * d r := gap_le_two_mul_event hstep
      have hd1 : 1 < d r := hstep.2.2.2.1
      have hsr : s < r := hstep.2.1
      -- `omega` needs the upper bound on `r` explicitly to split the
      -- displacement; without it the truncated subtraction defeats it.
      have hle : r ≤ sf := moving_horizon_path_index_le htail
      have hsplit : sf - s = (sf - r) + (r - s) := by omega
      refine ⟨S' + (d r - 1), ?_⟩
      have hexp : 2 * (S' + p) + 2 * d r = 2 * (S' + (d r - 1) + (p + 1)) := by omega
      omega

/-- **The bridge from the excess sum to the relaxed cap.**  At a canonical start,
if the accumulated excess plus the step count is at most `(3*M - 9)/8`, then the
relaxed index cap holds.  This is the decomposition of the cap into the two
quantities `REACH.md` names: the accumulated excess `S` and the event count `p`.

Neither hypothesis is proved here.  What is proved is that they suffice, so the
cap can be attacked through them. -/
theorem relaxed_cap_of_excess_sum {M sf Cf p S : Nat} (hM : 9 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : sf - (M + 2) ≤ 2 * (S + p)) (hbound : 8 * (S + p) ≤ 3 * M - 9) :
    4 * sf ≤ 7 * M - 1 := by
  have hsf : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hsplit : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel hsf
  have h4 : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  -- Chain the two bounds, keeping the truncated `3 * M - 9` off the path that
  -- `omega` has to reason about with a coefficient.
  have hA : 4 * (sf - (M + 2)) ≤ 8 * (S + p) := by omega
  -- Convert the truncated bound to an additive one; `omega` handles
  -- `8*(S+p) + 9 <= 3*M` where it will not handle `8*(S+p) <= 3*M - 9` next to
  -- a coefficient.
  have h9 : 9 ≤ 3 * M := by omega
  have hB : 8 * (S + p) + 9 ≤ 3 * M := by omega
  have hC : 4 * (sf - (M + 2)) + 4 * (M + 2) + 9 ≤ 3 * M + 4 * (M + 2) := by omega
  omega

/-- **The cap, decomposed.**  The relaxed cap follows from a bound on `S + p`,
uniformly in the path. -/
theorem relaxed_cap_of_uniform_excess_bound {lower : Nat} (hlow : 9 ≤ lower)
    (h : ∀ {M sf Cf p : Nat}, lower ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      ∃ S : Nat, sf - (M + 2) ≤ 2 * (S + p) ∧ 8 * (S + p) ≤ 3 * M - 9) :
    ∀ {M sf Cf p : Nat}, lower ≤ M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      4 * sf ≤ 7 * M - 1 := by
  intro M sf Cf p hM hcanon hpath
  obtain ⟨S, hS, hbound⟩ := h hM hcanon hpath
  exact relaxed_cap_of_excess_sum (by omega) hpath hS hbound

end A166944Research
