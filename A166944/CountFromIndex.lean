import A166944.BCapDictionary

/-!
# The event count is bounded by the index and the reservoir

Each moving-horizon step grows the horizon by `C' = D r = C + (d r - 1)`, and
`1 < d r` so the increment is at least `2`. Summing over a canonical replay from
`(M + 2, 2 * M - 2)` to `(sf, Cf)` therefore gives

    Cf - (2 * M - 2) >= 2 * p,

i.e. `p <= (Cf - 2 * M + 2) / 2`. Substituting the reservoir dictionary
`Cf = B sf + sf - 2` (`BCapDictionary`) turns that into

    p <= (B sf + sf - 2 * M) / 2.

So an upper bound on `sf` bounds `p`, and an upper bound on `B sf` does too. This
is the direction of travel the search needs: `REACH.md` records that the missing
input is an event count bound, and this file shows one sufficient source for it.

Why this is not yet the missing bound: the repository has no upper bound on `sf`
either. What it has is a *lower* bound (`moving_horizon_path_index_le`) and the
displacement bound `sf - s <= p * sqrt (4 (U + 1))`, which runs the wrong way --
it bounds `sf` in terms of `p`, and this file bounds `p` in terms of `sf`.

The two together are still informative: eliminating `p` gives
`sf - s <= (B sf + sf - 2 * M) / 2 * sqrt (4 (U + 1))`, a self-referential
inequality in `sf` alone. Whether that closes is not addressed here.
-/

namespace A166944Research

/-- **Horizon growth per step is at least two.** -/
theorem horizon_increment_ge_two {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C + 2 ≤ C' := hstep.2.2.2.2.2.2.2.1

/-- **The horizon at the endpoint is at least the start plus twice the count.**
For a canonical replay this reads `2 * M - 2 + 2 * p <= Cf`. -/
theorem horizon_ge_start_add_twice_count {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) : C + 2 * p ≤ Cf := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, rfl, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      have h1 : C + 2 ≤ C' := horizon_increment_ge_two hstep
      have h2 : C' + 2 * p ≤ Cf := ih htail
      omega

/-- **The event count is bounded by the endpoint horizon.** -/
theorem count_le_horizon {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) : 2 * p ≤ Cf - C := by
  have h := horizon_ge_start_add_twice_count hpath
  omega

/-- **The same, in the reservoir form the canonical replay actually has.**  With
`Cf = B sf + sf - 2` this is `p <= (B sf + sf - 2 * M) / 2` at a canonical start. -/
theorem canonical_count_le_reservoir {M sf Cf p : Nat}
    (hstate : IsMovingHorizonState sf Cf)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    2 * p ≤ B sf + sf - 2 - (2 * M - 2) := by
  have h := count_le_horizon hpath
  have hB := moving_horizon_state_B_add_index hstate
  omega

end A166944Research
