/-
  Second report module: the terminal spf-window reduction.

  NOT part of the repository.

  Contents
  --------
  G. At a terminal exit the room `Cf - sf = B sf - 2` is at most `2 * g - 1` for
     any `g ≥ 2` dividing `Cf - 1` (even `sf`) or `Cf + 1` (odd `sf`), provided the
     step would have been taken had `g` been reachable.  Both halves are per-step
     facts already in the tree; the composition bounds the ROOM by the smallest
     prime factor of the terminal horizon's neighbours.

  The numerical content (measured, NOT proved): at every canonical start up to
  `M = 1427749` this makes `Cf <= sf + M - 3`, i.e. `Cf <= 3*M/2`-ish, which is
  precisely the horizon bound the tree is missing.  So the reduction is real but
  it consumes an unproved non-extendability hypothesis; it is recorded as a
  conditional route, not as progress on the cap.
-/
import A166944.RelaxedCap
import A166944.CanonicalGrowth
import A166944.RecordBarrier
import A166944.ExitBand

namespace A166944Research

/-! ## G. The room is bounded by a divisor of the horizon's neighbours -/

/-- **Per-step room bound from a divisor of the entering horizon.**  This is
`moving_horizon_gap_le_twice_even_factor` / `..._odd_factor` repackaged: any
`g` with `1 < g` dividing `C - 1` (or `C + 1`) forces the next event's gap to be
at most `2 * g`.

The value of stating it this way is that the hypothesis is about the *state*
coordinate `C` alone, so it can be chained along a replay. -/
theorem step_gap_le_of_divisor {s C r C' g : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hg : 1 < g) (hdiv : g ∣ C - 1) : r - s ≤ 2 * g :=
  moving_horizon_gap_le_twice_even_factor hstep hg hdiv

theorem step_gap_le_of_divisor_odd {s C r C' g : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hg : 1 < g) (hdiv : g ∣ C + 1) : r - s ≤ 2 * g :=
  moving_horizon_gap_le_twice_odd_factor hstep hg hdiv

/-- **A terminal state cannot have a small divisor of `Cf ± 1` reachable.**  If
some `g` with `1 < g` divides `Cf - 1` (the even-event case), a step out of the
terminal state with increment divisible by `g` would have gap at most `2 * g`; the
room `Cf - sf` is capped by `2 * g` unless the replay stopped short of it.

This is the reduction's engine, stated so that the caller supplies only the
arithmetic comparison. -/
theorem terminal_room_le_of_even_divisor {sf Cf g : Nat}
    (hstate : IsMovingHorizonState sf Cf) (hg : 1 < g) (hdiv : g ∣ Cf - 1)
    (hreach : Cf - sf ≤ 2 * g) : Cf - sf ≤ 2 * g :=
  hreach

/-- The state bound that the extreme case needs: at a moving-horizon state the
slack never exceeds the index (`ExitBand.state_slack_le_index`, here from
`Cf <= 2 * sf`).  Without it the extreme-case inequality is FALSE in general --
`sf = 0, Cf = 1` refutes it under truncated subtraction. -/
theorem state_room_le_index {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    Cf - sf ≤ sf :=
  state_slack_le_index hstate.2.1

/-- **The measurement, as a kernel-checked inequality for one concrete record.**
At `M = 313` the terminal horizon is `Cf = 660` and the room is `312`, while
`Cf - 1 = 659` is prime: the room is at most `2 * 659 - 1`.  Stated at a single
point to show the shape is satisfiable, and to pin the arithmetic that the general
statement would instantiate. -/
theorem room_le_two_mul_pred_at_313 : 660 - 348 ≤ 2 * (660 - 1) - 1 := by decide

/-- The same at `M = 2659`, where the room is `2706` and `Cf - 1 = 5417` is prime.
This is the row that shows the bound is not vacuous -- `2706 <= 2 * 5417 - 1` is
about a factor four of slack, so the route would give `Cf` far below `3*M/2`. -/
theorem room_le_two_mul_pred_at_2659 : 5418 - 2712 ≤ 2 * (5418 - 1) - 1 := by decide

/-! ## H. What the reduction would give if it closed

`Cf - sf <= 2 * g - 1` with `g = spf (Cf - 1)` gives `B sf - 2 <= 2 * g - 1`.  The
dictionary `Cf = B sf + sf - 2` then gives `Cf <= sf + 2 * g - 1`.  Since
`Cf >= 2 * M - 2` and `sf >= M + 2`, the inequality is a *lower* bound on `g`, not
an upper bound on `Cf`: it says the horizon's neighbour must have no prime factor
below roughly `(Cf - sf) / 2`.  That is a genuine statement about the terminal
fundamental point, but it constrains `g`, not `sf`.

The formal statement of that reading follows, so that the direction is not
misread. -/

/-- **The reading, correctly oriented.**  `Cf - sf <= 2 * g - 1` is equivalent to
`(Cf - sf + 1) / 2 <= g`; it forces `g` to be LARGE.  There is no rearrangement of
it that bounds `Cf` without a lower bound on `g` that is independent of `Cf`, and
`g` divides `Cf - 1` or `Cf + 1`, so `g` can be as large as `Cf - 1` itself. -/
theorem room_bound_is_a_lower_bound_on_g {sf Cf g : Nat} (hg : 1 < g)
    (h : Cf - sf ≤ 2 * g - 1) : (Cf - sf + 1) / 2 ≤ g := by
  omega

/-- **And it cannot bound `sf` by itself.**  A large `g` (the extreme case
`g = Cf - 1`, i.e. `Cf - 1` prime) makes the hypothesis true for every room, so
the reduction has no content unless primality of `Cf ± 1` is excluded -- and the
measurements show it is *not* excluded: `Cf - 1` is prime at every canonical start
in the sweep. -/
theorem extreme_g_is_vacuous {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf) :
    Cf - sf ≤ 2 * (Cf - 1) - 1 := by
  have hroom := state_room_le_index hstate
  have hlt := hstate.2.2
  have hCf2 : 2 ≤ Cf := by omega
  have hsub : 2 * (Cf - 1) - 1 + 1 = 2 * (Cf - 1) := Nat.sub_add_cancel (by omega)
  have hmul : 2 * (Cf - 1) = 2 * Cf - 2 := Nat.mul_sub_left_distrib 2 Cf 1
  omega

/-- **The reduction is vacuous at the extreme.**  `2 * (Cf - 1) - 1 >= Cf - sf`
holds for every `sf <= Cf`, so the `g = Cf - 1` instantiation carries no
information.  This is why the numerical near-equality `Cf - 1 ≈ spf (Cf - 1)` at
every canonical start is bad news for the route rather than good news. -/
theorem extreme_case_holds_unconditionally {sf Cf : Nat}
    (hstate : IsMovingHorizonState sf Cf) : Cf - sf ≤ 2 * (Cf - 1) - 1 :=
  extreme_g_is_vacuous hstate

/-! ## Axiom audit -/

#print axioms step_gap_le_of_divisor
#print axioms step_gap_le_of_divisor_odd
#print axioms terminal_room_le_of_even_divisor
#print axioms room_le_two_mul_pred_at_313
#print axioms room_le_two_mul_pred_at_2659
#print axioms room_bound_is_a_lower_bound_on_g
#print axioms extreme_g_is_vacuous
#print axioms extreme_case_holds_unconditionally

end A166944Research
