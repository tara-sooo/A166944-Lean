import A166944.RoomLedger
import A166944.BandReentry

/-!
# The excursion ceiling: what each step does to the room

`BandReentry` refutes the no-reentry assumption -- a canonical replay leaves the
capped band `room <= M` and comes back -- so the tail cannot be packaged as a single
in-band suffix. This file proves what *is* true at every step, and the result is a
real inequality, not a tautology, and it is sharper than `GapBound`'s per-step
`r - s <= 2 * d r`.

## The one-step inequality

Write `room = C - s`, gap `g = r - s`, event `e = d r`. The repository's parity
quotient normal form (`moving_horizon_even_quotient_normal_form`, `_odd_`) gives the
**exact** next room:

    r % 2 = 0 :   C' - r = e * (q + 1),       q odd,  q >= 1
    r % 2 = 1 :   C' - r + 4 = e * (q + 1),   q even, q >= 2

Both cases therefore satisfy the parity-free bound

    2 * e <= (C' - r) + 2              (`two_mul_increment_le_room_next`)

**the room left after a step is at least twice the event, minus two.** The bound
mentions no gap, so it composes. Read through the transition identity
`room' + g = room + e - 1` it is *equivalent* to `g + e <= room + 1`, i.e. the room
plus one always covers the gap plus the event; the equivalence is recorded so neither
form is mistaken for the stronger one.

## What it buys at a band exit

The transition identity is `room' = room + e - 1 - g`. So a step whose room **rises**
satisfies `e >= g + 1`; a step that leaves the band, `room <= M < room'`, must rise,
hence `e >= g + 2` and `room' > room` -- the room strictly increases at an exit. That
is the exact mechanism behind `BandReentry`: leaving the band is a *gain* in room, so
the replay can and does come back, and no monotonicity in the other direction exists.
It is also the quantitative replacement for the false no-reentry packaging: an exit
is paid for by a strictly larger room, not by an assumption about permanence.

## Proved / refuted / numerically checked / not proved

**Proved here:** `two_mul_increment_le_room_next`,
`gap_add_increment_le_room_add_one`, `gap_form_iff_room_form`,
`band_exit_increment_ge_gap_add_two`, `band_exit_room_strictly_increases`,
`band_exit_gap_le_half_record` (`2 * (r - s) + 1 <= M` at any in-band exit),
`band_exit_structure`, and the canonical-start corollary
`band_exit_at_canonical_start`.

**Refuted, and recorded so it is not re-derived:** the natural guess that the room
drops by at most one per step, `C - s <= (C' - r) + 1`, is **false**. It is *not*
equivalent to the bound above -- the equivalence needs the gap added to the room.
A sweep to `2.9 * 10^6` finds the room dropping by 468 in a single step at
`(s, r, e, g, room, room') = (2861166, 2862610, 977, 1444, 2861124, 2860656)`. The
conserved quantity is `room + gap`, never `room` alone.
`room_drop_bound_is_not_available` isolates the arithmetic obstruction: the
hypothesis set actually available per step (the transition identity, `2 * e <=
room' + 2`, `g <= 2 * e`) is satisfied by data with `room' + 1 < room`, so no
argument from those hypotheses alone can bound the drop.

**Numerically checked to `2.9 * 10^6`** (zero violations): `2 * e <= room' + 2` at
all 224018 generic steps (arbitrary starts, not only canonical records) and at all
230 steps of the fifteen canonical record replays; and the proved exit triple
(`e >= g + 2`, `2 * g + 1 <= M`, room rises) at all 9642 generic band exits. The
strictly stronger empirical form `2 * g + 3 <= M` also holds at all 9642 exits but is
**not** proved here, so it is recorded as data only.

**Not proved, not claimed:** the frontier `2 * travel <= M`. The excess `S` is still
unbounded and `ExcessIdentity` shows `S` is the irreducible input. The `M = 13` and
`M = 43` replays violate travel while satisfying every bound here, so this file is
strictly weaker than the frontier and does not close it.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The partition identity for one step

`room' = room + e - 1 - g` is the transition identity in the form the excursion
arguments read; it is recorded first because every later statement is a consequence. -/

/-- **The room partition.**  The new room is the old room, plus the excess `e - 1`,
minus the gap. This is `moving_horizon_slack_transition` rearranged, and it is what
makes the room non-monotone: a long gap can lose more than the event pays. -/
theorem room_partition {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) = (C - s) + (d r - 1) :=
  moving_horizon_slack_transition hstep

/-! ## 2. The one-step inequality and its equivalent gap form -/

/-- **The room left after a step is at least twice the event minus two.**

Even case: `C' - r = e * (q + 1)` with `q >= 1`, so `C' - r >= 2 * e`.
Odd case: `C' - r + 4 = e * (q + 1)` with `q >= 2`, so `C' - r + 4 >= 3 * e`, and
`3 * e - 4 >= 2 * e - 2` because `e >= 2`.

Neither case uses the gap, which is why this form composes along a path. -/
theorem two_mul_increment_le_room_next {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    2 * d r ≤ (C' - r) + 2 := by
  by_cases heven : r % 2 = 0
  · obtain ⟨q, _, _, hq1, hlast⟩ :=
      moving_horizon_even_quotient_normal_form hstep heven
    have hmul : d r * 2 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact absurd hzero heven
      · exact hone
    obtain ⟨q, _, _, hq2, hlast⟩ :=
      moving_horizon_odd_quotient_normal_form hstep hodd
    have hmul : d r * 3 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    have he2 : 2 ≤ d r := by
      have := moving_horizon_step_event_ge_three hstep
      omega
    omega

/-- **The room plus one covers the gap plus the event.**  Equivalently the gap is at
most the room minus the event plus one, so a large event *forces* a short gap. -/
theorem gap_add_increment_le_room_add_one {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r - s) + d r ≤ (C - s) + 1 := by
  have htrans := moving_horizon_slack_transition hstep
  have hmain := two_mul_increment_le_room_next hstep
  have hsr : s < r := hstep.2.1
  omega

/-- **The gap is bounded by the room minus the event plus one.**  The form used when
the event is known to be a large fraction of the room: then the gap is short. -/
theorem gap_le_room_sub_increment_add_one {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hle : d r ≤ C - s) :
    r - s ≤ (C - s) - d r + 1 := by
  have hmain := gap_add_increment_le_room_add_one hstep
  omega

/-- **The two forms are equivalent.**  Recorded so neither is mistaken for strictly
stronger: each follows from the transition identity plus the other. -/
theorem gap_form_iff_room_form {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    ((r - s) + d r ≤ (C - s) + 1) ↔ (2 * d r ≤ (C' - r) + 2) :=
  ⟨fun _ => two_mul_increment_le_room_next hstep,
   fun _ => gap_add_increment_le_room_add_one hstep⟩

/-! ## 3. Band exits: the room strictly increases -/

/-- **A step whose room rises needs an event at least the gap plus one.**  Immediate
from `room' = room + e - 1 - g`. -/
theorem increment_ge_gap_add_one_of_room_rises {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hrise : C - s ≤ C' - r) :
    (r - s) + 1 ≤ d r := by
  have htrans := moving_horizon_slack_transition hstep
  have hsr : s < r := hstep.2.1
  omega

/-- **A band exit forces the event to exceed the gap by at least two.**

This is the mechanism behind `BandReentry`. The state is in the band, `room <= M`, and
the next state is out of it, `M < room'`; then the room rose, so the transition
identity forces `e >= g + 2`, and in particular `room' > room`. Leaving the band is a
*gain* in room -- which is exactly why the replay can come back, and why no
monotonicity argument in the opposite direction can work. -/
theorem band_exit_increment_ge_gap_add_two {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    (r - s) + 2 ≤ d r := by
  have htrans := moving_horizon_slack_transition hstep
  have hlt : C - s < C' - r := Nat.lt_of_le_of_lt hin hout
  have hsr : s < r := hstep.2.1
  omega

/-- **At a band exit the room strictly increases.**  The same hypotheses, stated as
the room comparison, which is the form that refutes any "leaving is permanent"
assumption directly rather than through an index argument. -/
theorem band_exit_room_strictly_increases {M s C r C' : Nat}
    (hin : C - s ≤ M) (hout : M < C' - r) :
    C - s < C' - r :=
  Nat.lt_of_le_of_lt hin hout

/-- **At a canonical start, a band exit costs at least a gap-plus-two event.**
`M >= 6` puts the canonical room `M - 4` inside the band, so the exit lemma applies
with the canonical parameters spelled out. -/
theorem band_exit_at_canonical_start {M s C r C' : Nat}
    (hM : 6 ≤ M) (hcanon : s = M + 2 ∧ C = 2 * M - 2)
    (hstep : IsMovingHorizonStep s C r C') (hout : M < C' - r) :
    (r - s) + 2 ≤ d r ∧ C - s < C' - r := by
  obtain ⟨rfl, rfl⟩ := hcanon
  have hroom : (2 * M - 2) - (M + 2) = M - 4 := canonical_start_room (by omega)
  have hin : (2 * M - 2) - (M + 2) ≤ M := by omega
  exact ⟨band_exit_increment_ge_gap_add_two hstep hin hout,
         band_exit_room_strictly_increases hin hout⟩

/-- **At any in-band start, a band exit forces `e >= g + 2`.**  The same statement
without the canonical parameters, for use mid-replay, where the current state is in
the band but is not the start. -/
theorem in_band_exit_forces {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    (r - s) + 2 ≤ d r ∧ C - s < C' - r :=
  ⟨band_exit_increment_ge_gap_add_two hstep hin hout,
   band_exit_room_strictly_increases hin hout⟩

/-! ## 3b. The crossing gap bound: the corollary that does bite

`in_band_exit_forces` gives `e >= g + 2` at an exit. `gap_le_room_sub_increment_add_one`
gives `g <= room - e + 1`. Substituting the first into the second at an *in-band*
start, `room <= M`, eliminates the event entirely:

    g <= M - (g + 2) + 1   i.e.   2 * g + 1 <= M .

So at every band exit whose start is in the band, the gap is at most half the record.
This is a genuine restriction that no previous file records: it says a replay crosses
the band only through a *short* gap, which is what forces the room to rise at an exit
and hence what makes `BandReentry` possible at all rather than accidental. -/

/-- **At a band exit the gap is at most half the record.**  Combining
`in_band_exit_forces` (`e >= g + 2`) with `gap_le_room_sub_increment_add_one`
(`g <= room - e + 1`) and `room <= M`. -/
theorem band_exit_gap_le_half_record {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    2 * (r - s) + 1 ≤ M := by
  have hinc := band_exit_increment_ge_gap_add_two hstep hin hout
  -- Additive route: the room form avoids inverting the truncated subtraction.
  have hroomform := gap_add_increment_le_room_add_one hstep
  omega

/-- **The two exit facts together.**  A band exit both costs a gap-plus-two event and
happens through a gap of at most half the record; the room therefore rises at the
exit. This is the exact structure `BandReentry` witnesses numerically, now with the
inequalities proved. -/
theorem band_exit_structure {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    (r - s) + 2 ≤ d r ∧ 2 * (r - s) + 1 ≤ M ∧ C - s < C' - r :=
  ⟨band_exit_increment_ge_gap_add_two hstep hin hout,
   band_exit_gap_le_half_record hstep hin hout,
   band_exit_room_strictly_increases hin hout⟩

/-! ## 4. The refuted strengthening, isolated

The step from `2 * e <= room' + 2` to a bound on the room *drop* is not available:
the drop bound `C - s <= (C' - r) + 1` is a strictly stronger claim, and it is false.
The arithmetic below exhibits the obstruction inside the hypothesis set that is
actually available at a step, so no argument using only those hypotheses can supply
it. -/

/-- **The available per-step hypotheses do not bound the room drop.**

Data satisfying all of

* the partition `room' + g = room + (e - 1)`,
* the one-step bound `2 * e <= room' + 2`,
* the gap bound `g <= 2 * e` (`GapBound`),

can still have `room' + 1 < room`, so `C - s <= (C' - r) + 1` is *not* a consequence
of them. The instance is the one a sweep to `2.9 * 10^6` realises at
`(s, r, e, g, room, room') = (2861166, 2862610, 977, 1444, 2861124, 2860656)`; the
numbers are checked, the step witness is numerical evidence rather than a formalised
finite step. -/
theorem room_drop_bound_is_not_available :
    ∃ room g e room' : Nat,
      room' + g = room + (e - 1) ∧ 2 * e ≤ room' + 2 ∧ g ≤ 2 * e ∧ room' + 1 < room :=
  ⟨2861124, 1444, 977, 2860656, by decide, by decide, by decide, by decide⟩

end A166944Research
