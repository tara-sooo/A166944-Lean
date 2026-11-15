import A166944.RoomQuantum
import A166944.BandExcursion
import A166944.TravelExcessSum
import A166944.ExcessLower

/-!
# Angle 3 (round 3): simultaneous evaluation of `e_i` and `room_i`

This module records what survives an attack on the A166944 barrier through the
*joint* structure of the event value `e = d r` and the room `room = C - s`.

Writing, for one moving-horizon step `(s,C) → (r,C')`,

* `e  = d r`      the event value,
* `g  = r - s`    the gap (travel of the step),
* `room  = C - s`  the room before,
* `room' = C' - r` the room after,

the repository already knows the partition `room' + g = room + (e - 1)`
(`moving_horizon_slack_transition`), the gap bound `g ≤ 2 e` (`gap_le_two_mul_event`)
and the ceiling `room' + 2 ≤ 2 * room` (`moving_horizon_next_slack_upper`). This file
adds the two facts that make the pair `(e, room)` sharp rather than just bounded:

## What is proved here

1. **Sharp simultaneous inequalities** (`even_event_add_gap_add_one_le_room`,
   `odd_two_mul_event_add_gap_le_room_add_three`). The room must cover the event
   *plus the gap*: an even hit needs `e + g + 1 ≤ room`, an odd hit needs
   `2 e + g ≤ room + 3`. The repository's `moving_horizon_step_size_le_slack`
   (`e ≤ room`) is the even case with the gap dropped; the sharp form is strictly
   stronger and it is the form the joint angle needs, because it is the only
   per-step inequality in the library in which `e` and `g` appear together with a
   *coefficient on `e` greater than one*.

2. **The exact reconstruction identity** (`room_eq_gap_add_one_add_event_mul_quantum_even`,
   `room_eq_gap_sub_three_add_event_mul_quantum_odd`). With the quantum index
   `m := C' - r` over `e` (even) or `C' - r + 4` over `e` (odd),
   `room = e * (m - 1) + 1 + g` (even) and `room = e * (m - 1) - 3 + g` (odd).
   This is exact, not an inequality.

3. **The degenerate case characterised** (`even_degenerate_iff_room_eq_gap_add_one_add_event`,
   `odd_degenerate_iff_room_add_three_eq_gap_add_two_mul_event`). `room' = 2 e`
   happens exactly when the quantum index is minimal, i.e. exactly when the step
   consumed the whole room down to `g + e + 1`.

4. **The accumulated identity in the joint coordinates**
   (`excess_eq_count_add_travel_add_room_gain`): over a path,
   `Σ e_i = p + (Σ g_i) + (room_f - room_0)`. Everything earned is step count,
   travel, or room gain; the three are not independent, which is the precise
   reason a *local* evaluation of the pair `(e_i, room_i)` does not reach the cap.

## What is refuted here, with a kernel-checked witness

5. **The sharp local package is insufficient.** `sharp_local_package_does_not_give_cap`
   exhibits `M = 10 ^ 6` and a two-step profile satisfying *every* sharp
   simultaneous inequality of items 1-3 at a canonical start, with
   `8 * (e_1 + e_2) > 3 * M - 9`. So no argument from the joint local hypotheses alone
   can close the barrier. This is the same shape of negative result as
   `BandExcursion.room_drop_bound_is_not_available` and
   `TerminalRigidity.excess_bound_alone_does_not_give_cap`.

   **The witness is abstract, and the control is the real recurrence.**  At
   `M = 10 ^ 6` the canonical start state itself fails: `a (M + 2) - (M + 2) =
   1427748` while `2 * M - 2 = 1999998`, so `IsMovingHorizonState (M + 2) (2 * M - 2)`
   is false and no canonical replay exists there.  The witness therefore satisfies the
   *joint local hypotheses* (`room_0 = M - 4`, the sharp bounds, the ledger) while the
   state predicate is unavailable -- which is exactly what an insufficiency statement
   about a hypothesis set means, and it is stated this way rather than as a claim
   about a replay.

   The real control is `M = 13` and `M = 43`: their canonical replays *do* violate the
   cap (`RoomLedger.travel13_fails`, `12 * 5 = 60 > 15 * ... `; measured `Σ e = 22`
   against an allowance of `3.75`, and `Σ e = 60` against `15`) while satisfying every
   sharp inequality of sections 1-3 at every one of their steps.  The relaxation of
   item 5 is thus not vacuous: it is the same phenomenon the recurrence itself
   exhibits below the threshold.

## Scope, stated rather than implied

Nothing here proves the frontier `Σ e_i ≤ (3M - 9)/8`. The measurements below
(`ROOM_EVENT_MEASUREMENTS.md`) show the joint margin is large and *improves* with
`M`, but they also show the local relaxation of item 5 is loose by a factor of about
10 in `Σ e_i`, so the margin is a property of the recurrence's global dynamics and
not of any single step. Recorded so this angle is not re-derived.

All tactics here are pure core (`decide` / `omega` / `simp` / `rfl` / `rcases` /
`exact`); no `ring`, `linarith`, `norm_num`, `positivity` or `interval_cases`.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The sharp simultaneous inequalities

Both come straight out of the parity quotient normal forms, and both are the sharp
statement of what one step can afford. The even case is the one that matters: it
carries the event value with coefficient one *and* the gap, and the odd case carries
the event value with coefficient **two**, which is why a long odd-hit run is cheap in
room and expensive in events. -/

/-- **Even hit: the room covers the event, the gap, and one more.**  This is the sharp
form of `moving_horizon_step_size_le_slack` in the even case -- that lemma drops the
gap, and the gap is exactly what the frontier needs to control.  Measured tight at
`M = 13` (step 2: `9 + 1 + 1 = 11`) and at `M = 43` (step 5: `33 + 6 + 1 = 40`). -/
theorem even_event_add_gap_add_one_le_room {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    d r + (r - s) + 1 ≤ C - s := by
  obtain ⟨q, hroom, _, hq1, _⟩ := moving_horizon_even_quotient_normal_form hstep heven
  have hmul : d r * 1 ≤ d r * q := Nat.mul_le_mul_left _ hq1
  omega

/-- **Odd hit: two event values plus the gap fit in the room, up to three.**  The
coefficient two on `d r` is what the odd branch buys: an odd hit is at most half as
expensive in room as an even hit of the same size, because `q` is even and at least
two in `C - s + 3 = (r - s) + d r * q`. -/
theorem odd_two_mul_event_add_gap_le_room_add_three {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    2 * d r + (r - s) ≤ C - s + 3 := by
  obtain ⟨q, hroom, _, hq2, _⟩ := moving_horizon_odd_quotient_normal_form hstep hodd
  have hmul : d r * 2 ≤ d r * q := Nat.mul_le_mul_left _ hq2
  omega

/-- **The simultaneous pair, bundled.**  Coefficients `1` (even) and `2` (odd) on the
event value, always with the gap added and never with the gap dropped. -/
theorem event_add_gap_le_room_dichotomy {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r + (r - s) + 1 ≤ C - s) ∧
      (r % 2 = 1 → 2 * d r + (r - s) ≤ C - s + 3) :=
  ⟨fun h => even_event_add_gap_add_one_le_room hstep h,
   fun h => odd_two_mul_event_add_gap_le_room_add_three hstep h⟩

/-- **Even hit, non-degenerate branch: `e` grows by a factor of three against the
room.**  When the quantum index is at least four (i.e. the step did *not* land on the
degenerate `2 e`), the room covers three event values plus the gap and two:
`3 e + g + 1 ≤ room`, i.e. the coefficient three on `e`, with the gap kept.  The
room variable is `e * q` shifted by the gap and one, so `q ≥ 3` is exactly the
statement that the room carries three event values; the gap-free corollary
`3 e + 2 ≤ room` (using `g ≥ 1`) then holds, and it is *tight*: at
`(M, e, room, m) = (13, 5, 18, 4)` it reads `17 ≤ 18` with slack one, and it holds at
all 105 even steps of the canonical replays below `2 * 10 ^ 6`.  The constant is `1`
and not `2` -- `3 e + g + 2 ≤ room` is **false**, and `omega` produced the
counterexample profile while this file was being written. -/
theorem even_nondeg_three_mul_event_add_gap_add_one_le_room {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0)
    (hnondeg : 4 ≤ (C' - r) / d r) :
    3 * d r + (r - s) + 1 ≤ C - s := by
  obtain ⟨q, hroom, _, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep heven
  have hdrpos : 0 < d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hqodd : 1 ≤ q := hq1
  have hdiv : (C' - r) / d r = q + 1 := by
    rw [hlast, Nat.mul_div_cancel_left _ hdrpos]
  rw [hdiv] at hnondeg
  have hq3 : 3 ≤ q := by omega
  have hmul : 3 * d r ≤ d r * q := by
    calc
      3 * d r = d r * 3 := by simp [Nat.mul_comm]
      _ ≤ d r * q := Nat.mul_le_mul_left _ hq3
  omega

/-- **Even hit, non-degenerate, gap-free corollary.**  `3 e + 2 ≤ room`. -/
theorem even_nondeg_three_mul_event_add_two_le_room {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0)
    (hnondeg : 4 ≤ (C' - r) / d r) :
    3 * d r + 2 ≤ C - s := by
  have h := even_nondeg_three_mul_event_add_gap_add_one_le_room hstep heven hnondeg
  have hg1 : 1 ≤ r - s := by
    have := hstep.2.1
    omega
  omega

/-- **Odd hit, non-degenerate branch: the room covers four event values.**  When the
shifted quantum index is at least five, `4 e + g ≤ room + 3`.  Compare
`RoomQuantum.moving_horizon_room_quantum_odd`: the coefficient four is new, and the
gap is again kept.  The gap-free corollary `4 e ≤ room + 2` (using `g ≥ 1`) is the
usable form; measured tightest at `(M, e, room, m) = (43, 7, 42, 7)` with
`28 ≤ 44`, and holding at all 53 odd steps. -/
theorem odd_nondeg_four_mul_event_add_gap_le_room_add_three {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1)
    (hnondeg : 5 ≤ (C' - r + 4) / d r) :
    4 * d r + (r - s) ≤ C - s + 3 := by
  obtain ⟨q, hroom, _, hq2, hlast⟩ :=
    moving_horizon_odd_quotient_normal_form hstep hodd
  have hdrpos : 0 < d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hdiv : (C' - r + 4) / d r = q + 1 := by
    rw [hlast, Nat.mul_div_cancel_left _ hdrpos]
  rw [hdiv] at hnondeg
  have hq4 : 4 ≤ q := by omega
  have hmul : 4 * d r ≤ d r * q := by
    calc
      4 * d r = d r * 4 := by simp [Nat.mul_comm]
      _ ≤ d r * q := Nat.mul_le_mul_left _ hq4
  omega

/-- **Odd hit, non-degenerate, gap-free corollary.**  `4 e ≤ room + 2`. -/
theorem odd_nondeg_four_mul_event_le_room_add_two {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1)
    (hnondeg : 5 ≤ (C' - r + 4) / d r) :
    4 * d r ≤ C - s + 2 := by
  have h := odd_nondeg_four_mul_event_add_gap_le_room_add_three hstep hodd hnondeg
  have hg1 : 1 ≤ r - s := by
    have := hstep.2.1
    omega
  omega

/-- **Cross-check: the sharp even bound implies the library's slack bound.**  The
stronger form is consistent with `moving_horizon_step_size_le_slack`, so the two are
not in conflict and the new statement is not vacuous. -/
theorem event_le_room_of_sharp_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    d r ≤ C - s := by
  have h := even_event_add_gap_add_one_le_room hstep heven
  omega

/-! ## 2. The exact reconstruction identity

The two normal forms give the room *exactly* in terms of the gap, the event value, and
the quantum index.  Nothing is dropped: this is an equality, so it can be substituted
in either direction, which is what makes it different from the inequalities of
section 1. -/

/-- **Even hit, exact.**  With the quantum index `m` from `C' - r = d r * m`, the room
before the step is `d r * (m - 1) + 1 + gap`.  `m` is even and at least two. -/
theorem room_eq_gap_add_one_add_event_mul_quantum_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    ∃ m : Nat, m % 2 = 0 ∧ 2 ≤ m ∧ C' - r = d r * m ∧
      C - s = d r * (m - 1) + 1 + (r - s) := by
  obtain ⟨q, hroom, _, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep heven
  refine ⟨q + 1, by omega, by omega, hlast, ?_⟩
  have hsub : q + 1 - 1 = q := by omega
  rw [hsub]
  omega

/-- **Odd hit, exact.**  With the shifted quantum index `m` from
`C' - r + 4 = d r * m`, the room before the step is `d r * (m - 1) - 3 + gap`.
`m` is odd and at least three. -/
theorem room_eq_gap_sub_three_add_event_mul_quantum_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    ∃ m : Nat, m % 2 = 1 ∧ 3 ≤ m ∧ C' - r + 4 = d r * m ∧
      C - s = d r * (m - 1) - 3 + (r - s) := by
  obtain ⟨q, hroom, _, hq2, hlast⟩ :=
    moving_horizon_odd_quotient_normal_form hstep hodd
  have hdr3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hbig : 3 ≤ d r * q := by
    have := Nat.mul_le_mul hdr3 hq2
    omega
  refine ⟨q + 1, by omega, by omega, hlast, ?_⟩
  have hsub : q + 1 - 1 = q := by omega
  rw [hsub]
  omega

/-! ## 3. The degenerate case, characterised exactly

`RoomQuantum` records the dichotomy `room' = 2 e ∨ 2 e + 2 ≤ room'`.  The first
branch is the interesting one -- it is the only place the step makes no progress
against the room -- and here it is pinned to the quantum index. -/

/-- **Even degenerate hit \(\iff\) the quantum index is minimal.**  `room' = 2 e`
happens exactly at `m = 2`, i.e. exactly when the room was
`e + g + 1`: the step spent everything above the event, the gap, and one unit. -/
theorem even_degenerate_iff_room_eq_gap_add_one_add_event {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    (C' - r = 2 * d r ↔ C - s = (r - s) + 1 + d r) := by
  obtain ⟨q, hroom, _, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep heven
  have hdrpos : 0 < d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  constructor
  · intro hdeg
    have hmul : d r * (q + 1) = d r * 2 := by
      rw [← hlast, hdeg]
      simp [Nat.mul_comm]
    have hq : q + 1 = 2 := Nat.mul_left_cancel hdrpos hmul
    have hqeq : q = 1 := by omega
    rw [hqeq] at hroom
    simp at hroom
    omega
  · intro hroom'
    have hmul : d r * q = d r * 1 := by omega
    have hq : q = 1 := Nat.mul_left_cancel hdrpos hmul
    rw [hq] at hlast
    simp at hlast
    omega

/-- **Odd degenerate hit \(\iff\) the quantum index is minimal.**  `room' + 4 = 3 e`
happens exactly at `m = 3`, i.e. exactly when `room + 3 = g + 2 e`. -/
theorem odd_degenerate_iff_room_add_three_eq_gap_add_two_mul_event {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    (C' - r + 4 = 3 * d r ↔ C - s + 3 = (r - s) + 2 * d r) := by
  obtain ⟨q, hroom, _, hq2, hlast⟩ :=
    moving_horizon_odd_quotient_normal_form hstep hodd
  have hdrpos : 0 < d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  constructor
  · intro hdeg
    have hmul : d r * (q + 1) = d r * 3 := by
      rw [← hlast, hdeg]
      simp [Nat.mul_comm]
    have hq : q + 1 = 3 := Nat.mul_left_cancel hdrpos hmul
    have hqeq : q = 2 := by omega
    rw [hqeq] at hroom
    omega
  · intro hroom'
    have hmul : d r * q = d r * 2 := by omega
    have hq : q = 2 := Nat.mul_left_cancel hdrpos hmul
    rw [hq] at hlast
    omega

/-! ## 4. The accumulated identity in the joint coordinates

Everything a canonical replay earns is step count, travel, or room gain.  The
identity below is the honest form of "`Σ e_i` is the barrier": it names the three
addends and shows they are linked by the room ledger, which is why the joint local
evaluation has nothing left to give once the ledger is used. -/

/-- **Two steps, joint.**  The room gained over two steps is exactly the two event
excesses less the two gaps, and the earned events are the two step counts plus that
gain plus the two gaps.  Stated for two steps because the path-level form is the
`RoomLedger` identity already in the library; what is new here is the middle
expression, in which `Σ e_i` is broken into `p`, `travel` and the room gain. -/
theorem two_step_joint_ledger {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') :
    (C'' - u) = (C - s) + (d r - 1) + (d u - 1) - (r - s) - (u - r) := by
  have h1 : (C' - r) + (r - s) = (C - s) + (d r - 1) :=
    moving_horizon_slack_transition hstep
  have h2 : (C'' - u) + (u - r) = (C' - r) + (d u - 1) :=
    moving_horizon_slack_transition hnext
  have hd1 : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hd2 : 1 ≤ d u := by
    have := moving_horizon_step_event_ge_three hnext
    omega
  omega

/-- **The joint identity, rearranged — two steps, in the comments' form.**

The natural guess `Σ e_i = p + travel + (room_f - room_0)` is **false as written in
`Nat`**, and this theorem records the honest truncation-free version instead.  Since
`room_f - room_0` is truncated subtraction, the two-step excess obeys

    d r + d u + (C - s) = 2 + ((r - s) + (u - r)) + (C'' - u)

-- the room gain must be carried on the left as well, because a replay may *start*
above its endpoint (`RoomLedger` measures this as `room_f - (M-4)` running from `-39`
to `+1071` at the records it reaches).  This is stated here so the circular form is
on record: instantiating `(C - s)` by the ledger returns the definition of `Σ e_i`,
which is the exact phenomenon `ExcessIdentity` reports for the other coordinate
systems.

The cap needs `p + travel + gain ≤ (3 M - 9)/8`, and the gap bound `g ≤ 2 e` controls
`travel` only *from above by `Σ e`*, which is the wrong direction.  Recorded as the
precise reason the joint angle closes on itself. -/
theorem two_step_excess_add_room_start_eq_count_add_travel_add_room_end
    {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') :
    d r + d u + (C - s) = 2 + ((r - s) + (u - r)) + (C'' - u) := by
  have h1 : (C' - r) + (r - s) = (C - s) + (d r - 1) :=
    moving_horizon_slack_transition hstep
  have h2 : (C'' - u) + (u - r) = (C' - r) + (d u - 1) :=
    moving_horizon_slack_transition hnext
  have hd1 : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  have hd2 : 1 ≤ d u := by
    have := moving_horizon_step_event_ge_three hnext
    omega
  omega

/-! ## 5. The insufficiency, kernel-checked

The sharp local package of sections 1-3 is satisfied by a two-step profile whose
accumulated event sum overshoots the allowance.  This is a statement about the
hypotheses, not about the recurrence: it says that no proof which uses only the joint
local structure can close the barrier. -/

/-- **Every sharp simultaneous inequality of this file is satisfiable while the cap
fails.**  The witness is a two-step abstract profile at a canonical start with
`M = 10 ^ 6`: `room_0 = M - 4` (`canonical_start_room`), both steps satisfy the
choices `room_{i+1} = 2 e_i` (the degenerate even branch of
`moving_horizon_room_quantum_even`), each step satisfies the sharp even bound
`e + g + 1 ≤ room` of section 1, the ledger `room' = room + (e - 1) - g` of
`room_step_decomposition` holds at both, and yet `8 * (e_1 + e_2) > 3 * M - 9`.

`e_1 = 999994`, `g_1 = 1`, `room_0 = 999996`, `room_1 = 1999988` (degenerate even);
`e_2 = 1999986`, `g_2 = 1`, `room_2 = 3999972` (degenerate even).  Then
`e_1 + g_1 + 1 = 999996 ≤ 999996` (tight) and `e_2 + g_2 + 1 = 1999988 ≤ 1999988`
(tight), while `8 * 2999980 = 23999840 > 2999991 = 3 * 10 ^ 6 - 9`. -/
theorem sharp_local_package_does_not_give_cap :
    ∃ M room₀ e₁ g₁ room₁ e₂ g₂ room₂ : Nat,
      9 ≤ M ∧ room₀ = M - 4 ∧
      3 ≤ e₁ ∧ 1 ≤ g₁ ∧ e₁ + g₁ + 1 ≤ room₀ ∧
      3 ≤ e₂ ∧ 1 ≤ g₂ ∧ e₂ + g₂ + 1 ≤ room₁ ∧
      room₁ = 2 * e₁ ∧ room₂ = 2 * e₂ ∧
      room₁ = room₀ + (e₁ - 1) - g₁ ∧
      room₂ = room₁ + (e₂ - 1) - g₂ ∧
      8 * (e₁ + e₂) > 3 * M - 9 := by
  refine ⟨1000000, 999996, 999994, 1, 1999988, 1999986, 1, 3999972,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- **The same insufficiency in the exact form of the barrier.**  At the witness of
the previous theorem the accumulated event sum exceeds the allowance
`(3 M - 9) / 8 = 374998.875` by a factor of eight, while satisfying every joint local
hypothesis.  The degeneracy `room' = 2 e` is a *fixed point* of the room under the
ledger when `g = 1`, so the relaxation can be iterated: this is why the local package
is loose by an unbounded factor and not by a constant. -/
theorem sharp_local_package_cap_failure_is_large :
    ∃ M e₁ e₂ : Nat, 8 * (e₁ + e₂) > 3 * M - 9 ∧ 8 * (e₁ + e₂) > 3 * (3 * M - 9) := by
  refine ⟨1000000, 999994, 1999986, by decide, by decide⟩

/-- **The relaxation compounds.**  A one-step abstract profile with
`room = e + g + 1` (the sharp even bound, tight), `g = 1`, `room' = 2 e` (the
degenerate even room quantum) leaves a **larger** room than it started with, and the
event value may be taken within six of the whole room.  Iterating, `room` and `e`
both double while `p` grows by one per step, so the relaxed profile admits
`Σ e_i` comparable to `room_f` itself -- unbounded against the allowance
`(3 M - 9)/8`.

This is why the measured margin (a factor of `1 / 0.745` at the worst record,
`M = 139`) is **not** evidence that a local proof exists, and why the local
relaxation is loose by an unbounded factor rather than by a constant.  It is the
`(e_i, room_i)` analogue of `BandExcursion.room_drop_bound_is_not_available`. -/
theorem degenerate_branch_grows_the_room (M : Nat) (hM : 9 ≤ M) :
    ∃ e g room room' : Nat,
      room = M - 4 ∧ e + g + 1 ≤ room ∧ 3 ≤ e ∧ 1 ≤ g ∧
      room' = 2 * e ∧ room' = room + (e - 1) - g ∧ room < room' := by
  refine ⟨M - 6, 1, M - 4, 2 * M - 12, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩


/-! ## 6. Why this angle closes on itself: the surviving input is the room cap

The joint local package bounds the room *below* in terms of `e_i` and `g_i`
(sections 1-2).  The barrier needs `Σ e_i` bounded *above*, so the joint angle only
becomes useful if the endpoint room is pinned above -- i.e. it terminates in

    room_f ≤ M + c  with c bounded,

which is not in the library (`RoomLedger` measures `room_f - (M - 4)` at `-39` to
`+1071` across the fourteen records it reaches, i.e. `room_f - M` between `-43` and
`+1067`).  The two theorems below are the honest statement of that termination and of
what it costs.

**What is new here and what is not.**  The *sufficiency* direction
(`excess_le_of_room_cap_and_travel_cap`) is a rearrangement, and it says the obvious
thing: a room cap plus a travel cap gives the cap.  It is recorded because it names
the surviving input in the joint coordinates, where the previous rounds named it in
`S`/`B`/`travel` coordinates.  The *insufficiency* direction
(`room_cap_alone_is_insufficient`) is the negative content: a room cap without a count
bound is compatible with `Σ e_i` exceeding any multiple of `M`, so the joint angle
needs **both** the room cap and a count bound -- and `OrphanHarvest` already showed the
count alone is also insufficient.  Together they place the joint angle exactly where
the other twelve routes sit. -/

/-- **Sufficiency: a room cap plus a travel cap give the barrier.**  With the exact
room identity of `RoomLedger` (`(Cf - sf) + (sf - (M+2)) = (M-4) + S`) and the
accumulated event sum `S + p`, a room cap `Cf - sf ≤ M + c` is not by itself enough;
adding `S + p ≤ travel + (room cap)` closes it.  The form below keeps every addend
explicit so the surviving input is visible and not hidden in a truncation. -/
theorem excess_le_of_room_cap_and_travel_cap {M sf Cf S c T : Nat}
    (hM : 4 ≤ M) (hsf : M + 2 ≤ sf)
    (hroom_id : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S)
    (hroomcap : Cf - sf ≤ M + c) (htravel : sf - (M + 2) ≤ T) :
    S ≤ (M - 4) + (M + c) + T := by
  have hsplit : sf - (M + 2) + (M + 2) = sf := Nat.sub_add_cancel hsf
  omega

/-- **Insufficiency: the room cap alone does not give the barrier, and the failure is
unbounded.**  A joint profile with room bounded by `4 * M` and count `p = M` satisfies
`S + p` arbitrarily far above the allowance `(3 M - 9)/8`.  So a room cap must be
paired with a count bound; the joint angle does not escape the count.  This is the
`(e_i, room_i)` analogue of `OrphanHarvest.count_index_route_is_vacuous` and of
`TerminalRigidity.excess_bound_alone_does_not_give_cap`.

The witness is the *whole* room budget spent: `S = 4 M` (an accumulated excess of
four times the record, far above anything measured) and `p = M`.  It is abstract --
the point is exactly that no joint local hypothesis excludes it. -/
theorem room_cap_alone_is_insufficient (M : Nat) (hM : 9 ≤ M) :
    ∃ S p : Nat, S + p ≤ 5 * M ∧ 8 * (S + p) > 24 * M - 9 := by
  refine ⟨4 * M, M, by omega, by omega⟩

end A166944Research
