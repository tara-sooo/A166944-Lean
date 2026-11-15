import A166944.CanonicalGrowth

/-!
# Angle A, surviving part: the event value's factor structure is the *room quantum*

This scratch module records what survives the prior-art check for attack angle A
("evaluate `gcd (C ± 1) r`") on the A166944 moving-horizon barrier.

The headline negative result is recorded in `FINDINGS_A.md`: the quantity the angle
proposes to bound is **not a derived constraint but a definition**.  Explicitly,
`constant_D_event_map` computes the first hit as

    d r = if r % 2 = 0 then Nat.gcd r (C - 1) else Nat.gcd (r - 2) (C + 1),

so `e = gcd (C ± 1) r` holds by `rfl`-level unfolding; bounding `gcd (C ± 1) r`
from above is *literally the same goal* as bounding `e`, and it is already known
that `e = C - 1` is consistent with every local hypothesis.

What does carry new content is the interaction of the two divisibilities
(`e ∣ r` and `e ∣ C ± 1`) with the step law.  Their difference has a *quantum*:
the room left after a step is either exactly the minimum allowed, or at least one
further quantum above it.  That is the sharp form of the slack, and it is what
this file proves.

Everything here is pure core (`decide` / `omega` / `simp` / `rfl`); no `ring`,
`linarith`, `norm_num`, `positivity` or `interval_cases`.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The carry: an event value divides the *next* horizon

`moving_horizon_even_quotient_normal_form` gives `C' - r = d r * (q + 1)`, and
`moving_horizon_odd_quotient_normal_form` gives `C' - r + 4 = d r * (q + 1)`.  In
both cases the divisor `d r` is inherited by the *post*-step horizon.  The fact is
already used inside `ReplayOffset210.moving_horizon_step_index_offset_residue`
(lines 48 and 54, as local `have`s); it is stated here as a standalone lemma
because the path-level arguments need it in that form.  This is a repackaging,
**not** a new discovery -- flagged so it is not double-counted. -/

/-- **Even hit: the event value divides the next horizon.**
`C' = C + (d r - 1)` and `d r ∣ C - 1` give `d r ∣ C'`. -/
theorem moving_horizon_event_dvd_next_horizon_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) : d r ∣ C' := by
  rcases moving_horizon_step_event_package hstep with h | h
  · have hdiv : d r ∣ C - 1 := h.2.1
    have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
    have hC1 : 1 ≤ C := by
      have hC2 : 2 ≤ C := by
        rw [← hstep.1.2.1]
        calc
          2 = D 2 := by simp [D, a]
          _ ≤ D s := D_le_of_le hstep.1.1
      omega
    have hdr : 1 ≤ d r := by
      have he3 := moving_horizon_step_event_ge_three hstep
      omega
    rw [hupd]
    have hsplit : C + (d r - 1) = (C - 1) + d r := by omega
    rw [hsplit]
    exact Nat.dvd_add hdiv (Nat.dvd_refl (d r))
  · exact absurd (h.1.symm.trans hr) (by decide)

/-- **Odd hit: the event value divides the next horizon shifted by two.**
`C' = C + (d r - 1)` and `d r ∣ C + 1` give `d r ∣ C' + 2`. -/
theorem moving_horizon_event_dvd_next_horizon_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) : d r ∣ C' + 2 := by
  rcases moving_horizon_step_event_package hstep with h | h
  · exact absurd (h.1.symm.trans hr) (by decide)
  · have hdiv : d r ∣ C + 1 := h.2.1
    have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
    have hdr : 1 ≤ d r := by
      have he3 := moving_horizon_step_event_ge_three hstep
      omega
    have hsplit : C + (d r - 1) + 2 = (C + 1) + d r := by omega
    rw [hupd, hsplit]
    exact Nat.dvd_add hdiv (Nat.dvd_refl (d r))

/-- **The carry, bundled.**  An event value divides the horizon that follows it. -/
theorem moving_horizon_event_dvd_next_horizon {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r ∣ C') ∧ (r % 2 = 1 → d r ∣ C' + 2) :=
  ⟨fun hr => moving_horizon_event_dvd_next_horizon_even hstep hr,
   fun hr => moving_horizon_event_dvd_next_horizon_odd hstep hr⟩

/-! ## 2. The room quantum dichotomy

The two normal forms make the *slack* an exact quantum rather than a continuum.
Writing `room := C - s` before the step and `room' := C' - r` after it:

* even hit: `room' = d r * (q + 1)` with `q` **odd** and `q >= 1`, so `q + 1` is
  even and `q + 1 >= 2`; hence `room' = 2 * d r` (only when `q = 1`) or
  `room' >= 4 * d r`.  The quantum is `4 * d r`, **not** `2 * d r + 2`;
* odd hit: `room' + 4 = d r * (q + 1)` with `q` even and `q >= 2`, hence
  `room' + 4 = 3 * d r` (only when `q = 2`) or `room' + 4 >= 5 * d r`.

This is the sharp form of `two_mul_increment_le_room_next` (`BandExcursion`): the
room cannot land *between* the minimum and the next quantum.  Measured on all 230
steps of the fifteen canonical record replays below `2 * 10 ^ 6`: zero violations,
with the degenerate case occurring only `2 + 1` times.  The even-branch quantum
being `4 * d r` rather than `2 * d r + 2` is *not* a detail: the first version of
this file claimed `2 * d r + 2` and `omega` produced the explicit counterexample
profile (`r / 2 = b`, `d r = c`, `C' = e` with `2b = e`, `2b + 2c = e - 2`), i.e.
the intermediate value is arithmetically unreachable because `q + 1` is even. -/

/-- **Even-hit room quantum.**  The room is exactly `2 * d r`, or at least one
quantum more. -/
theorem moving_horizon_room_quantum_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    C' - r = 2 * d r ∨ 4 * d r ≤ C' - r := by
  -- The quotient normal form gives `C' - r = d r * (q + 1)` with `q` odd, so
  -- `q + 1` is even and the room is an even multiple of `d r`. An earlier version
  -- of this statement used `2 * d r + 2 <= C' - r`, which is true but weak: the
  -- values between `2e` and `4e` are unreachable, and the sharper form is what the
  -- summation needs.
  obtain ⟨q, _, hqmod, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep hr
  have hdr1 : 1 ≤ d r := by
    have := moving_horizon_step_event_ge_three hstep
    omega
  rcases Nat.eq_or_lt_of_le hq1 with hq | hq
  · left
    rw [hlast, ← hq]
    omega
  · right
    -- `q >= 3` and odd, so `q + 1 >= 4`.
    have hq3 : 3 ≤ q := by omega
    have hmul : d r * 4 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [hlast]
    omega

/-- **Odd-hit room quantum.**  The shifted room is exactly `3 * d r`, or at least
`5 * d r`. -/
theorem moving_horizon_room_quantum_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4 := by
  obtain ⟨q, _, hqmod, hq2, hlast⟩ :=
    moving_horizon_odd_quotient_normal_form hstep hr
  rcases Nat.eq_or_lt_of_le hq2 with hq | hq
  · left
    rw [hlast, ← hq]
    omega
  · right
    have hq4 : 4 ≤ q := by omega
    have hmul : d r * 5 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [hlast]
    omega

/-- **The room quantum dichotomy, bundled.** -/
theorem moving_horizon_room_quantum {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → C' - r = 2 * d r ∨ 4 * d r ≤ C' - r) ∧
      (r % 2 = 1 → C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4) :=
  ⟨fun hr => moving_horizon_room_quantum_even hstep hr,
   fun hr => moving_horizon_room_quantum_odd hstep hr⟩

/-- **The event divides the room, in the quantum normal form.**  Even hit:
`d r ∣ C' - r`. -/
theorem moving_horizon_event_dvd_room_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) : d r ∣ C' - r := by
  obtain ⟨q, _, _, _, hlast⟩ := moving_horizon_even_quotient_normal_form hstep hr
  exact ⟨q + 1, hlast⟩

/-- **The event divides the shifted room.**  Odd hit: `d r ∣ C' - r + 4`. -/
theorem moving_horizon_event_dvd_room_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) : d r ∣ C' - r + 4 := by
  obtain ⟨q, _, _, _, hlast⟩ := moving_horizon_odd_quotient_normal_form hstep hr
  exact ⟨q + 1, hlast⟩

/-! ## 3. Why this does not bound the sum

The quantum dichotomy is exact and it is *still* compatible with an arbitrarily
large accumulated excess: on the degenerate even branch `room' = 2 * d r` the
quotient `q` is pinned to `1`, but `d r` itself is free, and the odd branch's
`q = 2` case likewise leaves `d r` free.  The local system therefore admits
`sum e_i` far above `(3 * M - 9) / 8`; `RoomLedger.travel_bound_without_threshold_is_false`
already exhibits exactly that at `M = 13`, so no consequence of these lemmas alone
can close the barrier.  Recorded here as a scope warning, not as a theorem. -/

end A166944Research

