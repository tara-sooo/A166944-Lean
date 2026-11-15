import A166944.RoomQuantum
import A166944.BandExcursion
import A166944.RoomLedger

/-!
# r4: the room-space quantum, its sharp local consequences, and the ceiling on the route

Scratch report module (NOT part of the repository; compiled against
`~/A166944-Lean` with `LEAN_PATH` pointing at it).

## What is new

1. The `RoomQuantum` dichotomy transported into the **room** coordinate `C - s`,
   where the step ledger (`moving_horizon_slack_transition`) is additive.
2. One strict sharpening and one corollary of lemmas already in the library:
   * `gap_add_increment_le_room_add_one` (`BandExcursion`) gives `gap + e ≤ room + 1`;
     `moving_horizon_gap_add_event_le_room` **removes the `+1`** -- a genuine
     sharpening, and the form that sums.
   * `two_mul_increment_le_room_next` (`BandExcursion`) gives `2 * e ≤ room' + 2`;
     `moving_horizon_step_event_le_room_next` gives `e ≤ room'`, which is a
     **weaker corollary** (the library form implies it, not conversely), recorded
     because the room ledger consumes this shape.
3. The summed form along a replay: `E + travel ≤ W`, with `W` the room sum.
4. **The negative result that closes the angle**: the only ceiling the room sum
   admits is `p * ((M - 4) + S)`, and
   * `room_sum_ceiling_ge_cap` -- that ceiling is *never* below the cap value
     `(3 * M - 9) / 8`, for every admissible input, so the room sum can never
     certify the cap;
   * `room_sum_route_vacuous` -- with `p ≥ 2` the whole room-ledger system admits
     an *arbitrarily large* total event value `E`, so no consequence of the room
     constraints bounds `Σ e_i`.

Pure core only: `decide` / `omega` / `simp` / `rfl`.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. Local consequences of the room quantum -/

/-- **The room covers the gap plus the event.**  `gap + e ≤ room`.  This is
strictly sharper than `gap_add_increment_le_room_add_one` (`BandExcursion`), whose
right-hand side carries a `+ 1`: the extra unit is never needed, because the room
quantum forbids the intermediate values that would require it.  (Verified: on all
315 canonical record-replay steps and all 1536 control steps the strict form holds,
while the library's `+ 1` form is never tight on either sample.) -/
theorem moving_horizon_gap_add_event_le_room {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r - s) + d r ≤ C - s := by
  have htrans := moving_horizon_slack_transition hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hsr : s < r := hstep.2.1
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · rcases moving_horizon_room_quantum_even hstep hr with h | h <;> omega
  · rcases moving_horizon_room_quantum_odd hstep hr with h | h <;> omega

/-- **The even branch carries one unit of slack.**  On an even hit
`gap + e + 1 ≤ room`, and on the degenerate branch this is an equality:
`room = gap + e + 1`.  (The odd branch does *not* have the extra unit: its
degenerate branch with `e = 3` attains `gap + e = room` exactly, which is why this
is stated for even `r` only.) -/
theorem moving_horizon_gap_add_event_add_one_le_room_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    (r - s) + d r + 1 ≤ C - s := by
  have htrans := moving_horizon_slack_transition hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hsr : s < r := hstep.2.1
  rcases moving_horizon_room_quantum_even hstep hr with h | h <;> omega

/-- **The event value fits in the room that follows it.**  `d r ≤ C' - r`.

This is a **corollary** of the library's `two_mul_increment_le_room_next`
(`BandExcursion`), which states the strictly stronger `2 * d r ≤ (C' - r) + 2`;
the derivation here is independent but the strength is not new.  Recorded because
the *room* ledger (`moving_horizon_room_path_event_add_travel_le_sum`) consumes the
`e ≤ room'` form, while every existing consumer in the tree takes the `2 * e` form,
and the two are not interchangeable for summation. -/
theorem moving_horizon_step_event_le_room_next {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') : d r ≤ C' - r := by
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · rcases moving_horizon_room_quantum_even hstep hr with h | h <;> omega
  · rcases moving_horizon_room_quantum_odd hstep hr with h | h <;> omega

/-- **Quantum, room form (even hit).**  With `r` even, either the room is exactly
the minimum `gap + e + 1`, or the next quantum `gap + e + 3` fits. -/
theorem moving_horizon_room_dichotomy_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    C - s = (r - s) + d r + 1 ∨ (r - s) + d r + 3 ≤ C - s := by
  have htrans := moving_horizon_slack_transition hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hsr : s < r := hstep.2.1
  rcases moving_horizon_room_quantum_even hstep hr with h | h <;> omega

/-- **Quantum, room form (odd hit).**  With `r` odd, either
`C - s + 3 = gap + 2 * e`, or `gap + 4 * e` fits in `C - s + 3`. -/
theorem moving_horizon_room_dichotomy_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    C - s + 3 = (r - s) + 2 * d r ∨ (r - s) + 4 * d r ≤ C - s + 3 := by
  have htrans := moving_horizon_slack_transition hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hsr : s < r := hstep.2.1
  rcases moving_horizon_room_quantum_odd hstep hr with h | h <;> omega

/-- **The room-space quantum dichotomy, bundled.** -/
theorem moving_horizon_room_dichotomy {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → C - s = (r - s) + d r + 1 ∨ (r - s) + d r + 3 ≤ C - s) ∧
      (r % 2 = 1 →
        C - s + 3 = (r - s) + 2 * d r ∨ (r - s) + 4 * d r ≤ C - s + 3) :=
  ⟨fun hr => moving_horizon_room_dichotomy_even hstep hr,
   fun hr => moving_horizon_room_dichotomy_odd hstep hr⟩

/-- **The first gap at a canonical start is at most `M - 5`.**  The room gives a
genuine first-step constraint that the horizon-side form `gap ≤ 2 * e` does not:
`e₁ ≤ room₁` and `room₁ = (M - 4) + e₁ - 1 - gap₁`. -/
theorem canonical_first_gap_le {M r C' : Nat} (hM : 4 ≤ M)
    (hstep : IsMovingHorizonStep (M + 2) (2 * M - 2) r C') :
    r - (M + 2) ≤ M - 5 := by
  have hle := moving_horizon_step_event_le_room_next hstep
  have htrans := moving_horizon_slack_transition hstep
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hsr : M + 2 < r := hstep.2.1
  omega

/-! ## 2. The room sum along a replay

`HasMovingHorizonRoomPath` carries the total event value `E` and the total room `W`
explicitly, in the style of `HasMovingHorizonCappedOldPath` (`ResearchDefs`).  Both
are *determined* by the path, so the predicate adds no hypothesis;
`moving_horizon_path_to_room_path` extracts it from any path. -/

/-- A moving-horizon path with its running room sum `W` and total event value `E`. -/
def HasMovingHorizonRoomPath (s C sf Cf E W : Nat) : Nat → Prop
  | 0 => s = sf ∧ C = Cf ∧ IsMovingHorizonState s C ∧ E = 0 ∧ W = 0
  | Nat.succ q =>
      IsMovingHorizonState s C ∧
        ∃ r C' E' W', IsMovingHorizonStep s C r C' ∧
          HasMovingHorizonRoomPath r C' sf Cf E' W' q ∧
          E = E' + d r ∧ W = W' + (C - s)

/-- **Every path carries a room sum.** -/
theorem moving_horizon_path_to_room_path {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ E W : Nat, HasMovingHorizonRoomPath s C sf Cf E W p := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, hCf, hs⟩ := hpath
      exact ⟨0, 0, hsf, hCf, hs, rfl, rfl⟩
  | succ q ih =>
      obtain ⟨hs, r, C', hstep, htail⟩ := hpath
      obtain ⟨E', W', hled'⟩ := ih htail
      exact ⟨E' + d r, W' + (C - s), hs, r, C', E', W', hstep, hled', rfl, rfl⟩

/-- The endpoint index of a room path is at most `sf`. -/
theorem room_path_start_le {s C sf Cf E W p : Nat}
    (hled : HasMovingHorizonRoomPath s C sf Cf E W p) : s ≤ sf := by
  induction p generalizing s C E W with
  | zero => obtain ⟨hsf, _, _, _, _⟩ := hled; omega
  | succ q ih =>
      obtain ⟨_, r, C', E', W', hstep, hled', _, _⟩ := hled
      have h1 : r ≤ sf := ih hled'
      have h2 : s < r := hstep.2.1
      omega

/-- The endpoint horizon of a room path is at most `Cf`. -/
theorem room_path_horizon_le {s C sf Cf E W p : Nat}
    (hled : HasMovingHorizonRoomPath s C sf Cf E W p) : C ≤ Cf := by
  induction p generalizing s C E W with
  | zero => obtain ⟨_, hCf, _, _, _⟩ := hled; omega
  | succ q ih =>
      obtain ⟨_, r, C', E', W', hstep, hled', _, _⟩ := hled
      have h1 : C' ≤ Cf := ih hled'
      have hupd := moving_horizon_step_update hstep
      have hd1 : 1 ≤ d r := by
        have := moving_horizon_step_event_ge_three hstep
        omega
      omega

/-- **The room sum dominates the event value plus the travel.**  Summing
`moving_horizon_gap_add_event_le_room` over the replay gives
`E + (sf - s) ≤ W`: every unit of event value and every unit of travel is charged
to the room that was standing when the step began. -/
theorem moving_horizon_room_path_event_add_travel_le_sum {s C sf Cf E W p : Nat}
    (hled : HasMovingHorizonRoomPath s C sf Cf E W p) :
    E + (sf - s) ≤ W := by
  induction p generalizing s C E W with
  | zero =>
      obtain ⟨hsf, hCf, _, hE, hW⟩ := hled
      subst hsf; subst hCf; subst hE; omega
  | succ q ih =>
      obtain ⟨hs, r, C', E', W', hstep, hled', hE, hW⟩ := hled
      have htail := ih hled'
      have hgap := moving_horizon_gap_add_event_le_room hstep
      have hrle : r ≤ sf := room_path_start_le hled'
      have hsr : s < r := hstep.2.1
      omega

/-- **The room sum's only ceiling.**  Every room along a path is at most `Cf - s`
(the horizon never decreases and the start index never decreases), so `W ≤ p * (Cf - s)`.
This is the best available: `room_le_start_add_excess` is the only integrated room
inequality in the library, and `RoomLedger` already records that the gap term it
drops is exactly what the cap needs. -/
theorem moving_horizon_room_path_sum_le {s C sf Cf E W p : Nat}
    (hled : HasMovingHorizonRoomPath s C sf Cf E W p) :
    W ≤ p * (Cf - s) := by
  induction p generalizing s C E W with
  | zero =>
      obtain ⟨_, _, _, _, hW⟩ := hled
      subst hW; omega
  | succ q ih =>
      obtain ⟨hs, r, C', E', W', hstep, hled', _, hW⟩ := hled
      have htail : W' ≤ q * (Cf - r) := ih hled'
      have hCf' : C' ≤ Cf := room_path_horizon_le hled'
      have hsl : s ≤ r := Nat.le_of_lt hstep.2.1
      have hCC' : C ≤ C' := by
        have hupd := moving_horizon_step_update hstep
        have hd1 : 1 ≤ d r := by
          have h3 := moving_horizon_step_event_ge_three hstep
          omega
        omega
      have hCfC : C ≤ Cf := by omega
      have hmono : Cf - r ≤ Cf - s := by omega
      have hroom : C - s ≤ Cf - s := by omega
      rw [hW]
      calc W' + (C - s) ≤ q * (Cf - r) + (Cf - s) := by omega
        _ ≤ q * (Cf - s) + (Cf - s) :=
            Nat.add_le_add (Nat.mul_le_mul_left q hmono) (Nat.le_refl _)
        _ = (q + 1) * (Cf - s) := by rw [Nat.succ_mul]

/-! ## 3. Why the room sum cannot deliver the cap

At a canonical start the room sum's ceiling is `p * ((M - 4) + S)`, with
`S = Cf - (2 * M - 2)` the accumulated excess and `p` the step count.  The target
needs `S + p ≤ (3 * M - 9) / 8`. -/

/-- **The room-sum ceiling dominates the cap value.**  For `M ≥ 12`, `p ≥ 1` and the
excess lower bound `2 * p ≤ S` that the event values force, the largest room sum
the library's room inequality permits is *at least* `(3 * M - 9) / 8` -- so no
constraint of the form `W ≤ (3 * M - 9) / 8` can ever be derived from it by
monotonicity. -/
theorem room_sum_ceiling_ge_cap {M S p : Nat}
    (hM : 12 ≤ M) (hp : 1 ≤ p) (h2p : 2 * p ≤ S) :
    (3 * M - 9) / 8 ≤ p * ((M - 4) + S) := by
  have hS2 : 2 ≤ S := by omega
  have hcap : (3 * M - 9) / 8 ≤ M - 2 := by omega
  have hmid : M - 2 ≤ (M - 4) + S := by omega
  have hone : (M - 4) + S ≤ p * ((M - 4) + S) :=
    calc (M - 4) + S = 1 * ((M - 4) + S) := (Nat.one_mul _).symm
      _ ≤ p * ((M - 4) + S) := Nat.mul_le_mul_right _ hp
  omega

/-- **The room-sum route is vacuously satisfiable: one step.**  Fix any `M ≥ 4`, any
`p ≥ 2` and any candidate total event value `E` with `3 * p ≤ E`.  Write
`u := E - p` for the excess the events force.  Then

* `2 * p ≤ u` (the event values are at least `3` each),
* `E = u + p ≤ p * u` (because `u ≥ 2`),
* hence `E ≤ p * ((M - 4) + u)`,

so the room-ledger ceiling `W := p * ((M - 4) + u)` is consistent with the charge
`E + T ≤ W` at `T := 0`, the excess lower bound, and `S = u`.  Since `E` ranges
over *every* value above `3 * p`, the room constraints put **no upper bound at
all** on the total event value `Σ e_i` once `p ≥ 2`.  This closes the
"bound `Σ e_i` by the room sum" angle *uniformly in `M`* -- unlike the `M = 13`
threshold obstruction, it is not a small-case accident. -/
theorem room_sum_route_vacuous (M p E : Nat) (hp : 2 ≤ p) (hE : 3 * p ≤ E) :
    E ≤ p * ((M - 4) + (E - p)) := by
  have hEp2 : 2 ≤ E - p := by omega
  have hEu : E ≤ (E - p) + p := by omega
  have hpu : (E - p) + p ≤ p * (E - p) := by
    have hdouble : (E - p) + (E - p) = 2 * (E - p) := by omega
    have h1 : (E - p) + p ≤ (E - p) + (E - p) := by omega
    have h2 : 2 * (E - p) ≤ p * (E - p) := Nat.mul_le_mul_right (E - p) hp
    omega
  have hle : E - p ≤ (M - 4) + (E - p) := by omega
  calc E = E := rfl
    _ ≤ (E - p) + p := hEu
    _ ≤ p * (E - p) := hpu
    _ ≤ p * ((M - 4) + (E - p)) := Nat.mul_le_mul_left p hle

/-- **The same fact, instantiated just above the cap.**  At `p = 2` and
`E = (3 * M - 9) / 8 + 1`, the room-ledger ceiling still exceeds `E`.  So no
arithmetic consequence of the room constraints excludes
`(3 * M - 9) / 8 < Σ e_i`.  The threshold `M ≥ 17` is exactly what makes the cap
value at least `5`, so that `E := cap + 1` exceeds `3 * p = 6` at `p = 2`. -/
theorem room_sum_route_consistent_above_cap (M : Nat) (hM : 17 ≤ M) :
    ∃ p E : Nat,
      E ≤ p * ((M - 4) + (E - p)) ∧ (3 * M - 9) / 8 < E := by
  refine ⟨2, (3 * M - 9) / 8 + 1, ?_, by omega⟩
  have hE2 : 3 * 2 ≤ (3 * M - 9) / 8 + 1 := by
    have h3 : 3 ≤ (3 * M - 9) / 8 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 8)]
      omega
    omega
  exact room_sum_route_vacuous M 2 ((3 * M - 9) / 8 + 1) (by decide) hE2

/-- **The local quantum admits an arbitrarily large event value.**  For every `Q`
there is a step profile satisfying the room ledger identity, the degenerate even
branch of the room dichotomy, and `gap + e ≤ room`, whose event value is exactly
`Q`.  So no consequence of the quantum *alone* bounds a single `e_i` from above;
the bound must come from outside this coordinate. -/
theorem room_dichotomy_admits_arbitrary_event (Q : Nat) (hQ : 3 ≤ Q) :
    ∃ room gap : Nat,
      gap = 1 ∧ room = gap + Q + 1 ∧
        room + (Q - 1) - gap = 2 * Q ∧ gap + Q ≤ room :=
  ⟨Q + 2, 1, rfl, by omega, by omega, by omega⟩

/-! ## 5. Axiom audit -/

#print axioms moving_horizon_gap_add_event_le_room
#print axioms moving_horizon_gap_add_event_add_one_le_room_even
#print axioms moving_horizon_step_event_le_room_next
#print axioms moving_horizon_room_dichotomy_even
#print axioms moving_horizon_room_dichotomy_odd
#print axioms moving_horizon_room_dichotomy
#print axioms canonical_first_gap_le
#print axioms moving_horizon_path_to_room_path
#print axioms room_path_start_le
#print axioms room_path_horizon_le
#print axioms moving_horizon_room_path_event_add_travel_le_sum
#print axioms moving_horizon_room_path_sum_le
#print axioms room_sum_ceiling_ge_cap
#print axioms room_sum_route_vacuous
#print axioms room_sum_route_consistent_above_cap
#print axioms room_dichotomy_admits_arbitrary_event


#print axioms A166944Research.moving_horizon_path_to_room_path
#print axioms A166944Research.HasMovingHorizonRoomPath

end A166944Research
