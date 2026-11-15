import A166944.RoomLedger

/-!
# A replay can leave the capped band and return to it

`Attempt.lean` records an open gap in prose:

> A genuine replay can leave and later re-enter the capped band; the single
> terminal-suffix package therefore needs an additional no-reentry argument.

The gap matters because a natural way to bound the terminal index is to treat the
tail of a replay as one package once it is inside the band `room <= M`, and that
argument silently assumes the replay never returns after leaving. This file shows
the assumption is false, with a witnessed replay, so such an argument has to
handle re-entry rather than exclude it.

The witness is the canonical replay from the record `M = 43`, which starts at
`(45, 84)` and runs

    (45,84) -> (47,88) -> (48,90) -> (51,96) -> (60,100) -> (66,132)

with rooms `41, 42, 45, 40, 66`. The room exceeds `M = 43` at `(51,96)` and is back
below it at `(60,100)`: the replay leaves the band and re-enters it.

The same happens at `M = 313`, where the replay visits `(342,648)` with room `306`,
then `(343,658)` with room `315 > 313`, then `(348,660)` with room `312 <= 313`.
One witness refutes the assumption, so only `M = 43` is formalised.
-/

namespace A166944Research

/-- Room of a state: how much horizon is left above the current index. -/
def room (s C : Nat) : Nat := C - s

/-! ## The steps of the `M = 43` replay -/

theorem step43_1 : IsMovingHorizonStep 45 84 47 88 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    have hj : j = 46 := by omega
    subst j
    decide
  · simp [IsMovingHorizonState, D, a]

theorem step43_2 : IsMovingHorizonStep 47 88 48 90 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    omega
  · simp [IsMovingHorizonState, D, a]

theorem step43_3 : IsMovingHorizonStep 48 90 51 96 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    -- 48 < j < 51 leaves only j = 49 or 50
    have h1 : j = 49 ∨ j = 50 := by omega
    rcases h1 with h | h <;> subst h <;> decide
  · simp [IsMovingHorizonState, D, a]

theorem step43_4 : IsMovingHorizonStep 51 96 60 100 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    -- 51 < j < 60: decide the whole finite range at once
    have h : j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 57 ∨
             j = 58 ∨ j = 59 := by omega
    rcases h with h | h | h | h | h | h | h | h <;> subst h <;> decide
  · simp [IsMovingHorizonState, D, a]

theorem step43_5 : IsMovingHorizonStep 60 100 66 132 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    -- 60 < j < 66
    have h : j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨ j = 65 := by omega
    rcases h with h | h | h | h | h <;> subst h <;> decide
  · simp [IsMovingHorizonState, D, a]

/-! ## The rooms along that replay -/

/-- The replay is inside the band at `(48,90)`: room `42 <= 43`. -/
theorem room_inside_before : room 48 90 = 42 ∧ room 48 90 ≤ 43 := by
  constructor <;> decide

/-- **The replay leaves the capped band.**  At `(51,96)` the room is `45 > 43`. -/
theorem room_exceeds_M : room 51 96 = 45 ∧ 43 < room 51 96 := by
  constructor <;> decide

/-- **The replay returns to the band.**  At the later state `(60,100)` the room is
back to `40 <= 43`. -/
theorem room_returns_inside : room 60 100 = 40 ∧ room 60 100 ≤ 43 := by
  constructor <;> decide

/-- **No-reentry is false.**  A canonical replay reaches a state inside the band,
then a later state outside it, then a still later state inside it again. So the
tail of a replay cannot be packaged as a single in-band suffix on the assumption
that leaving is permanent. -/
theorem replay_reenters_capped_band :
    room 48 90 ≤ 43 ∧ 43 < room 51 96 ∧ room 60 100 ≤ 43 ∧
    (48 : Nat) < 51 ∧ (51 : Nat) < 60 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end A166944Research
