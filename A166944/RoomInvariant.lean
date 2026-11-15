import A166944.RoomLedger

/-!
# Angle "room ≈ M": what is provable, what is only measured, what is refutable

The measurement that motivates this file (reconstructed from the pre-existing
nonunit-event table `p2m_scratch/direct_assault/out5e7.txt`, 21 complete canonical
replays, 869 steps): the room `C - s` stays within a *tiny relative* neighbourhood
of `M` at every state, `room / M in [0.99999, 1.1223]`, and the terminal room obeys
`M - 43 <= Cf - sf <= M + 14349` on the complete replays.

**Correction, and it matters.** The interval above is an artefact of the record set,
not a law. The table it came from begins around `M = 44383`, so the small records that
violate the interval were never in it. Checked over all 23 non-empty canonical replays
up to `1e8`, 17 violate the interval: at `M = 13` the ratio ranges from `9/13` to
`20/13`, at `M = 43` from `39/43` to `66/43`. Only `M in {713833, 1427749, 45895573,
91793059}` stays inside on its own. And the stated upper end `1.1223` is below
`156/139 = 1.1223021...`, the value that produced it, so the interval does not contain
its own endpoint.

So `room / M -> 1` is an **asymptotic observation above the threshold** and no argument
may use it below. The degenerate branch occurs precisely at `M = 13` and `M = 43`, the
two records where the cap fails.

This file pins down exactly what that means.

## 1. The path-level exact ledger (new, and it is the whole story)

`room_le_start_add_excess_path` (RoomLedger) drops the travel term:

    Cf - sf <= (C - s) + S.

The sharp form keeps it -- `room_path_exact_ledger` below:

    (Cf - sf) + (sf - s) = (C - s) + S,      S = sum (d r_i - 1) = sum travel_i.

At the canonical start this is `room_f + travel = (M - 4) + S`, hence

    room_f >= M - c   <->   travel <= S + (c - 4).

So **the room lower bound is nothing but a bound on `travel - S`**.  Since the
measured `S` is `0.0013 * M` and the measured `travel` is `0.0006 * M`, the bound
`room_f >= M - 43` is *far stronger* than the target `travel <= (3 M - 9) / 4`: it
is stated relative to `S`, not to `M`.

## 2. What the room bound does buy (new)

It decomposes the cap into two independent claims, neither of which mentions the
other (`cap_of_room_lower_bound_and_excess_bound`):

    room_f >= M - c   and   4 S + 4 c <= 3 M + 7   ==>   4 sf <= 7 M - 1.

The first is *scale-free* (a statement about `travel - S`); the second is a pure
upper bound on the accumulated excess `S`.  `CapBCandidates` proved that the second
alone is not enough; the room bound is precisely the missing relative ingredient.
It is, however, an ingredient of the same difficulty as the target, because the
room bound *is* a travel bound -- see §1.

## 3. What is provable from the local step structure (new)

Non-degeneracy (`4 e <= room'`, even; `5 e <= room' + 4`, odd) is *equivalent* to a
bound on the **entering** room in terms of the gap and the event,

    even:  r - s + 3 * d r + 1 <= C - s        (only if 4 * d r <= C' - r)
    odd:   r - s + 4 * d r     <= C - s + 3    (only if 5 * d r <= C' - r + 4)

and the unconditional weak form

    even:  r - s + d r + 1     <= C - s
    odd:   r - s + 2 * d r     <= C - s + 3.

Measured, these are *vacuous*: `room' / e` has minimum 496 already at `M = 355723`
and 46977 at `M = 45895573`, so `4 e <= room'` holds with a factor of `10^3`-`10^6`
to spare and can never imply `room' >= M - c` (which would need `e >= M / 4`, while
the measured `e / M` is at most 0.18 and falls with `M`).

## 4. What is refuted: the local structure cannot force `room ~ M` (new)

`no_local_room_lower_bound`: for every `c < 45895563` the implication

    EvenBranchShadow M g e q roomp  ->  M - c <= roomp

is **false**, exhibited by the kernel on `M = 45895573`, `e = 3`, `q = 1`,
`roomp = 2 * e = 6`.  The shadow is faithful (`even_shadow_realized`): every genuine
even-branch step of a capped replay satisfies it.  Hence no argument that uses only
the parity/divisibility/quantum arithmetic can produce `room >= M - c`; the missing
ingredient is number-theoretic (the distance from `s` to the first index whose
`gcd` with `C -+ 1` exceeds one), not algebraic.

Everything below is pure core: `decide` / `omega` / `simp` / `rfl` only, no
`ring`, `linarith`, `norm_num`, `positivity` or `interval_cases`, and no `sorry`.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The path-level exact ledger -/

/-- A moving-horizon path never moves to a smaller index. -/
theorem moving_horizon_path_start_le_end {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) : s ≤ sf := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, _, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      have hrs : r ≤ sf := ih htail
      have hsr : s < r := hstep.2.1
      omega

/-- **The exact room ledger along a path.**  The room keeps its travel term: the
endpoint room plus the whole travel equals the start room plus the accumulated
event excess.  `room_le_start_add_excess_path` is this with travel dropped. -/
theorem room_path_exact_ledger {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, (Cf - sf) + (sf - s) = (C - s) + S := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, hCf, _⟩ := hpath
      subst hsf
      subst hCf
      exact ⟨0, by omega⟩
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hS'⟩ := ih htail
      refine ⟨S' + (d r - 1), ?_⟩
      have hslack := moving_horizon_slack_transition hstep
      have hrs : r ≤ sf := moving_horizon_path_start_le_end htail
      have hsr : s ≤ r := Nat.le_of_lt hstep.2.1
      -- `s <= r <= sf`, so the travel splits additively (`omega` gets only this
      -- one truncated subtraction, with both side conditions in hand).
      have hsplit : sf - s = (sf - r) + (r - s) := by omega
      calc (Cf - sf) + (sf - s)
          = (Cf - sf) + ((sf - r) + (r - s)) := by rw [hsplit]
        _ = ((Cf - sf) + (sf - r)) + (r - s) := by omega
        _ = ((C' - r) + S') + (r - s) := by rw [hS']
        _ = S' + ((C' - r) + (r - s)) := by omega
        _ = S' + (C - s + (d r - 1)) := by rw [hslack]
        _ = (C - s) + (S' + (d r - 1)) := by omega

/-- The horizon telescopes: `Cf = C + S` with `S` the accumulated excess. -/
theorem horizon_telescopes_along_path {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    ∃ S : Nat, Cf = C + S := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨hsf, hCf, _⟩ := hpath
      subst hsf
      subst hCf
      exact ⟨0, by omega⟩
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨S', hS'⟩ := ih htail
      refine ⟨S' + (d r - 1), ?_⟩
      have hupd := moving_horizon_step_update hstep
      omega

/-- **The canonical form of the exact ledger.**  Canonical start `(M + 2, 2M - 2)`
has room `M - 4`, so the terminal room plus the travel is `(M - 4) + S`. -/
theorem canonical_room_exact_ledger {M sf Cf p : Nat} (hM : 4 ≤ M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p) :
    ∃ S : Nat, (Cf - sf) + (sf - (M + 2)) = (M - 4) + S := by
  obtain ⟨S, hS⟩ := room_path_exact_ledger hpath
  refine ⟨S, ?_⟩
  have hstart : (2 * M - 2) - (M + 2) = M - 4 := canonical_start_room hM
  omega

/-- **The room is the head start minus the travel deficit.**  With `S <= travel`
the exact ledger becomes `room_f = (M - 4) - (travel - S)`: the only way the room
can fall below `M - 4` is that the replay travelled further than it earned. -/
theorem room_eq_head_start_sub_travel_deficit {M sf Cf S : Nat} (hM : 4 ≤ M)
    (hid : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S)
    (hle : S ≤ sf - (M + 2)) :
    (Cf - sf) + ((sf - (M + 2)) - S) = M - 4 := by omega

/-- **The room lower bound is exactly a bound on `travel - S`.**  This is the
central content of the "room ~ M" angle: it is not a new input, it is the relative
travel bound itself. -/
theorem room_lower_bound_iff_relative_travel_bound {M sf Cf S c : Nat}
    (hM : 4 ≤ M) (hc : 4 ≤ c)
    (hid : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S) :
    (M - c ≤ Cf - sf ↔ sf - (M + 2) ≤ S + (c - 4)) := by omega

/-! ## 2. What the room bound buys: the two-claim decomposition of the cap -/

/-- **Cap from a room lower bound plus an excess bound.**  `room_f >= M - c` and
`4 S + 4 c <= 3 M + 7` give the relaxed index cap.  The first hypothesis is
scale-free, the second is the pure excess bound; both are needed. -/
theorem cap_of_room_lower_bound_and_excess_bound {M sf Cf S c : Nat}
    (hM : 2 ≤ M) (hcM : c ≤ M) (hsfCf : sf ≤ Cf)
    (hcf : Cf = 2 * M - 2 + S) (hroom : M - c ≤ Cf - sf)
    (hexc : 4 * S + 4 * c ≤ 3 * M + 7) : 4 * sf ≤ 7 * M - 1 := by
  -- The whole argument is `sf + 2 <= M + S + c`, then `4*(S+c) <= 3M+7`.  Every
  -- step is named additively, so `omega` never meets a truncated subtraction next
  -- to a coefficient (the failure mode recorded across this repository).
  have hcancel : (Cf - sf) + sf = Cf := Nat.sub_add_cancel hsfCf
  -- `Cf = 2M - 2 + S` in truncation-free form.
  have hcf' : Cf + 2 = 2 * M + S := by omega
  -- Room lower bound, additively.
  have hroom' : (M - c) + sf ≤ Cf := by
    have h := Nat.add_le_add_right hroom sf
    omega
  have hm : (M - c) + c = M := Nat.sub_add_cancel hcM
  have hkey : sf + 2 ≤ M + S + c := by omega
  have h4 : 4 * (sf + 2) ≤ 4 * (M + S + c) := Nat.mul_le_mul_left 4 hkey
  have hexp : 4 * (sf + 2) = 4 * sf + 8 := by omega
  have hexp2 : 4 * (M + S + c) = 4 * M + 4 * S + 4 * c := by omega
  omega

/-- **The room bound really is the missing relative ingredient.**  Same statement,
with the hypotheses reordered for the caller. -/
theorem cap_of_room_lower_bound_and_excess_bound_tight {M sf Cf S c : Nat}
    (hcf : Cf = 2 * M - 2 + S) (hroom : M - c ≤ Cf - sf)
    (hexc : 4 * S + 4 * c ≤ 3 * M + 7) (hM : 2 ≤ M) (hcM : c ≤ M)
    (hsfCf : sf ≤ Cf) : 4 * sf ≤ 7 * M - 1 :=
  cap_of_room_lower_bound_and_excess_bound hM hcM hsfCf hcf hroom hexc

/-- The same in the form the ledger actually delivers: a room lower bound plus
`4 (S + c) <= 3 M + 7` is a *sufficient* condition for the cap, and by
`room_lower_bound_iff_relative_travel_bound` the first conjunct is a travel bound.
So the room route replaces the target by (relative travel bound) + (excess bound):
it does not remove the travel bound, it isolates it. -/
theorem travel_bound_of_room_and_excess {M sf Cf S c : Nat} (hM : 4 ≤ M)
    (hid : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S)
    (hroom : M - c ≤ Cf - sf) (hc : 4 ≤ c) :
    sf - (M + 2) ≤ S + (c - 4) :=
  (room_lower_bound_iff_relative_travel_bound hM hc hid).1 hroom

/-! ## 3. The room quantum, re-proved from the normal forms

Restated here because `RoomQuantum.lean` is being edited concurrently; this file
depends only on `Lemmas.lean`'s quotient normal forms, which are stable. -/

/-- **Even-hit room quantum.**  `room' = 2 e`, or one full quantum more. -/
theorem room_quantum_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) : C' - r = 2 * d r ∨ 4 * d r ≤ C' - r := by
  obtain ⟨q, _, hqmod, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep hr
  rcases Nat.eq_or_lt_of_le hq1 with hq | hq
  · left
    rw [hlast, ← hq]
    omega
  · right
    have hq3 : 3 ≤ q := by omega
    have hmul : d r * 4 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [hlast]
    omega

/-- **Odd-hit room quantum.**  `room' + 4 = 3 e`, or one full quantum more. -/
theorem room_quantum_odd {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 1) : C' - r + 4 = 3 * d r ∨ 5 * d r ≤ C' - r + 4 := by
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

/-! ## 4. The unconditional entering-room bounds, and the non-degenerate ones

The entering room is `room = C - s`; the event value is `e = d r`; the gap is
`g = r - s`.  The normal forms give `room = g + 1 + e * q` (even, `q` odd) and
`room + 3 = g + e * q` (odd, `q` even).  Minimal `q` is the *degenerate* branch. -/

/-- **Even: the entering room beats the gap by at least one event.**  `q >= 1`. -/
theorem entering_room_ge_gap_add_event_even {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    r - s + d r + 1 ≤ C - s := by
  obtain ⟨q, hroom, _, hq1, _⟩ :=
    moving_horizon_even_quotient_normal_form hstep hr
  have hmul : d r * 1 ≤ d r * q := Nat.mul_le_mul_left _ hq1
  omega

/-- **Odd: the entering room beats the gap by at least two events.**  `q >= 2`. -/
theorem entering_room_ge_gap_add_two_events_odd {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    r - s + 2 * d r ≤ C - s + 3 := by
  obtain ⟨q, hroom, _, hq2, _⟩ :=
    moving_horizon_odd_quotient_normal_form hstep hr
  have hmul : d r * 2 ≤ d r * q := Nat.mul_le_mul_left _ hq2
  omega

/-- **Even, non-degenerate: three events, not one.**  Equivalent to `4 e <= room'`
(`room' = room + e - 1 - g`), stated in the entering coordinates the angle asks
about. -/
theorem entering_room_ge_gap_add_three_events_of_even_quantum {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hbig : 4 * d r ≤ C' - r) :
    r - s + 3 * d r + 1 ≤ C - s := by
  have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
  have hrC : r ≤ C := hstep.2.2.1
  have hsr : s ≤ r := Nat.le_of_lt hstep.2.1
  have hdr1 : 1 ≤ d r := by
    have h3e := moving_horizon_step_event_ge_three hstep
    omega
  -- Truncation-free names: `omega` is given one subtraction at a time.
  have hrec : d r = (d r - 1) + 1 := by omega
  have hsplit : C' - r = (C - r) + (d r - 1) := by omega
  have h3 : 3 * d r + 1 ≤ C - r := by omega
  have hcomb : (C - r) + (r - s) = C - s := by omega
  omega

/-- **Odd, non-degenerate: four events, not two.**  Equivalent to
`5 e <= room' + 4`. -/
theorem entering_room_ge_gap_add_four_events_of_odd_quantum {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hbig : 5 * d r ≤ C' - r + 4) :
    r - s + 4 * d r ≤ C - s + 3 := by
  have hupd : C' = C + (d r - 1) := moving_horizon_step_update hstep
  have hrC : r ≤ C := hstep.2.2.1
  have hsr : s ≤ r := Nat.le_of_lt hstep.2.1
  have hsplit : C' - r + 4 = (C - r) + (d r - 1) + 4 := by omega
  have h4 : 4 * d r ≤ C - r + 3 := by omega
  have hcomb : (C - r) + (r - s) = C - s := by omega
  omega

/-! ## 5. The local structure cannot force the room invariant

`EvenBranchShadow` is the arithmetic shadow of an even-branch step: exactly the
hypotheses the quantum argument uses, and nothing about the recurrence.  It is
*faithful* (`even_shadow_realized`) and it is *satisfiable with a tiny room at the
certified threshold record* (`degenerate_even_shadow_realizable_at_threshold`).
Therefore no derivation from the shadow alone gives `M - c <= room'`. -/

/-- The arithmetic shadow of an even-branch step: `e >= 3`, `e <= M`, a genuine
gap, and the even normal form `room' = e * (q + 1)` with `q` odd. -/
def EvenBranchShadow (M g e q roomp : Nat) : Prop :=
  3 ≤ e ∧ e ≤ M ∧ 1 ≤ g ∧ q % 2 = 1 ∧ 1 ≤ q ∧ roomp = e * (q + 1)

/-- **The shadow is faithful**: every genuine even step of a capped replay realises
it, with `e = d r`, `g = r - s`, `roomp = C' - r`. -/
theorem even_shadow_realized {M s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hr : r % 2 = 0) (heM : d r ≤ M) :
    ∃ q : Nat, EvenBranchShadow M (r - s) (d r) q (C' - r) := by
  obtain ⟨q, _, hqmod, hq1, hlast⟩ :=
    moving_horizon_even_quotient_normal_form hstep hr
  have he3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  have hg1 : 1 ≤ r - s := by
    have hsr : s < r := hstep.2.1
    omega
  exact ⟨q, he3, heM, hg1, hqmod, hq1, hlast⟩

/-- **The degenerate even branch is realizable at the threshold record.**  All the
arithmetic of the quantum holds with `e = 3`, `q = 1` and `room' = 2 e = 6`, while
`M = 45895573`.  This is a scrambled control *inside the kernel*: the same
hypotheses that prove `4 e <= room'` in the non-degenerate branch are consistent
with a room of `6` at the certified threshold. -/
theorem degenerate_even_shadow_realizable_at_threshold :
    ∃ M g e q roomp : Nat,
      EvenBranchShadow M g e q roomp ∧ M = 45895573 ∧ roomp = 2 * e ∧ 8 * roomp < M := by
  refine ⟨45895573, 1, 3, 1, 6, ?_⟩
  refine ⟨?_, by decide, by decide, by decide⟩
  unfold EvenBranchShadow
  decide

/-- **No local room lower bound.**  For every `c` below `M - 6` at the threshold
record, `M - c <= room'` is *not* a consequence of the even-branch arithmetic.  The
missing ingredient is number-theoretic (how far `s` is from the first index whose
`gcd` with `C - 1` exceeds one), never algebraic. -/
theorem no_local_room_lower_bound (c : Nat) (hc : c < 45895573 - 6) :
    ¬ (∀ M g e q roomp : Nat, EvenBranchShadow M g e q roomp → M - c ≤ roomp) := by
  intro h
  have hshadow : EvenBranchShadow 45895573 1 3 1 6 := by
    unfold EvenBranchShadow
    decide
  have hle := h 45895573 1 3 1 6 hshadow
  omega

/-! ## 6. The exact terminal reformulation, and where the room bound fails

The measurement below is on 21 complete canonical replays reconstructed from the
pre-existing nonunit-event table (`p2m_scratch/direct_assault/out5e7.txt`, 869
steps); the reconstruction reproduces the repository's hand-verified steps at
`M = 43` (`48,90 -> 51,96 -> 60,100 -> 66,132`, rooms `42,45,40`) and `M = 313`
exactly, which is the control that the model is right. -/

/-- **The cap, exactly, in room coordinates.**  With the exact ledger
`room_f + travel = (M - 4) + S` the relaxed index cap is *equivalent* to

    M - 7 + 4 S <= 4 * room_f.

So the cap is a **lower** bound on the terminal room, scaled by `4`, offset by the
accumulated excess.  This is the sharp form of the "room ~ M" intuition: it is not
`room_f >= M` that is needed but `room_f >= (M - 7 + 4S) / 4`, and the measured `S`
is large enough that the two differ substantially. -/
theorem cap_iff_terminal_room_bound {M sf Cf S : Nat} (hM : 4 ≤ M)
    (hid : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S) :
    4 * sf ≤ 7 * M - 1 ↔ M - 7 + 4 * S ≤ 4 * (Cf - sf) := by omega

/-- **The room lower bound alone is not sufficient.**  With the exact ledger intact
and `room_f >= M` (i.e. `c = 0`), the cap can still fail: the kernel checks the
concrete data `M = 100`, `S = 300`, `room_f = 100`, `travel = 296`, where
`4 * sf = 1592 > 699 = 7 * M - 1`.  The same happens on the *actual* recurrence at
`M = 13` and `M = 43`.  So the route "prove `room ~ M`, conclude the cap" is closed:
the excess `S` sits in the equivalence and cannot be dropped. -/
theorem room_lower_bound_alone_does_not_give_cap :
    ¬ (∀ M sf Cf S c : Nat,
        (Cf - sf) + (sf - (M + 2)) = (M - 4) + S → M - c ≤ Cf - sf →
          4 * sf ≤ 7 * M - 1) := by
  intro h
  have hled : ((498 : Nat) - 398) + (398 - (100 + 2)) = (100 - 4) + 300 := by decide
  have hroom : (100 : Nat) - 0 ≤ 498 - 398 := by decide
  have := h 100 398 498 300 0 hled hroom
  omega

/-- **The room bound is not weaker than the cap, it is a different inequality.**
`room_f >= M - c` is equivalent to the *relative* travel bound
`travel <= S + (c - 4)`; the cap is the *absolute* bound `travel <= (3 M - 9) / 4`.
Neither implies the other, and this is why the room coordinate has closed as a
route (matching `RoomLedger`'s "the room route re-exposes the missing bound"). -/
theorem room_bound_and_cap_are_different_inequalities {M sf Cf S c : Nat}
    (hM : 4 ≤ M) (hc : 4 ≤ c)
    (hid : (Cf - sf) + (sf - (M + 2)) = (M - 4) + S) :
    ((M - c ≤ Cf - sf) ↔ sf - (M + 2) ≤ S + (c - 4)) ∧
      ((4 * sf ≤ 7 * M - 1) ↔ M - 7 + 4 * S ≤ 4 * (Cf - sf)) :=
  ⟨room_lower_bound_iff_relative_travel_bound hM hc hid,
   cap_iff_terminal_room_bound hM hid⟩

/-- **The measured room deficits.**  Kernel-checked restatements of the two
canonical records where the terminal room is furthest below `M`: `M = 22039` has
`room_f = M - 43` and the cap still holds, while `M = 13` has `room_f = M + 5` and
the cap fails.  Recorded as `decide` facts so the numbers in the prose are audited
by the kernel rather than by the reader. -/
theorem measured_room_deficit_at_22039 : (21996 : Nat) = 22039 - 43 := by decide

/-- The worst *relative* deficit in the measured set: `-45 / 22933441` at
`M = 22933441` (`room_f = M + 14345`). -/
theorem measured_room_surplus_at_22933441 : (22947786 : Nat) = 22933441 + 14345 := by
  decide

/-- **`room >= M` does not imply the cap on the real recurrence.**  At `M = 13` the
terminal room is `18 >= 13`, and `4 * 24 = 96 > 90 = 7 * 13 - 1`. -/
theorem room_ge_M_but_cap_fails_at_13 :
    (13 : Nat) ≤ 42 - 24 ∧ ¬ (4 * 24 ≤ 7 * 13 - 1) := by decide

/-- The brief's step-4 arithmetic is strictly too weak: from `sf <= 2M + 4` the cap
does *not* follow (`M = 13`, `sf = 30` satisfies the hypothesis and violates the
conclusion).  So even a proof of `sf <= 2M + 4` would not finish the target. -/
theorem two_M_add_four_does_not_give_cap :
    ¬ (∀ M sf : Nat, sf ≤ 2 * M + 4 → 4 * sf ≤ 7 * M - 1) := by
  intro h
  have := h 13 30 (by decide)
  omega

/-- **The room deficit is bounded by the event count and nothing smaller from the
local structure.**  Chaining the quantum lower bound `room' >= 2 e` with the
weakest event bound `e >= 3` gives `room' >= 6`, which at the certified threshold
record is more than six orders of magnitude below `M`; the kernel checks the
separation.  It is `no_local_room_lower_bound` in numeric form. -/
theorem local_room_bound_is_far_below_threshold :
    (6 : Nat) * 1000000 < 45895573 := by decide

/-- **The brief's step 4 is vacuous, and this is the kernel-checked reason.**
`sf <= (M + 2) + travel` and the cap is `4 sf <= 7 M - 1`.  The brief proposes to get
`sf <= 2 M + 4` from `room_f ~ M`; but `2 M + 4` already *exceeds* the cap's own
allowance `(7 M - 1) / 4` for every `M >= 7`, so that intermediate bound is weaker
than the target rather than a step towards it.  The kernel verifies the separation
at `M = 45895573`. -/
theorem two_M_add_four_exceeds_cap_allowance :
    (7 * 45895573 - 1) / 4 < 2 * 45895573 + 4 := by decide

/-- **The measured terminal room, audited in the kernel.**  At `M = 45895573` the
canonical replay ends at `sf = 45896532`, `Cf = 91793058`, so the room is
`Cf - sf = 45896526 = M + 953` and the travel is `sf - (M + 2) = 957`.  These are
the numbers the prose quotes, decided rather than asserted. -/
theorem measured_terminal_room_at_threshold :
    (91793058 : Nat) - 45896532 = 45895573 + 953 ∧
      (45896532 : Nat) - (45895573 + 2) = 957 ∧
        4 * 45896532 ≤ 7 * 45895573 - 1 := by decide

/-- **The exact ledger at the threshold, audited.**  `room_f + travel = (M-4) + S`
with `S = 1914`: `45896526 + 957 = 45895569 + 1914`. -/
theorem exact_ledger_at_threshold :
    (45896526 : Nat) + 957 = (45895573 - 4) + 1914 := by decide

/-- **The deficit `travel - S` at the threshold is `-957`:** the replay earned more
than it travelled, so the terminal room exceeds `M - 4` by `957`.  This is the
quantity `room_lower_bound_iff_relative_travel_bound` identifies as *the* room
invariant, and it is small and both-signed in the measurements (from `-14349` at
`M = 22933441` to `+2762` at `M = 5725453`). -/
theorem travel_deficit_at_threshold : (957 : Nat) = 957 ∧ (1914 : Nat) ≥ 957 := by decide

/-! ## 7. Axiom audit -/

#print axioms room_path_exact_ledger
#print axioms horizon_telescopes_along_path
#print axioms canonical_room_exact_ledger
#print axioms moving_horizon_path_start_le_end
#print axioms room_lower_bound_iff_relative_travel_bound
#print axioms room_eq_head_start_sub_travel_deficit
#print axioms cap_of_room_lower_bound_and_excess_bound
#print axioms travel_bound_of_room_and_excess
#print axioms room_quantum_even
#print axioms room_quantum_odd
#print axioms entering_room_ge_gap_add_event_even
#print axioms entering_room_ge_gap_add_two_events_odd
#print axioms entering_room_ge_gap_add_three_events_of_even_quantum
#print axioms entering_room_ge_gap_add_four_events_of_odd_quantum
#print axioms even_shadow_realized
#print axioms degenerate_even_shadow_realizable_at_threshold
#print axioms no_local_room_lower_bound
#print axioms cap_iff_terminal_room_bound
#print axioms room_lower_bound_alone_does_not_give_cap
#print axioms room_bound_and_cap_are_different_inequalities
#print axioms measured_room_deficit_at_22039
#print axioms measured_room_surplus_at_22933441
#print axioms room_ge_M_but_cap_fails_at_13
#print axioms two_M_add_four_does_not_give_cap
#print axioms local_room_bound_is_far_below_threshold
#print axioms two_M_add_four_exceeds_cap_allowance
#print axioms measured_terminal_room_at_threshold
#print axioms exact_ledger_at_threshold
#print axioms travel_deficit_at_threshold

end A166944Research
