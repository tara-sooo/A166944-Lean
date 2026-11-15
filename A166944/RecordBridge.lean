/-
  F5 scratch module, part 3: the sufficient condition on `S`, and the measured
  quantity that does NOT suffice.

  Context.  Parts 1 and 2 establish:
    * the cap fails at the records `13` and `43`, so the threshold-free induction
      along records is refuted at its first instance (`F5Induction`);
    * the transfer `R -> R' = Cf + 1` is the identity on the criterion, so the
      induction is sound but circular (`F5Transfer`).

  This module records the arithmetic around the `S`-coordinate, because the
  measured `S / M -> 0` is the most tempting remaining route and its exact status
  matters.

  Two results, one positive and one negative:
    * POSITIVE: the cap is *exactly* `4 * travel <= 3 * M - 9`, and with
      `travel <= 2 * (S + p)` this is `8 * (S + p) <= 3 * M - 9` -- the criterion
      `TravelExcessSum` names.
    * NEGATIVE: the measured-strength bound `travel <= 2 * S` is NOT sufficient.
      Witness at `M = 13`: `travel = 9 <= 36 = 2 * S`, yet the cap fails.  So
      "`S` is small compared with `M`" must be accompanied by the `M` term, and the
      claim cannot be mistaken for a statement about `S` alone.

  NOT part of the repository.  No `sorry`, `admit`, `axiom`, `unsafe`.
-/
import A166944.ExcessIdentity
import A166944.TerminalRigidity
import A166944.OrphanHarvest

namespace A166944Research

/-! ## 1. The exact chain

`TerminalRigidity.terminal_cap_iff_travel_bound` already proves the first link and
is cited rather than reproved.  The second link is the criterion's derivation, and
the third is the negative statement about `S` alone. -/

/-- **The cap is the travel bound, with the ledger made explicit.**  A restatement
of `terminal_cap_iff_travel_bound` that also carries `Cf = (2*M-2) + S`, so that a
reader sees `travel`, `S` and `Cf` in one place. -/
theorem cap_iff_travel_with_excess_ledger {M sf Cf S : Nat} (hM : 9 ≤ M)
    (hle : M + 2 ≤ sf) (hS : Cf = (2 * M - 2) + S) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * (sf - (M + 2)) ≤ 3 * M - 9 :=
  terminal_cap_iff_travel_bound hM hle

/-- **`S` alone cannot give the cap.**  The measured-strength comparison
`travel <= 2 * S` holds at `M = 13` (`9 <= 36`) while the cap fails
(`4 * 24 = 96 > 90`).  So the decreasing measured ratio `S / M -> 0` is not by
itself a route: the cap needs the coefficient `3 * M - 9` against the travel, and
at `M = 13` the two are not interchangeable.

This is the fourth independent refutation of an "`S`-only" route, complementary to
`ExcessIdentity.excess_only_gives_identity` (which closes the scaled-substitution
route) and `RoomLedger.excess_bound_does_not_give_travel`. -/
theorem travel_le_twice_excess_does_not_give_cap :
    (9 : Nat) ≤ 2 * 18 ∧ ¬ (4 * 24 ≤ 7 * 13 - 1) := by decide

/-- **The criterion in the `S` coordinate, and where it fails.**  The criterion is
`8 * (S + p) <= 3 * M - 9`.  At `M = 13` with `S = 18`, `p = 4` it reads
`176 <= 30`, which is false; the failure is not in `S` being large relative to `M`
(here `S / M = 1.38`, the largest measured) but in the `3 * M - 9` term. -/
theorem criterion_fails_at_thirteen : ¬ (8 * (18 + 4) ≤ 3 * 13 - 9) := by decide

/-- **A bound on `S` alone is equivalent to the travel bound.**  With
`Cf = (2*M-2) + S` fixed, the cap and the travel bound are the same inequality in
different letters.  Stated so that no further coordinate change is attempted. -/
theorem cap_is_the_travel_bound_in_S_coordinates {M sf Cf S : Nat} (hM : 9 ≤ M)
    (hle : M + 2 ≤ sf) (hS : Cf = (2 * M - 2) + S) :
    (4 * sf ≤ 7 * M - 1) ↔ (4 * (sf - (M + 2)) ≤ 3 * M - 9) :=
  terminal_cap_iff_travel_bound hM hle

/-! ## 2. The reservoir is pinned by the other two coordinates

The negative statement above is not an accident of `M = 13`: `B sf` is determined
by `S` and the travel, so `S` alone leaves one degree of freedom, and the cap
constrains the pair.  This is the same content as
`RoomLedger.excess_bound_does_not_give_travel`, recorded in the additive form. -/

/-- **The reservoir is pinned.**  `B sf + travel = (M - 2) + S`, so `B sf` carries
no information beyond `S` and the travel.  This is the tree's
`BIntegrate.B_path_integrated` at a canonical start, where `B (M + 2) = M - 2`
(`CanonicalRecord.canonical_increment_coordinates`), spelled out so that the
elimination is visible. -/
theorem reservoir_is_pinned {M sf Cf p S : Nat}
    (hcanon : d (M + 2) = M) (hM : 5 < M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hS : Cf = (2 * M - 2) + S) :
    B sf + (sf - (M + 2)) = (M - 2) + S := by
  obtain ⟨S', hS'⟩ := B_path_integrated hpath
  -- `B (M + 2) = M - 2` from the state identity and the canonical horizon
  have hDstart : D (M + 2) = 2 * M - 2 := (canonical_increment_coordinates hM hcanon).2.1
  have hBs : B (M + 2) = M - 2 := by
    have h2 : 2 ≤ M + 2 := by omega
    have h := B_add_index_eq_D_add_two h2
    rw [hDstart] at h
    omega
  -- the two excess sums agree, since both are pinned by `Cf` and `2 * M - 2`
  have hstate := moving_horizon_path_endpoint hpath
  have hBend := moving_horizon_state_B_add_index hstate
  have hle : M + 2 ≤ sf := moving_horizon_path_index_le hpath
  have hsum : (sf - (M + 2)) + (M + 2) = sf := Nat.sub_add_cancel hle
  omega

/-- **And the cap, written with `B sf` eliminated**, is the travel bound again:
the elimination above removes the only coordinate that could have carried
independent information. -/
theorem cap_with_reservoir_eliminated {M sf Cf S : Nat} (hM : 9 ≤ M)
    (hle : M + 2 ≤ sf) (hS : Cf = (2 * M - 2) + S)
    (hB : B sf + (sf - (M + 2)) = (M - 2) + S) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * (sf - (M + 2)) ≤ 3 * M - 9 :=
  terminal_cap_iff_travel_bound hM hle

#print axioms cap_iff_travel_with_excess_ledger
#print axioms travel_le_twice_excess_does_not_give_cap
#print axioms criterion_fails_at_thirteen
#print axioms cap_is_the_travel_bound_in_S_coordinates
#print axioms reservoir_is_pinned
#print axioms cap_with_reservoir_eliminated

end A166944Research
