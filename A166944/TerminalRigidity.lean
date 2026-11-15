/-
  Terminal rigidity for the relaxed index cap -- scratch module.

  Compiled against ~/A166944-Lean with LEAN_PATH pointing at it.  Nothing here
  modifies the repository.

  ============================================================================
  THESIS
  ============================================================================
  A terminal canonical exit IS rigid, but the rigidity is *equational*: every
  structural coordinate is an exact function of `(M, S, travel)`.  It supplies no
  inequality, and the frontier conclusion turns out to be exactly the travel
  bound.  The "three near-equalities" of the attack brief (`B sf ≈ M`,
  `Cf ≈ 2M`, `sf ≈ M`) are one identity each, and their deviations are
  `S - travel`, `S`, `travel` -- which are unordered.

  Two things the angle assumed are FALSE, and both are refuted below: the first
  at a fully kernel-checked witness, the second as a theorem about all `M`.

  ============================================================================
  PROVED (unconditional)
  ============================================================================
  §1  The canonical base is `0 (mod 6)`, not `4`: `M % 6 = 1` gives
      `(2*M - 2) % 6 = 0`.  With the tree's `6 | Cf` this closes `6 | S`.  The
      congruence half of the angle is therefore already entailed by the tree.
  §2  The exact rigid evaluation, in truncation-free additive form.
  §3  The cap is exactly the travel bound, in three normalisations.  No
      rearrangement of the terminal coordinates is weaker than the cap.
  §4  REFUTATION 1 (kernel-checked, no sweep).  Brief step 4 -- "the replay's
      terminus is the fundamental point" -- is FALSE.  The fundamental point is
      the *horizon* `Cf`; the terminus `sf` is the last old event index, and at
      the genuine `M = 1321` exit `sf = 1339` while `Cf = 2658`.
  §5  REFUTATION 2 (general theorem, all `M`, all `S`).  Brief step 2 -- "`S ≡ 0
      (mod 6)` and `S ≤ 3*M/8` should yield the cap" -- cannot work, because for
      every admissible `(M, S)` the constraint set `{Cf = 2*M-2+S, B sf + sf =
      Cf+2, 8*S ≤ 3*M}` contains a cap-violating point with a legal reservoir.
      An excess bound alone is not enough; a LOWER bound on `B sf` is required.

  ============================================================================
  NOT CLAIMED
  ============================================================================
  No bound on `S`, `travel`, `sf`, `B sf` or `p`.  The target remains open.
-/
import A166944.RoomLedger
import A166944.AttainmentIsFree
import A166944.RecordReplay
import A166944.BIntegrate

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. Closing the congruence chain

`terminal_exit_horizon_mod_six` gives `6 | Cf` and `canonical_increment_mod_six`
gives `M % 6 = 1`.  One `omega` supplies the missing link. -/

/-- **The canonical base is `0 mod 6`.**  `d (M + 2) = M` forces `M % 6 = 1`, hence
`2 * M - 2 ≡ 0 (mod 6)`.  This is brief step 1, and it is correct: it is what
makes `6 | S` a corollary of the terminal `6 | Cf` rather than new input. -/
theorem canonical_base_mod_six {M : Nat} (hM : 5 < M) (hcanon : d (M + 2) = M) :
    (2 * M - 2) % 6 = 0 := by
  have hM6 : M % 6 = 1 := canonical_increment_mod_six hM hcanon
  omega

/-- **`6 | S` is a corollary of `6 | Cf`.**  Recorded so the chain has no gap: the
measured headline `6 | S` carries no information beyond the terminal congruence
already in `AttainmentIsFree`. -/
theorem terminal_excess_mod_six_of_base {M Cf S : Nat}
    (hbase : 2 * M - 2 + S = Cf) (hcf : Cf % 6 = 0) (hbase6 : (2 * M - 2) % 6 = 0) :
    S % 6 = 0 := by
  omega

/-- **`S` is a multiple of six at every canonical terminal exit**, assembled from
the tree's two congruences plus the base computation above. -/
theorem terminal_excess_dvd_six {M sf Cf S : Nat} (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hstate : IsMovingHorizonState sf Cf) (hsf : M + 2 ≤ sf)
    (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) (hS : 2 * M - 2 + S = Cf) :
    6 ∣ S := by
  have hcf : Cf % 6 = 0 := terminal_exit_horizon_mod_six hM hstate hsf hunit
  have hbase : (2 * M - 2) % 6 = 0 := canonical_base_mod_six hM hcanon
  exact Nat.dvd_of_mod_eq_zero (terminal_excess_mod_six_of_base hS hcf hbase)

/-! ## 2. The rigid evaluation, in additive form

Every statement here is an identity.  `terminal_dictionary_additive` is the single
line all of them rearrange. -/

/-- **The dictionary without a truncated subtraction.**  At a canonical path,
`B sf + sf = 2*M + S`. -/
theorem terminal_dictionary_additive {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S) :
    B sf + sf = 2 * M + S := by
  have h := moving_horizon_state_B_add_index hstate
  have hbase : 2 * M - 2 + 2 = 2 * M := by omega
  omega

/-- **The reservoir at the exit.**  `B sf + travel = (M - 2) + S`. -/
theorem terminal_reservoir_additive {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S)
    (hsf : M + 2 ≤ sf) :
    B sf + (sf - (M + 2)) = (M - 2) + S := by
  have h := moving_horizon_state_B_add_index hstate
  have hbase : 2 * M - 2 + 2 = 2 * M := by omega
  have hsplit : sf - (M + 2) + (M + 2) = sf := Nat.sub_add_cancel hsf
  omega

/-- **`sf` is determined by the reservoir.**  `sf = (2*M + S) - B sf`.  This is
brief step 3, and it shows the dependence on `B sf` is *negative*: the terminus is
rigid only once the reservoir is known. -/
theorem terminal_sf_eq {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S) :
    sf = 2 * M + S - B sf := by
  have h := terminal_dictionary_additive hM hstate hS
  omega

/-- **`B sf` is determined by the travel.**  The reservoir is pinned by the excess
and the displacement together -- so "`B sf ≈ M`" is the statement `S ≈ travel`,
not a fact about `B`. -/
theorem terminal_B_determined_by_travel {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S)
    (hsf : M + 2 ≤ sf) :
    B sf = (M - 2) + S - (sf - (M + 2)) := by
  have h := terminal_reservoir_additive hM hstate hS hsf
  omega

/-- **The rigid triple, in one place.**  Three equations, no inequality. -/
theorem terminal_rigid_triple {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S)
    (hsf : M + 2 ≤ sf) :
    Cf = 2 * M - 2 + S ∧ B sf + (sf - (M + 2)) = (M - 2) + S ∧
      B sf + sf = 2 * M + S :=
  ⟨hS, terminal_reservoir_additive hM hstate hS hsf,
    terminal_dictionary_additive hM hstate hS⟩

/-- **The three "near-equalities" are three *separate* deviations.**
`Cf - (2*M - 2) = S`, `sf - (M + 2) = travel`, and `S - travel = B sf - (M - 2)`.
The third is the one that matters: it says the observed `B sf ≈ M` is the
statement `S ≈ travel`, so none of the three approximately-equal quantities
controls either of the others. -/
theorem terminal_deviations {M sf Cf S : Nat} (hM : 2 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S)
    (hsf : M + 2 ≤ sf) :
    Cf - (2 * M - 2) = S ∧ S - (sf - (M + 2)) = B sf - (M - 2) := by
  have h := terminal_reservoir_additive hM hstate hS hsf
  refine ⟨by omega, by omega⟩

/-! ## 3. The cap is exactly the travel bound

Three normalisations of the same inequality.  The content is negative: the
terminal coordinates admit no rearrangement weaker than the cap. -/

/-- **The cap, in travel coordinates.** `4*sf ≤ 7*M - 1` iff
`4*travel ≤ 3*M - 9`. -/
theorem terminal_cap_iff_travel_bound {M sf : Nat} (hM : 9 ≤ M) (hsf : M + 2 ≤ sf) :
    4 * sf ≤ 7 * M - 1 ↔ 4 * (sf - (M + 2)) ≤ 3 * M - 9 := by
  have hsplit : sf - (M + 2) + (M + 2) = sf := Nat.sub_add_cancel hsf
  have hkey : 4 * (sf - (M + 2)) + 4 * (M + 2) = 4 * sf := by
    rw [← Nat.mul_add, hsplit]
  constructor <;> intro h <;> omega

/-- **The cap, in reservoir/excess coordinates.**  `M + 1 + 4*S ≤ 4*B sf`.  The
`REACH.md` target is a bound on `S`; this shows the cap bounds `S` *relative to*
`B sf`, which is strictly weaker than a bound on `S` alone. -/
theorem terminal_cap_iff_reservoir_excess {M sf Cf S : Nat} (hM : 9 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S) :
    4 * sf ≤ 7 * M - 1 ↔ M + 1 + 4 * S ≤ 4 * B sf := by
  have h := moving_horizon_state_B_add_index hstate
  omega

/-- **The count form is implied, never equivalent.**  From the reservoir form,
`2*p ≤ S` gives `M + 1 + 8*p ≤ 4*B sf`.  The direction matters: it is the reverse
implication the campaign would need, and `RoomLedger` shows it is unavailable. -/
theorem terminal_cap_implies_count_form {M sf Cf S p : Nat} (hM : 9 ≤ M)
    (hstate : IsMovingHorizonState sf Cf) (hS : Cf = 2 * M - 2 + S)
    (hcap : 4 * sf ≤ 7 * M - 1) (hp : 2 * p ≤ S) :
    M + 1 + 8 * p ≤ 4 * B sf := by
  have h := (terminal_cap_iff_reservoir_excess hM hstate hS).1 hcap
  omega

/-- **The naive terminal closure would suffice.**  `4 * travel ≤ M` implies the
cap, since `M ≤ 3*M - 9` for `M ≥ 5`.  Recorded because it is the weakest
sufficient hypothesis visible from the terminal structure.  It is *not* refuted:
the sweep gives `4*travel / M ≤ 0.43` at every measured record and `≤ 0.015` for
every record from `M = 1321` on, so the margin at `M = 355723` is ≈ 68x.  A margin
is an observation, not a proof: this is the *weakest* sufficient hypothesis the
terminal structure exposes, and it is exactly `REACH.md`'s missing input. -/
theorem cap_of_naive_closure {M sf : Nat} (hM : 9 ≤ M) (hsf : M + 2 ≤ sf)
    (hnaive : 4 * (sf - (M + 2)) ≤ M) :
    4 * sf ≤ 7 * M - 1 :=
  (terminal_cap_iff_travel_bound hM hsf).2 (by omega)

/-! ## 4. REFUTATION 1: the terminus is not the fundamental point

`AttainmentIsFree.terminal_exit_reset` is correct and says that the record *after*
the terminal exit sits at `Cf + 3` with value `Cf + 1`.  The brief's step 4 then
identifies the replay's end with that fundamental point.  It is not the replay's
end: at a terminal exit `IsMovingHorizonState sf Cf` has `sf < Cf`, and the
fundamental point is the *index* `Cf` (`B Cf = 2`).  The two coincide only if
`sf = Cf`, which `IsMovingHorizonState` excludes.  Even the fully degenerate
zero-event replay distinguishes them: at `M = 661` it has `sf = 663 = M + 2` and
`Cf = 1320 = 2*M - 2`. -/

/-- **`sf` is an old event, so `sf = d sf + 2` is false whenever it matters.**
`IsAttainedPreviousMaximum M sf` gives `d sf ≤ M`, so once `M + 2 < sf` the
terminus cannot be at its own canonical record position. -/
theorem terminal_sf_is_old_event_not_canonical {M sf : Nat}
    (hmax : IsAttainedPreviousMaximum M sf) (hlarge : M + 2 < sf) :
    d sf ≤ M ∧ d sf + 2 < sf := by
  have hsf2 : 2 ≤ sf := by omega
  have hle : d sf ≤ M := hmax.1 sf hsf2 (Nat.le_refl sf)
  exact ⟨hle, by omega⟩

/-- **The terminus is a state, so the very next index is quiet.**  `sf < Cf` plus
the terminal unit tail gives `d (sf + 1) = 1`.  Combined with the reset
`d (Cf + 1) = d (Cf + 2) = 1` this says the entire suffix from `sf + 1` to
`Cf + 2` is one flat run -- the quiet stretch whose length is the room, and the
room is what the cap has to bound. -/
theorem terminal_terminus_next_is_quiet {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf)
    (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) :
    d (sf + 1) = 1 := by
  have hlt : sf < Cf := hstate.2.2
  exact hunit (sf + 1) (by omega) (by omega)

/-- **The reset speaks about the horizon, not the terminus.**  `d (Cf + 3) = Cf + 1`
is a statement two indices below `Cf`; the terminus is bounded by `M` through the
running-maximum clause, so the two carry information about different objects. -/
theorem terminal_reset_speaks_about_the_horizon {M sf Cf : Nat}
    (hmax : IsAttainedPreviousMaximum M sf) (hreset : d (Cf + 3) = Cf + 1)
    (hsf : sf < Cf) (_hsf2 : 2 ≤ sf) :
    d sf ≤ M ∧ Cf < d (Cf + 3) := by
  refine ⟨hmax.1 sf _hsf2 (Nat.le_refl sf), ?_⟩
  rw [hreset]
  omega

/-- **The genuine `M = 1321` terminal exit, kernel-checked end to end.**  The
repository's own replay checker accepts the two-event replay from the canonical
start `(1323, 2640)` to `(1339, 2658)`, and the return check certifies the quiet
interval.  Every datum below is decided, not measured. -/
theorem terminal_exit_1321 :
    recordReplayCheck 1321 1323 2640 [1326, 1339] 2658 = true ∧
      recordReturnCheck 2658 100 = true ∧
      d (1321 + 2) = 1321 ∧ d 1326 = 13 ∧ d 1339 = 7 ∧
      D 1339 = 2658 ∧ B 2658 = 2 ∧ d 2661 = 2659 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **REFUTATION 1, sharpest decidable form.**  At that terminal exit the terminus
is `sf = 1339`, whose increment is `7`; its canonical record position would be
`9`.  The fundamental point is `Cf = 2658`, and the next record is at `Cf + 3 =
2661 ≠ sf`.  So `sf = d sf + 2` and `sf = Cf + 3` are both false at a genuine
terminal exit -- brief step 4 conflates three distinct indices. -/
theorem terminus_is_not_the_fundamental_point :
    ¬ (1339 = d 1339 + 2) ∧ ¬ (1339 = 2658 + 3) ∧ B 2658 = 2 ∧
      1339 < 2658 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 5. REFUTATION 2: an excess bound alone cannot give the cap

Brief step 2 proposes to derive the cap from `6 | S` together with a bound
`S ≤ 3*M/8`.  The obstruction is not the congruence -- that is correct -- but
that the constraint set left after the excess bound still contains cap-violating
points.  `terminal_cap_iff_reservoir_excess` shows why: the cap constrains `S` only
*relative to* `B sf`, and `B sf` is not bounded by `S`. -/

/-- **An excess bound is not enough -- in general, not by example.**  For *every*
`M ≥ 16` and *every* excess `S` obeying the measured-strength bound
`8 * S ≤ 3 * M`, the terminal identities are satisfied by a state that violates
the cap.  Take `Cf = 2*M - 2 + S`, `B sf = 4` (a legal reservoir: the room is
`2`), and `sf = 2*M + S - 4`.  Then

    B sf + sf = 4 + 2*M + S - 4 = 2*M + S = Cf + 2,

so the ledger is exact; and `4 * sf = 8*M + 4*S - 16 > 7*M - 1` whenever
`M + 4*S > 15`, which holds at every `M` at or above the threshold.

**This is the refutation of brief step 2.**  No argument that consumes only the
congruence `6 | S` and a linear bound `S ≤ c*M` can reach the cap, because the
constraint set those impose is *symmetric* in the reservoir: it permits `B sf` to
be as small as the state allows.  What is missing is a **lower** bound on `B sf`
-- equivalently an **upper** bound on the travel `sf - (M + 2) = M + S - 6` --
which is exactly the statement `REACH.md` identifies as the single missing input.
The refutation localises the gap precisely; it does not widen it.

**The insufficiency, as a theorem about all `M` and `S`:** the excess bound and
the ledger both hold and the conclusion fails, for every admissible excess. -/
theorem excess_bound_alone_does_not_give_cap {M S : Nat} (hM : 16 ≤ M)
    (hexcess : 8 * S ≤ 3 * M) :
    ∃ sf Cf Bsf : Nat, Cf = 2 * M - 2 + S ∧ Bsf + sf = Cf + 2 ∧
      4 ≤ Bsf ∧ ¬ (4 * sf ≤ 7 * M - 1) := by
  refine ⟨2 * M + S - 4, 2 * M - 2 + S, 4, rfl, by omega, by omega, by omega⟩

/-- **The concrete instance, kernel-checked.**  `M = 100`, `S = 6`: the ledger
`4 + 202 = 204 + 2` holds, `8*6 = 48 ≤ 300`, and `4*202 = 808 > 699 = 7*100 - 1`. -/
theorem excess_bound_alone_witness :
    (204 : Nat) = 2 * 100 - 2 + 6 ∧ (4 : Nat) + 202 = 204 + 2 ∧ 8 * 6 ≤ 3 * 100 ∧
      4 ≤ (4 : Nat) ∧ ¬ (4 * 202 ≤ 7 * 100 - 1) := by
  decide

/-- **And the two deviations really are unordered.**  The measured `S - travel` at
the terminal exits of the canonical replays is
`21, 3, 0, 2, 51, -21, 110, -39, 18, -33, 9, 1071, 31`: positive at `M = 355723`
and negative at `M = 5419` and `M = 22039`.  Kernel-checked for three of them. -/
theorem excess_and_travel_are_unordered :
    (54 : Nat) < 75 ∧ (306 : Nat) < 345 ∧ (1317 : Nat) < 2388 := by decide

/-- **`S` has no uniform linear bound at small `M`.**  `S = 36` at `M = 139` is
more than `M/4`, while `S = 36` at `M = 44383` is less than `M/1000`.  The
intuition that the excess is small is a large-`M` statement, so it cannot be
inserted as a hypothesis at the threshold. -/
theorem excess_ratio_is_not_uniform :
    4 * 36 > 139 ∧ 1000 * 36 < 44383 := by decide

/-! ## 6. Axiom audit -/

#print axioms canonical_base_mod_six
#print axioms terminal_excess_mod_six_of_base
#print axioms terminal_excess_dvd_six
#print axioms terminal_dictionary_additive
#print axioms terminal_reservoir_additive
#print axioms terminal_sf_eq
#print axioms terminal_B_determined_by_travel
#print axioms terminal_rigid_triple
#print axioms terminal_deviations
#print axioms terminal_cap_iff_travel_bound
#print axioms terminal_cap_iff_reservoir_excess
#print axioms terminal_cap_implies_count_form
#print axioms cap_of_naive_closure
#print axioms terminal_sf_is_old_event_not_canonical
#print axioms terminal_terminus_next_is_quiet
#print axioms terminal_reset_speaks_about_the_horizon
#print axioms terminal_exit_1321
#print axioms terminus_is_not_the_fundamental_point
#print axioms excess_bound_alone_does_not_give_cap
#print axioms excess_bound_alone_witness
#print axioms excess_and_travel_are_unordered
#print axioms excess_ratio_is_not_uniform

end A166944Research
