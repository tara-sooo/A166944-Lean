/-
  Report module for the "record-structure" attack on the relaxed index cap.

  NOT part of the repository; lives in scratch and is compiled against
  ~/A166944-Lean with LEAN_PATH pointing at it.

  Contents
  --------
  A. The attainment clause of `IsAttainedPreviousMaximum` is entailed by the
     canonical hypothesis plus the path, so it carries no information about `sf`.
  B. Therefore `IsAttainedPreviousMaximum M sf` is *equivalent* to its first
     component at a canonical start.
  C. Consequently the frontier's two formulations (attained form / capped form)
     are logically equivalent as universally quantified statements.  This closes
     the "use the second component actively" angle rather than advancing it.
  D. Structural consequences at a terminal exit: `B Cf = 2`, `6 | Cf`, and the
     next record sits at `Cf + 3`.
-/
import A166944.RelaxedCap
import A166944.CanonicalRecord
import A166944.BCoordinates
import A166944.RecordBarrier

namespace A166944Research

/-! ## A. The attainment clause is free -/

/-- **The second component of `IsAttainedPreviousMaximum` needs no hypothesis
beyond the canonical start.**  The witness is the canonical index `M + 2` itself:
`d (M + 2) = M` by hypothesis, and `M + 2 ≤ sf` is the tree's unconditional
lower bound `moving_horizon_path_index_le`.

This is the precise reason the "second component" cannot be used to bound `sf`
from above: it holds at *every* index at or beyond `M + 2`, independently of
anything else in the hypotheses. -/
theorem attainment_clause_holds_at_every_index {M : Nat} (hcanon : d (M + 2) = M)
    (sf : Nat) (hsf : M + 2 ≤ sf) : ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = M :=
  ⟨M + 2, by omega, hsf, hcanon⟩

/-- Specialisation of the previous statement to the shape the target uses. -/
theorem attainment_clause_is_free {M sf : Nat} (hcanon : d (M + 2) = M)
    (hsf : M + 2 ≤ sf) : ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = M :=
  attainment_clause_holds_at_every_index hcanon sf hsf

/-- **The first component alone already gives the whole predicate**, once the
canonical hypothesis and the index lower bound are available. -/
theorem attained_previous_maximum_of_upper_bound {M sf : Nat}
    (hcanon : d (M + 2) = M) (hsf : M + 2 ≤ sf)
    (hup : ∀ j : Nat, 2 ≤ j → j ≤ sf → d j ≤ M) :
    IsAttainedPreviousMaximum M sf :=
  ⟨hup, attainment_clause_is_free hcanon hsf⟩

/-! ## B. The equivalence at a canonical start -/

/-- **`IsAttainedPreviousMaximum M sf` is exactly its upper-bound component** at a
canonical start.  The forward direction is projection; the backward direction is
`attained_previous_maximum_of_upper_bound`.  Nothing is lost by discarding the
existential clause from the hypothesis set. -/
theorem attained_previous_maximum_iff_upper_bound {M sf : Nat}
    (hcanon : d (M + 2) = M) (hsf : M + 2 ≤ sf) :
    IsAttainedPreviousMaximum M sf ↔
      ∀ j : Nat, 2 ≤ j → j ≤ sf → d j ≤ M := by
  constructor
  · intro h
    exact h.1
  · intro hup
    exact attained_previous_maximum_of_upper_bound hcanon hsf hup

/-- **Refutation of the "second component" angle, in the form a refutation takes.**
There is no index predicate `Q` such that the attainment clause plus `Q` bounds
`sf` from above unless `Q` alone does: the clause holds at every `sf ≥ M + 2`.
Stated as the satisfiability of the clause at an *arbitrary* large index. -/
theorem attainment_clause_gives_no_index_bound {M : Nat} (hcanon : d (M + 2) = M)
    (N : Nat) :
    ∃ sf : Nat, N ≤ sf ∧ ∃ r : Nat, 2 ≤ r ∧ r ≤ sf ∧ d r = M :=
  ⟨max N (M + 2), Nat.le_max_left _ _,
    attainment_clause_holds_at_every_index hcanon (max N (M + 2)) (Nat.le_max_right _ _)⟩

/-! ## C. The two formulations of the frontier are equivalent -/

/-- **The frontier, in the capped form.**  Same statement as
`a166944_relaxed_index_cap` with `IsAttainedPreviousMaximum M sf` replaced by its
first component.  No `IsGreaterTwinPrime` is used by either side, so the
equivalence below is stated without it. -/
def RelaxedIndexCapCappedForm : Prop :=
  ∀ {M sf Cf p : Nat}, 45895573 ≤ M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    (∀ j : Nat, 2 ≤ j → j ≤ sf → d j ≤ M) → 4 * sf ≤ 7 * M - 1

/-- **The frontier, in the attained form** (the target's hypothesis set, minus the
`IsGreaterTwinPrime` conjunct, which the conclusion does not consume). -/
def RelaxedIndexCapAttainedForm : Prop :=
  ∀ {M sf Cf p : Nat}, 45895573 ≤ M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1

/-- **The two forms are logically equivalent.**  So the target's attained-maximum
hypothesis may be replaced by the running-maximum bound with no loss, and every
route that consumes the attained form is a route that consumes only the bound.
This is the sharpest available statement of "the second component is not an
independent input". -/
theorem relaxed_index_cap_attained_iff_capped :
    RelaxedIndexCapAttainedForm ↔ RelaxedIndexCapCappedForm := by
  constructor
  · intro h M sf Cf p hM hcanon hpath hup
    exact h hM hcanon hpath
      (attained_previous_maximum_of_upper_bound hcanon
        (moving_horizon_path_index_le hpath) hup)
  · intro h M sf Cf p hM hcanon hpath hmax
    exact h hM hcanon hpath hmax.1

/-- The direction that matters for "can the second component be used": any proof
of the capped form transports to the attained form for free. -/
theorem relaxed_index_cap_of_capped_form (h : RelaxedIndexCapCappedForm) :
    RelaxedIndexCapAttainedForm :=
  relaxed_index_cap_attained_iff_capped.2 h

/-- And conversely, so the two are interchangeable and neither is weaker. -/
theorem capped_form_of_relaxed_index_cap (h : RelaxedIndexCapAttainedForm) :
    RelaxedIndexCapCappedForm :=
  relaxed_index_cap_attained_iff_capped.1 h

/-! ## D. Terminal exits are fundamental -/

/-- **A terminal exit is a fundamental point.**  If no index strictly after `sf`
and at most `Cf` carries a nontrivial increment, the unit-tail ledger
`B m + (m - s) = B s` (`BCoordinates`) cancels the room `Cf - sf` against the
dictionary `B sf + sf = Cf + 2`, leaving `B Cf = 2`.

This is what makes the *endpoint* coordinate rigid on a terminal path, and it is
the reason a terminal replay cannot stop at an arbitrary horizon. -/
theorem terminal_exit_B_eq_two {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf)
    (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) : B Cf = 2 := by
  have hle : sf ≤ Cf := Nat.le_of_lt hstate.2.2
  have htail := B_add_index_sub_eq_of_unit_tail hstate.1 hle hunit
  have hdict := moving_horizon_state_B_add_index hstate
  have hroom : Cf - sf + sf = Cf := Nat.sub_add_cancel hle
  omega

/-- **The terminal horizon is a multiple of six.**  Immediate from
`terminal_exit_B_eq_two` and `fundamental_point_mod_six`; the lower bound `6 ≤ Cf`
comes from the canonical start, so no extra hypothesis on the size of the replay
is needed. -/
theorem terminal_exit_horizon_mod_six {M sf Cf : Nat} (hM : 5 < M)
    (hstate : IsMovingHorizonState sf Cf) (hsf : M + 2 ≤ sf)
    (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) : Cf % 6 = 0 := by
  have hCf6 : 6 ≤ Cf := by
    have hlt := hstate.2.2
    omega
  exact fundamental_point_mod_six hCf6 (terminal_exit_B_eq_two hstate hunit)

/-- **Beyond a terminal exit the recurrence resets at `Cf + 3`.**  The next record
after the fundamental point `Cf` has value `Cf + 1` and index `Cf + 3`, so the
terminal horizon of a canonical replay is exactly one less than the value of the
following record.  This is what the measurements show (`j1 = Cf + 3`,
`d j1 = Cf + 1` at every canonical start), and it is a consequence of
`fundamental_reset_at_three`, not a new hypothesis. -/
theorem terminal_exit_reset {M sf Cf : Nat} (hM : 5 < M)
    (hstate : IsMovingHorizonState sf Cf) (hsf : M + 2 ≤ sf)
    (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) :
    d (Cf + 1) = 1 ∧ d (Cf + 2) = 1 ∧ d (Cf + 3) = Cf + 1 := by
  have hCf6 : 6 ≤ Cf := by
    have hlt := hstate.2.2
    omega
  exact fundamental_reset_at_three hCf6 (terminal_exit_B_eq_two hstate hunit)

/-- **The excess sum of a terminal canonical replay is a multiple of six.**  With
the terminal exit fundamental, `S = Cf - (2 * M - 2)` inherits `6 | Cf` and the
canonical congruence `M % 6 = 1`. -/
theorem terminal_excess_mod_six {M sf Cf S : Nat} (hM : 5 < M)
    (hcanon : d (M + 2) = M) (hstate : IsMovingHorizonState sf Cf)
    (hsf : M + 2 ≤ sf) (hunit : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1)
    (hS : S + (2 * M - 2) = Cf) : S % 6 = 0 := by
  have hCf6 := terminal_exit_horizon_mod_six hM hstate hsf hunit
  have hM6 : M % 6 = 1 := canonical_increment_mod_six hM hcanon
  omega

/-! ## E. Monotonicity: prefixes are easier, so terminal paths are the hard case -/

/-- **The cap is monotone downward along a step.**  A step strictly increases the
index (`IsMovingHorizonStep` carries `s < r`), so if the cap holds at a successor
state it holds at the state itself.

Consequence: the target quantifies over *all* paths, but a shorter path is never
harder than a longer one.  It is therefore enough to bound the terminal
(maximal) replay, which is the only case where `D` has caught up with its own
index. -/
theorem relaxed_cap_of_successor {M s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcap : 4 * r ≤ 7 * M - 1) : 4 * s ≤ 7 * M - 1 := by
  have hsr := hstep.2.1
  omega

/-- The same monotonicity stated on paths: if a path extends the endpoint of
another, the cap transfers backwards. -/
theorem relaxed_cap_of_path_extension {M sf Cf r C' : Nat}
    (hstep : IsMovingHorizonStep sf Cf r C') (hcap : 4 * r ≤ 7 * M - 1) :
    4 * sf ≤ 7 * M - 1 :=
  relaxed_cap_of_successor hstep hcap

/-- **Terminal form of the frontier.**  By the monotonicity above, if the cap can
be proved for paths that cannot be extended any further, it holds for every path.
The hypothesis below is therefore *weaker* than the target's, in the sense that it
constrains fewer `(sf, Cf, p)` triples. -/
def RelaxedIndexCapTerminalForm : Prop :=
  ∀ {M sf Cf p : Nat}, 45895573 ≤ M → d (M + 2) = M →
    HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
    (∀ j : Nat, 2 ≤ j → j ≤ sf → d j ≤ M) →
    (∀ j : Nat, sf < j → j ≤ Cf → d j = 1) → 4 * sf ≤ 7 * M - 1

/-- The terminal form is implied by the capped form (add a hypothesis to the
antecedent), so a proof of the terminal form is not automatically a proof of the
cap.  The reduction in the other direction needs the extension argument; it is
recorded here as a target rather than asserted. -/
theorem terminal_form_of_capped_form (h : RelaxedIndexCapCappedForm) :
    RelaxedIndexCapTerminalForm := by
  intro M sf Cf p hM hcanon hpath hup _
  exact h hM hcanon hpath hup

/-! ## F. Axiom audit (must print only `propext` / `Quot.sound`, or nothing) -/

#print axioms attainment_clause_holds_at_every_index
#print axioms attainment_clause_is_free
#print axioms attained_previous_maximum_of_upper_bound
#print axioms attained_previous_maximum_iff_upper_bound
#print axioms attainment_clause_gives_no_index_bound
#print axioms relaxed_index_cap_attained_iff_capped
#print axioms relaxed_index_cap_of_capped_form
#print axioms capped_form_of_relaxed_index_cap
#print axioms terminal_exit_B_eq_two
#print axioms terminal_exit_horizon_mod_six
#print axioms terminal_exit_reset
#print axioms terminal_excess_mod_six
#print axioms relaxed_cap_of_successor
#print axioms relaxed_cap_of_path_extension
#print axioms terminal_form_of_capped_form

end A166944Research
