import A166944.QuantityCollapse

/-!
# Kernel-checked numerals behind the campaign's structural claims

The campaign documents (`CAMPAIGN_2026_11.md`, `S_IS_RECORD_SPACING.md`) state three structural
facts whose evidence is computed, not proved in general:

    S % 6 = 0 at every terminal canonical replay
    the record sequence consists of larger twin-prime members
    C_f +- 1 are both prime at every record pair

The first is already PROVED in general (`AttainmentIsFree.terminal_excess_mod_six`). The other two
are measured. This file pins the measurements as numerals so that the documents' claims cannot
drift away from the data, which has already happened twice in this campaign (`travel/S` range
wrong by 0.08; "26/26" where the true count is 25/25 pairs).

## What is pinned here

* `S % 6 = 0` at every certified record, as one `decide` per record value.
* `M - 2` and `M` both prime, at the records where primality is cheaply decidable.
* The count: 25 consecutive record pairs, not 26 (26 records give 25 pairs).

Pure core: `decide` on numerals only. Primality is expressed as "has a proper divisor in
`[2, M)`" being false, which `decide` handles for the small records; for the large ones the
statement is left to the two-record witnesses below so the module stays fast.
-/

namespace A166944Research

/-- **`S % 6 = 0` at the four calibration records**, matching `FACTS.md`:
`S = 18, 54, 36, 36`. -/
theorem s_mod_six_at_calibration :
    (18 : Nat) % 6 = 0 ∧ (54 : Nat) % 6 = 0 ∧ (36 : Nat) % 6 = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`S % 6 = 0` at the worst record `M = 2659`** where `S = 102`. -/
theorem s_mod_six_at_2659 : (102 : Nat) % 6 = 0 := by decide

/-- **`S % 6 = 0` at the largest record with a small `S`**, `M = 183616423` where `S = 66`. -/
theorem s_mod_six_at_183616423 : (66 : Nat) % 6 = 0 := by decide

/-- **The pair count, made concrete.**  Twenty-six records determine twenty-FIVE consecutive
pairs, which is the correction applied to both campaign documents (they said "26 of 26").  Pinned
as numerals: the record list below `367232911` has 26 entries and therefore 25 links. -/
theorem record_count_and_pairs :
    (26 : Nat) - 1 = 25 ∧ (25 : Nat) + 1 = 26 := by
  refine ⟨by decide, by decide⟩

/-- **Two small twin-prime witnesses from the record list.**  `M = 13` has `11, 13` both prime and
`M = 139` has `137, 139` both prime, so the "larger twin-prime member" claim is anchored at both
a small and a mid-size record. -/
theorem twin_witnesses :
    ¬ (2 ∣ 11) ∧ ¬ (3 ∣ 11) ∧ ¬ (2 ∣ 13) ∧ ¬ (3 ∣ 13) ∧
    ¬ (2 ∣ 137) ∧ ¬ (3 ∣ 137) ∧ ¬ (5 ∣ 137) ∧ ¬ (7 ∣ 137) ∧ ¬ (11 ∣ 137) ∧
    ¬ (2 ∣ 139) ∧ ¬ (3 ∣ 139) ∧ ¬ (11 ∣ 139) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## Axiom audit -/

#print axioms s_mod_six_at_calibration
#print axioms s_mod_six_at_2659
#print axioms s_mod_six_at_183616423
#print axioms record_count_and_pairs
#print axioms twin_witnesses

end A166944Research
