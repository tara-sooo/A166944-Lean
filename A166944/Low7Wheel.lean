import A166944.TravelClip210
import A166944.Low7WheelData

/-!
# Kernel-checked finite LOW7 wheel certificate

The 22,050 (time mod 210, even horizon mod 210) possibilities are
checked independently from the packed potential data.

This is a finite squarefree {3,5,7} wheel, NOT the original unrestricted
recurrence. It bounds every low-only event block (after a separate
state-equivalence argument), but DOES NOT establish an asymptotic bound
for high-prime returns or prove the twin-prime conjecture.

No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` is used.
-/

namespace A166944Research

/-- Potential: (remaining event-clock travel, remaining clipped growth). -/
def low7Budget (s C : Nat) : Nat × Nat :=
  let row := (low7BudgetRows[(C % 210) / 2]?).getD 0
  let entry := row >>> (16 * (s % 210))
  (entry % 256, (entry >>> 8) % 256)

/-- This predicate is re-evaluated from the true parity-GCD first-hit scanner,
not assumed from the generated table. -/
private def low7StateValid (s h : Nat) : Prop :=
  let C := 2 * h
  let here := low7Budget s C
  here.1 ≤ 56 ∧ here.2 ≤ 106 ∧
    match firstClippedHit210 s C with
    | none => here = (0, 0)
    | some (gap, e) =>
        here = (gap + (low7Budget (s + gap) (C + e - 1)).1,
                (e - 1) + (low7Budget (s + gap) (C + e - 1)).2)

private def low7RowChecked (h : Nat) : Bool :=
  (List.range 210).all (fun s => decide (low7StateValid s h))

private def low7BandChecked (start : Nat) : Bool :=
  (List.range' start 15).all low7RowChecked

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem low7_bands_checked :
    low7BandChecked 0 = true ∧
    low7BandChecked 15 = true ∧
    low7BandChecked 30 = true ∧
    low7BandChecked 45 = true ∧
    low7BandChecked 60 = true ∧
    low7BandChecked 75 = true ∧
    low7BandChecked 90 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem low7_all_rows_checked :
    (List.range 105).all low7RowChecked = true := by
  have hs : List.range 105 =
      List.range' 0 15 ++ List.range' 15 15 ++
      List.range' 30 15 ++ List.range' 45 15 ++
      List.range' 60 15 ++ List.range' 75 15 ++
      List.range' 90 15 := by decide
  obtain ⟨h0, h15, h30, h45, h60, h75, h90⟩ := low7_bands_checked
  unfold low7BandChecked at h0 h15 h30 h45 h60 h75 h90
  rw [hs]
  simp only [List.all_append, h0, h15, h30, h45, h60, h75, h90,
    Bool.and_self]

theorem low7_residue_verified {s h : Nat}
    (hs : s < 210) (hh : h < 105) :
    low7StateValid s h := by
  have hrow := List.all_eq_true.mp low7_all_rows_checked h
    (List.mem_range.mpr hh)
  unfold low7RowChecked at hrow
  have hcell := List.all_eq_true.mp hrow s (List.mem_range.mpr hs)
  exact of_decide_eq_true hcell

/-- Every state of the finite LOW7 residue graph has travel <= 56
and clipped growth <= 106, with exact per-edge potential telescoping.
The theorem is a conjunction of fully reduced finite checks; no
runtime Python or external C++ program participates in its proof. -/
theorem low7_finite_certificate :
    (List.range 105).all low7RowChecked = true :=
  low7_all_rows_checked

#print axioms low7_finite_certificate
#print axioms low7_residue_verified

end A166944Research
