import A166944.ResidualRebalancedPairCaps210

/-! # Finite cost and period checks for two and three demands -/

namespace A166944Research.RebalancedSmallAnchorData210

def smallAnchorCap210 (e : Nat) : Nat :=
  let coarse := if Nat.Prime e ∧ e ≤ 107 then 37 * e + 1047 else min 1166 (startupWeightAtCap210 1036 e)
  if e ∈ rebalancedPairIncrements210 then min coarse (rebalancedPairCostCap210 e) else coarse

def phaseCreditWidth210 (e : Nat) : Nat := 2 * Nat.lcm 210 (2 * e)

def smallAnchorIncrements210 : List Nat :=
  [9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 33, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59,
   61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 93, 95, 97, 99, 101, 103, 107, 115, 119]

set_option maxRecDepth 16384 in
theorem small_anchor_increment_checked210 :
    ∀ e : Fin 160, 1 < e.val → e.val % 2 = 1 → ¬ e.val ∣ 210 →
      0 < smallAnchorCap210 e.val → phaseCreditWidth210 e.val < 3 * (smallAnchorCap210 e.val + 10012) →
      e.val ∈ smallAnchorIncrements210 := by
  decide +kernel

theorem small_anchor_cap_le210 (e : Nat) : smallAnchorCap210 e ≤ 5006 := by
  let coarse := if Nat.Prime e ∧ e ≤ 107 then 37 * e + 1047 else min 1166 (startupWeightAtCap210 1036 e)
  have h : coarse ≤ 5006 := by
    dsimp only [coarse]
    split
    · rename_i hp
      have := hp.2
      omega
    · exact (min_le_left _ _).trans (by decide)
  change (if e ∈ rebalancedPairIncrements210 then min coarse (rebalancedPairCostCap210 e) else coarse) ≤ _
  split
  · exact (min_le_left _ _).trans h
  · exact h

def smallAnchorDrift210 (e f : Nat) : Nat :=
  if e = f then 2 * f - 2 else f - 1

private abbrev smallAnchorRow (e : Nat) : Nat × Nat × Nat :=
  (e, smallAnchorCap210 e, phaseCreditWidth210 e)

/-- Increment, cost cap and period width. The equality below certifies
these cached values before using them in the finite checks. -/
private def smallAnchorRows210 : List (Nat × Nat × Nat) :=
  [(9, 315, 1260), (11, 1452, 4620), (13, 1476, 5460), (17, 1650, 7140),
   (19, 1698, 7980), (23, 1665, 9660), (25, 525, 2100), (27, 525, 3780),
   (29, 1854, 12180), (31, 1926, 13020), (33, 402, 4620), (37, 2416, 15540),
   (39, 492, 5460), (41, 2564, 17220), (43, 2638, 18060), (45, 204, 1260),
   (47, 2786, 19740), (49, 402, 2940), (51, 630, 7140), (53, 3008, 22260),
   (55, 360, 4620), (57, 564, 7980), (59, 3230, 24780), (61, 3304, 25620),
   (63, 128, 1260), (65, 204, 5460), (67, 3526, 28140), (69, 432, 9660),
   (71, 3674, 29820), (73, 3748, 30660), (75, 20, 2100), (77, 264, 4620),
   (79, 3970, 33180), (81, 300, 11340), (83, 4118, 34860), (85, 352, 7140),
   (87, 234, 12180), (89, 4340, 37380), (93, 168, 13020), (95, 242, 7980),
   (97, 4636, 40740), (99, 102, 13860), (101, 4784, 42420), (103, 4858, 43260),
   (107, 5006, 44940), (115, 22, 9660), (119, 74, 7140)]

set_option maxRecDepth 16384 in
private theorem small_anchor_rows_checked210 : smallAnchorRows210 = smallAnchorIncrements210.map smallAnchorRow := by
  decide +kernel

private theorem small_anchor_row_mem210 {e : Nat} (he : e ∈ smallAnchorIncrements210) :
    smallAnchorRow e ∈ smallAnchorRows210 := by
  rw [small_anchor_rows_checked210]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

private def pairFloor210 (e f : Nat × Nat × Nat) : Nat :=
  max (e.2.2 + 2 * smallAnchorDrift210 e.1 f.1) f.2.2

private def tripleFloor210 (e f h : Nat × Nat × Nat) : Nat :=
  max (e.2.2 + 2 * smallAnchorDrift210 e.1 f.1 + 2 * smallAnchorDrift210 f.1 h.1) (pairFloor210 f h)

abbrev smallAnchorPairFloor210 (e f : Nat) : Nat := pairFloor210 (smallAnchorRow e) (smallAnchorRow f)

abbrev smallAnchorTripleFloor210 (e f h : Nat) : Nat :=
  tripleFloor210 (smallAnchorRow e) (smallAnchorRow f) (smallAnchorRow h)

private def smallAnchorPairTest210 (e f : Nat × Nat × Nat) : Prop :=
  let cost := 3 * (e.2.1 + f.2.1)
  let width := pairFloor210 e f
  width < cost → cost ≤ 10188 ∧ cost ≤ width + 4052 ∧ max e.1 f.1 ≤ 77

private def smallAnchorTripleTest210 (e f h : Nat × Nat × Nat) : Prop :=
  let cost := 3 * (e.2.1 + f.2.1 + h.2.1)
  let width := tripleFloor210 e f h
  width < cost → cost ≤ 43278 ∧ cost ≤ width + 8368 ∧ max e.1 (max f.1 h.1) ≤ 119

private instance (e f : Nat × Nat × Nat) : Decidable (smallAnchorPairTest210 e f) := by
  unfold smallAnchorPairTest210
  infer_instance

private instance (e f h : Nat × Nat × Nat) : Decidable (smallAnchorTripleTest210 e f h) := by
  unfold smallAnchorTripleTest210
  infer_instance

private def smallAnchorPairCheck210 (e : Nat × Nat × Nat) : Bool :=
  smallAnchorRows210.all fun f => decide (smallAnchorPairTest210 e f)

private def smallAnchorTripleCheck210 (e : Nat × Nat × Nat) : Bool :=
  smallAnchorRows210.all fun f => smallAnchorRows210.all fun h =>
    decide (smallAnchorTripleTest210 e f h)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem small_anchor_pair_checks210 :
    smallAnchorRows210.all smallAnchorPairCheck210 = true := by
  decide +kernel

private def smallAnchorTripleRows210 (start : Nat) : List (Nat × Nat × Nat) :=
  (smallAnchorRows210.drop start).take 8

section
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem small_anchor_triples_0 : (smallAnchorTripleRows210 0).all smallAnchorTripleCheck210 = true := by
  decide +kernel
private theorem small_anchor_triples_8 : (smallAnchorTripleRows210 8).all smallAnchorTripleCheck210 = true := by
  decide +kernel
private theorem small_anchor_triples_16 : (smallAnchorTripleRows210 16).all smallAnchorTripleCheck210 = true := by
  decide +kernel
private theorem small_anchor_triples_24 : (smallAnchorTripleRows210 24).all smallAnchorTripleCheck210 = true := by
  decide +kernel
private theorem small_anchor_triples_32 : (smallAnchorTripleRows210 32).all smallAnchorTripleCheck210 = true := by
  decide +kernel
private theorem small_anchor_triples_40 : (smallAnchorTripleRows210 40).all smallAnchorTripleCheck210 = true := by
  decide +kernel

end

private theorem small_anchor_triple_checks210 :
    smallAnchorRows210.all smallAnchorTripleCheck210 = true := by
  have hs : smallAnchorRows210 = smallAnchorTripleRows210 0 ++ smallAnchorTripleRows210 8 ++
      smallAnchorTripleRows210 16 ++ smallAnchorTripleRows210 24 ++ smallAnchorTripleRows210 32 ++
      smallAnchorTripleRows210 40 := by decide +kernel
  rw [hs]
  simp only [List.all_append, small_anchor_triples_0, small_anchor_triples_8, small_anchor_triples_16,
    small_anchor_triples_24, small_anchor_triples_32, small_anchor_triples_40, Bool.and_self]

theorem small_anchor_pair_test210 {e f : Nat}
    (he : e ∈ smallAnchorIncrements210) (hf : f ∈ smallAnchorIncrements210) :
    smallAnchorPairFloor210 e f < 3 * (smallAnchorCap210 e + smallAnchorCap210 f) →
      3 * (smallAnchorCap210 e + smallAnchorCap210 f) ≤ 10188 ∧
      3 * (smallAnchorCap210 e + smallAnchorCap210 f) ≤ smallAnchorPairFloor210 e f + 4052 ∧
      max e f ≤ 77 :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp small_anchor_pair_checks210 _ (small_anchor_row_mem210 he))
    _ (small_anchor_row_mem210 hf))

theorem small_anchor_triple_test210 {e f g : Nat}
    (he : e ∈ smallAnchorIncrements210) (hf : f ∈ smallAnchorIncrements210)
    (hg : g ∈ smallAnchorIncrements210) :
    smallAnchorTripleFloor210 e f g < 3 * (smallAnchorCap210 e + smallAnchorCap210 f + smallAnchorCap210 g) →
      3 * (smallAnchorCap210 e + smallAnchorCap210 f + smallAnchorCap210 g) ≤ 43278 ∧
      3 * (smallAnchorCap210 e + smallAnchorCap210 f + smallAnchorCap210 g) ≤ smallAnchorTripleFloor210 e f g + 8368 ∧
      max e (max f g) ≤ 119 :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp small_anchor_triple_checks210 _ (small_anchor_row_mem210 he))
    _ (small_anchor_row_mem210 hf)) _ (small_anchor_row_mem210 hg))

end A166944Research.RebalancedSmallAnchorData210
