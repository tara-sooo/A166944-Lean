import A166944.VerifiedLaterRecordExtension

/-! # Certified record replays through 11751795061 -/

namespace A166944Research

private def hitsAfter1468965061 : List Nat := [
  1468965073, 1468965080, 1468965084, 1468965184
]

private def hitsAfter2937930211 : List Nat := [
  2937930216, 2937930226, 2937930233, 2937930234, 2937930239, 2937930240, 2937930247, 2937930252,
  2937940099, 2937940122, 2937940123, 2937940127, 2937940133, 2937940134, 2937940844, 2937940909,
  2937940913, 2937940914, 2937940917, 2937940920, 2937940926, 2937940932, 2937940937, 2937940938,
  2937947252, 2937947254, 2937947256, 2937947259, 2937947260, 2937947273, 2937947280, 2937947286,
  2937948850, 2937948857, 2937948858, 2937948860, 2937948864, 2937948884, 2937948887, 2937948888,
  2937948902, 2937948910, 2937948912, 2937948925, 2937948927, 2937948937, 2937948939, 2937948941,
  2937948942, 2937949018, 2937949020, 2937949023
]

private def hitsAfter5875882249 : List Nat := [
  5875882260, 5875882266, 5875882305, 5875882307, 5875882308, 5875882310, 5875882314, 5875882420,
  5875882421, 5875882422, 5875882430, 5875882434, 5875882443, 5875882447, 5875882452, 5875882457,
  5875882458, 5875927603, 5875927610, 5875927614, 5875927657, 5875927660, 5875927661, 5875927662,
  5875927667, 5875927668
]

private def boundaryRecordSegments : List (Nat × Nat × List Nat) := [
  (2937930210, 54202, hitsAfter1468965061),
  (5875882248, 76654, hitsAfter2937930211),
  (11751795060, 108405, hitsAfter5875882249)
]

set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
private theorem boundary_record_segments_accepted :
    recordPrefixCheck 1468965061 11751795061 boundaryRecordSegments = true := by
  simp only [boundaryRecordSegments, recordPrefixCheck, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem verified_prefix_through_11751795063 :
    d 11751795063 = 11751795061 ∧ IsAttainedPreviousMaximum 11751795061 11751795063 ∧
      RecordsVerifiedThrough 11751795063 := by
  obtain ⟨hcanon, hmax, hprefix⟩ := verified_prefix_through_1468965063
  exact recordPrefixCheck_sound boundaryRecordSegments (by decide) hcanon hmax hprefix
    boundary_record_segments_accepted

theorem record_index_and_twin_prime_of_le_11751795061 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 11751795061) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) : n = R + 2 ∧ IsGreaterTwinPrime R := by
  have hindex : n ≤ 11751795063 := by
    by_contra h
    have hlast := hprior 11751795063 (by decide) (by omega)
    rw [verified_prefix_through_11751795063.1] at hlast
    omega
  obtain ⟨hposition, hlo, hhi⟩ := verified_prefix_through_11751795063.2.2 hR hn hindex hd hprior
  exact ⟨hposition, prime_of_no_proper_factor (by omega) hhi, prime_of_no_proper_factor (by omega) hlo⟩

end A166944Research
