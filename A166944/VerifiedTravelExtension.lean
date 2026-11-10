import A166944.VerifiedRecordPrefix

/-!
# Travel in the first interval after the verified prefix

The accepted replay proves the next strict record and bounds all
capped prefixes in the same interval. The generator only supplies
indices and the terminal root bound.
-/

namespace A166944Research

private def extensionHits : List Nat := [
    22933560, 22933591, 22933597, 22933602, 22933605, 22933623, 22933631, 22933632,
    22933647, 22933653, 22933664, 22933668, 22933698, 22933700, 22933704, 22938265,
    22938268, 22938269, 22938270, 22938363, 22938365, 22938367, 22938372, 22938579,
    22938580, 22938581, 22938582, 22938586, 22938587, 22938593, 22938594, 22939304,
    22939308, 22939309, 22939314, 22939317, 22939320, 22939326, 22939329, 22939336,
    22939340, 22939344, 22940147, 22940148, 22940150, 22940154, 22940160, 22940166,
    22940179, 22940182, 22940183, 22940184, 22940187, 22940190, 22940203, 22940204,
    22940207, 22940208, 22940213, 22940220, 22940226, 22940227, 22940232, 22940246,
    22940250, 22940256, 22940258, 22940262, 22940267, 22940268, 22940295, 22940298,
    22940309, 22941260, 22941264, 22941567, 22941678, 22941680, 22941684, 22941697,
    22941707, 22941708, 22941736, 22941738, 22941740, 22941744, 22941758, 22941776,
    22941778, 22941789, 22941792, 22941847, 22941852, 22941855, 22941856, 22941858,
    22942900, 22942901, 22942910, 22942914, 22942960, 22942962, 22942971, 22942977,
    22942980, 22943093, 22943097, 22943100, 22943102, 22943109, 22943110, 22943111,
    22943112, 22943117, 22943118, 22943140, 22943142, 22943144, 22943147, 22943149,
    22943154, 22943157, 22943160, 22943295, 22943298, 22943615, 22943616, 22943620,
    22943622, 22943627, 22943628, 22943630, 22943634, 22943640, 22943659, 22943662,
    22943664, 22943690, 22943694, 22943914, 22943916, 22943939, 22943951, 22944107,
    22944108, 22945432, 22945463, 22945464, 22945470, 22945476, 22945494, 22945496,
    22945512, 22945518, 22945538, 22945542, 22945770, 22945777, 22945785, 22945787,
    22945788, 22945793, 22945794, 22945803, 22945806, 22945813, 22945820, 22945824,
    22945852, 22945854, 22945859, 22945860, 22945980, 22945986, 22946049, 22946056,
    22946058, 22946067, 22946070, 22946077, 22946082, 22946172, 22946177, 22946178,
    22946187, 22946190, 22946191, 22946200, 22946202, 22946211, 22946217, 22946219,
    22946220, 22946245, 22947464, 22947468, 22947587, 22947588, 22947590, 22947594,
    22947626, 22947630, 22947633, 22947678, 22947680, 22947684, 22947775, 22947782,
    22947786
  ]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem extensionReplay_accepted :
    recordReplayCheck 22933441 (22933441 + 2) (2 * 22933441 - 2) extensionHits 45895572 = true := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem extensionReturn_accepted : recordReturnCheck 45895572 6774 = true := by decide

private theorem extension_next_record :
    22933441 < 45895573 ∧ IsAttainedPreviousMaximum 22933441 45895574 ∧
      d 45895575 = 45895573 ∧ D 45895574 = 45895572 :=
  canonical_replay_next_record extensionHits (by decide) last_verified_record_value
    last_verified_prefix_maximum extensionReplay_accepted extensionReturn_accepted

theorem canonical_travel_bound_at_22933441 {sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (22933441 + 2) (2 * 22933441 - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum 22933441 sf) :
    2 * (sf - (22933441 + 2)) ≤ 22933441 :=
  canonical_replay_travel_bound extensionHits (by decide) last_verified_record_value
    last_verified_prefix_maximum extensionReplay_accepted extensionReturn_accepted (by decide) hpath hmax

/-- There is no intervening canonical record value, and all capped
prefixes at the lower endpoint satisfy the travel bound. -/
theorem canonical_travel_bound_on_verified_extension {M sf Cf p : Nat}
    (hM : 22933441 ≤ M) (hupper : M < 45895573) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) :
    2 * (sf - (M + 2)) ≤ M := by
  have hcap := extension_next_record.2.1.1 (M + 2) (by omega) (by omega)
  have hEq : M = 22933441 := by omega
  subst M
  exact canonical_travel_bound_at_22933441 hpath hmax

private theorem extension_prefix_accepted :
    recordPrefixCheck 22933441 45895573 [(45895572, 6774, extensionHits)] = true := by
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨extensionReplay_accepted, extensionReturn_accepted⟩, by decide⟩

theorem records_verified_through_45895575 : RecordsVerifiedThrough 45895575 :=
  (recordPrefixCheck_sound [(45895572, 6774, extensionHits)] (by decide : 5 < 22933441)
    last_verified_record_value last_verified_prefix_maximum records_verified_through_22933443
    extension_prefix_accepted).2.2

theorem record_index_and_factors_of_le_45895573 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 45895573) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) :
    n = R + 2 ∧ NoProperFactor (R - 2) ∧ NoProperFactor R := by
  have hindex : n ≤ 45895575 := by
    by_cases h : n ≤ 45895575
    · exact h
    · have hlast := hprior 45895575 (by decide) (by omega)
      rw [extension_next_record.2.2.1] at hlast
      omega
  exact records_verified_through_45895575 hR hn hindex hd hprior

end A166944Research
