import A166944.VerifiedRecordExtension

/-! # Certified record replays through 1468965061 -/

namespace A166944Research

private def hitsAfter367232911 : List Nat := [
  367233016, 367233018, 367233029, 367233042, 367233048, 367233050, 367233054, 367233057,
  367233063, 367241539, 367241544, 367241555, 367241558, 367241560, 367241561, 367241562,
  367241679, 367241680, 367241681, 367241682, 367241684, 367241687, 367241689, 367241690,
  367241693, 367241694, 367241700, 367241706, 367241714, 367241717, 367241728, 367241737,
  367241742, 367241751, 367241760, 367241766, 367241784, 367241787, 367241790, 367241798,
  367241799, 367241820, 367241826, 367243885, 367243890, 367243896, 367244054, 367244058,
  367244061, 367244067, 367244070, 367244075, 367244076, 367244077, 367244082, 367244094,
  367244097, 367244099, 367244105, 367244106, 367244124, 367244127, 367244130, 367244133,
  367244152, 367244154, 367244168, 367244172, 367244180, 367244184, 367244191, 367244197,
  367244202, 367244215, 367244220, 367244226, 367244351, 367244352, 367244353, 367244388,
  367244390, 367244394, 367244399, 367244407, 367244409, 367244410, 367244411, 367244412,
  367244417, 367244418, 367244425, 367244429, 367244430, 367244447, 367244451, 367244454,
  367246892, 367246977, 367246980, 367247010, 367247020, 367247030, 367247034, 367247043,
  367247051, 367247052, 367247077, 367247091, 367247094
]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem replayAfter367232911_accepted :
    recordReplayCheck 367232911 367232913 734465820 hitsAfter367232911 734482122 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem returnBefore734482123_accepted : recordReturnCheck 734482122 27101 = true := by
  decide +kernel

private def hitsAfter734482123 : List Nat := [
  734482127, 734482128, 734483320, 734483322, 734483332, 734483334
]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem replayAfter734482123_accepted :
    recordReplayCheck 734482123 734482125 1468964244 hitsAfter734482123 1468965060 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem returnBefore1468965061_accepted : recordReturnCheck 1468965060 38327 = true := by
  decide +kernel

private theorem verified_prefix_through_734482125 :
    d 734482125 = 734482123 ∧ IsAttainedPreviousMaximum 734482123 734482125 ∧
      RecordsVerifiedThrough 734482125 := by
  obtain ⟨hcanon, hmax, hprefix⟩ := verified_prefix_through_367232913
  apply recordPrefixCheck_sound [(734482122, 27101, hitsAfter367232911)] (by decide : 5 < 367232911)
    hcanon hmax hprefix
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨replayAfter367232911_accepted, returnBefore734482123_accepted⟩, by decide⟩

theorem next_record_after_367232911 :
    367232911 < 734482123 ∧ IsAttainedPreviousMaximum 367232911 734482124 ∧
      d 734482125 = 734482123 ∧ D 734482124 = 734482122 :=
  canonical_replay_next_record hitsAfter367232911 (by decide) verified_prefix_through_367232913.1
    verified_prefix_through_367232913.2.1 replayAfter367232911_accepted returnBefore734482123_accepted

theorem next_record_after_734482123 :
    734482123 < 1468965061 ∧ IsAttainedPreviousMaximum 734482123 1468965062 ∧
      d 1468965063 = 1468965061 ∧ D 1468965062 = 1468965060 :=
  canonical_replay_next_record hitsAfter734482123 (by decide) verified_prefix_through_734482125.1
    verified_prefix_through_734482125.2.1 replayAfter734482123_accepted returnBefore1468965061_accepted

theorem verified_prefix_through_1468965063 :
    d 1468965063 = 1468965061 ∧ IsAttainedPreviousMaximum 1468965061 1468965063 ∧
      RecordsVerifiedThrough 1468965063 := by
  obtain ⟨hcanon, hmax, hprefix⟩ := verified_prefix_through_734482125
  apply recordPrefixCheck_sound [(1468965060, 38327, hitsAfter734482123)] (by decide : 5 < 734482123)
    hcanon hmax hprefix
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨replayAfter734482123_accepted, returnBefore1468965061_accepted⟩, by decide⟩

theorem record_index_and_twin_prime_of_le_1468965061 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 1468965061) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) : n = R + 2 ∧ IsGreaterTwinPrime R := by
  have hindex : n ≤ 1468965063 := by
    by_contra h
    have hlast := hprior 1468965063 (by decide) (by omega)
    rw [verified_prefix_through_1468965063.1] at hlast
    omega
  obtain ⟨hposition, hlo, hhi⟩ := verified_prefix_through_1468965063.2.2 hR hn hindex hd hprior
  exact ⟨hposition, prime_of_no_proper_factor (by omega) hhi, prime_of_no_proper_factor (by omega) hlo⟩

theorem twin_travel_from_1468965061 (htravel : TwinPrimeTravelBoundFrom 1468965061) :
    TwinPrimeTravelBoundFrom 367232911 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_cases hlarge : 1468965061 ≤ M
  · exact htravel hlarge htwin hcanon hpath hmax
  by_cases hfirst : M < 734482123
  · have hcap := next_record_after_367232911.2.1.1 (M + 2) (by omega) (by omega)
    rw [hcanon] at hcap
    have heq : M = 367232911 := by omega
    subst M
    exact canonical_replay_travel_bound hitsAfter367232911 (by decide) hcanon
      verified_prefix_through_367232913.2.1 replayAfter367232911_accepted returnBefore734482123_accepted
      (by decide) hpath hmax
  · have hcap := next_record_after_734482123.2.1.1 (M + 2) (by omega) (by omega)
    rw [hcanon] at hcap
    have heq : M = 734482123 := by omega
    subst M
    exact canonical_replay_travel_bound hitsAfter734482123 (by decide) hcanon
      verified_prefix_through_734482125.2.1 replayAfter734482123_accepted returnBefore1468965061_accepted
      (by decide) hpath hmax

end A166944Research
