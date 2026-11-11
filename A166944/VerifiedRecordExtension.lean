import A166944.VerifiedFiftyMillionBridge

/-! # Two further certified record replays

The checked segments extend the record prefix from 91793059 to 367232911.
Each segment also bounds travel on every capped prefix before its next record.
-/

namespace A166944Research

private def hitsAfter91793059 : List Nat := [
  91793067, 91799040, 91799048, 91799050, 91799051, 91799052, 91799057, 91799058,
  91806441, 91806450, 91807190, 91807194, 91807217, 91807218, 91807220, 91807224,
  91807282, 91807284, 91807287, 91807290, 91807357, 91807377, 91807380, 91807387,
  91807392, 91807403, 91807410, 91807413, 91807416, 91807422, 91807430, 91807434,
  91807446, 91807452, 91807980, 91808140, 91808142, 91808145, 91808147, 91808148,
  91808159, 91808160, 91808167, 91808172, 91808180, 91808184, 91808200, 91808202,
  91808225, 91808234, 91808249, 91808250, 91808256
]

private def hitsAfter183616423 : List Nat := [
  183616427, 183616428, 183616443, 183616446, 183616477
]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem replayAfter91793059_accepted :
    recordReplayCheck 91793059 91793061 183586116 hitsAfter91793059 183616422 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem returnBefore183616423_accepted : recordReturnCheck 183616422 13550 = true := by
  decide +kernel

private theorem replayAfter183616423_accepted :
    recordReplayCheck 183616423 183616425 367232844 hitsAfter183616423 367232910 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem returnBefore367232911_accepted : recordReturnCheck 367232910 19163 = true := by
  decide +kernel

private theorem prefixThrough183616425 :
    d 183616425 = 183616423 ∧ IsAttainedPreviousMaximum 183616423 183616425 ∧
      RecordsVerifiedThrough 183616425 := by
  apply recordPrefixCheck_sound [(183616422, 13550, hitsAfter91793059)] (by decide : 5 < 91793059)
    fifty_million_bridge_next_record.2.2.1 verified_maximum_at_91793059 records_verified_through_91793061
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨replayAfter91793059_accepted, returnBefore183616423_accepted⟩, by decide⟩

theorem next_record_after_91793059 :
    91793059 < 183616423 ∧ IsAttainedPreviousMaximum 91793059 183616424 ∧
      d 183616425 = 183616423 ∧ D 183616424 = 183616422 :=
  canonical_replay_next_record hitsAfter91793059 (by decide) fifty_million_bridge_next_record.2.2.1
    verified_maximum_at_91793059 replayAfter91793059_accepted returnBefore183616423_accepted

theorem next_record_after_183616423 :
    183616423 < 367232911 ∧ IsAttainedPreviousMaximum 183616423 367232912 ∧
      d 367232913 = 367232911 ∧ D 367232912 = 367232910 :=
  canonical_replay_next_record hitsAfter183616423 (by decide) prefixThrough183616425.1
    prefixThrough183616425.2.1 replayAfter183616423_accepted returnBefore367232911_accepted

theorem verified_prefix_through_367232913 :
    d 367232913 = 367232911 ∧ IsAttainedPreviousMaximum 367232911 367232913 ∧
      RecordsVerifiedThrough 367232913 := by
  apply recordPrefixCheck_sound [(367232910, 19163, hitsAfter183616423)] (by decide : 5 < 183616423)
    prefixThrough183616425.1 prefixThrough183616425.2.1 prefixThrough183616425.2.2
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨replayAfter183616423_accepted, returnBefore367232911_accepted⟩, by decide⟩

theorem record_index_and_twin_prime_of_le_367232911 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 367232911) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) : n = R + 2 ∧ IsGreaterTwinPrime R := by
  have hindex : n ≤ 367232913 := by
    by_contra h
    have hlast := hprior 367232913 (by decide) (by omega)
    rw [verified_prefix_through_367232913.1] at hlast
    omega
  obtain ⟨hposition, hlo, hhi⟩ := verified_prefix_through_367232913.2.2 hR hn hindex hd hprior
  exact ⟨hposition, prime_of_no_proper_factor (by omega) hhi, prime_of_no_proper_factor (by omega) hlo⟩

/-- The two checked segments move the remaining travel hypothesis to the
last certified record. -/
theorem twin_travel_from_367232911 (htravel : TwinPrimeTravelBoundFrom 367232911) :
    TwinPrimeTravelBoundFrom 50000000 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_cases hlarge : 367232911 ≤ M
  · exact htravel hlarge htwin hcanon hpath hmax
  by_cases hfirst : M < 183616423
  · have hlo : 91793059 ≤ M := by
      by_contra h
      have hcap := fifty_million_bridge_next_record.2.1.1 (M + 2) (by omega) (by omega)
      rw [hcanon] at hcap
      omega
    have hcap := next_record_after_91793059.2.1.1 (M + 2) (by omega) (by omega)
    rw [hcanon] at hcap
    have heq : M = 91793059 := by omega
    subst M
    exact canonical_replay_travel_bound hitsAfter91793059 (by decide) hcanon
      verified_maximum_at_91793059 replayAfter91793059_accepted returnBefore183616423_accepted
      (by decide) hpath hmax
  · have hcap := next_record_after_183616423.2.1.1 (M + 2) (by omega) (by omega)
    rw [hcanon] at hcap
    have heq : M = 183616423 := by omega
    subst M
    exact canonical_replay_travel_bound hitsAfter183616423 (by decide) hcanon
      prefixThrough183616425.2.1 replayAfter183616423_accepted returnBefore367232911_accepted
      (by decide) hpath hmax

end A166944Research
