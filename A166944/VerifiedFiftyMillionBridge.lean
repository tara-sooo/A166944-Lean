import A166944.TravelTarget

/-!
# Certified travel below fifty million

The37-event replay after record45895573 reaches the next record91793059.
It closes every capped canonical start in[45895573,50000000), without
assuming the open reserve inequality used above fifty million.
-/

namespace A166944Research

private def fiftyMillionHits : List Nat := [
  45895577, 45895578, 45895684, 45895699, 45895846, 45895880, 45895884, 45895887,
  45895890, 45895920, 45895926, 45895929, 45895932, 45895940, 45895944, 45895948,
  45895950, 45895960, 45895962, 45895969, 45895971, 45895973, 45895974, 45896064,
  45896070, 45896073, 45896411, 45896430, 45896433, 45896440, 45896442, 45896510,
  45896514, 45896516, 45896520, 45896531, 45896532
]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem fiftyReplay_accepted :
    recordReplayCheck 45895573 45895575 91791144 fiftyMillionHits 91793058 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem fiftyReturn_accepted : recordReturnCheck 91793058 9580 = true := by
  decide +kernel

theorem fifty_million_bridge_next_record :
    45895573 < 91793059 ∧ IsAttainedPreviousMaximum 45895573 91793060 ∧
      d 91793061 = 91793059 ∧ D 91793060 = 91793058 :=
  canonical_replay_next_record fiftyMillionHits (by decide) verified_record_at_45895573
    verified_maximum_at_45895573 fiftyReplay_accepted fiftyReturn_accepted

theorem canonical_travel_bound_at_45895573 {sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo 45895575 91791144 sf Cf p)
    (hmax : IsAttainedPreviousMaximum 45895573 sf) : 2 * (sf - 45895575) ≤ 45895573 :=
  canonical_replay_travel_bound fiftyMillionHits (by decide) verified_record_at_45895573
    verified_maximum_at_45895573 fiftyReplay_accepted fiftyReturn_accepted (by decide) hpath hmax

theorem canonical_travel_bound_below_fifty_million {M sf Cf p : Nat}
    (hM : 45895573 ≤ M) (hupper : M < 50000000) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) : 2 * (sf - (M + 2)) ≤ M := by
  have hcap := fifty_million_bridge_next_record.2.1.1 (M + 2) (by omega) (by omega)
  have heq : M = 45895573 := by omega
  subst M
  exact canonical_travel_bound_at_45895573 hpath hmax

private theorem fiftyPrefix_accepted :
    recordPrefixCheck 45895573 91793059 [(91793058, 9580, fiftyMillionHits)] = true := by
  simp only [recordPrefixCheck, Bool.and_eq_true]
  exact ⟨⟨fiftyReplay_accepted, fiftyReturn_accepted⟩, by decide⟩

theorem records_verified_through_91793061 : RecordsVerifiedThrough 91793061 :=
  (recordPrefixCheck_sound [(91793058, 9580, fiftyMillionHits)] (by decide : 5 < 45895573)
    verified_record_at_45895573 verified_maximum_at_45895573 records_verified_through_45895575
    fiftyPrefix_accepted).2.2

theorem record_index_and_factors_of_le_91793059 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 91793059) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) :
    n = R + 2 ∧ NoProperFactor (R - 2) ∧ NoProperFactor R := by
  have hindex : n ≤ 91793061 := by
    by_cases h : n ≤ 91793061
    · exact h
    · have hlast := hprior 91793061 (by decide) (by omega)
      rw [fifty_million_bridge_next_record.2.2.1] at hlast
      omega
  exact records_verified_through_91793061 hR hn hindex hd hprior

theorem target_for_records_le_91793059 {R : Nat}
    (hR : 5 < R) (hbound : R ≤ 91793059) (hrecord : IsDifferenceRecord R) :
    IsGreaterTwinPrime R := by
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  obtain ⟨_, hlo, hhi⟩ := record_index_and_factors_of_le_91793059 hR hbound hn hd hprior
  exact ⟨prime_of_no_proper_factor (by omega) hhi, prime_of_no_proper_factor (by omega) hlo⟩

theorem twin_travel_from_fifty_million (htravel : TwinPrimeTravelBoundFrom 50000000) :
    TwinPrimeTravelBoundFrom 45895573 := by
  intro M sf Cf p hM htwin hcanon hpath hmax
  by_cases h : M < 50000000
  · exact canonical_travel_bound_below_fifty_million hM h hcanon hpath hmax
  · exact htravel (by omega) htwin hcanon hpath hmax

theorem target_of_twin_travel_from_fifty_million (htravel : TwinPrimeTravelBoundFrom 50000000) :
    Target := by
  intro R hR hrecord
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  exact (record_index_and_twin_prime_of_twin_travel_bound_from_45895573
    (twin_travel_from_fifty_million htravel) hR hn hd hprior).2

end A166944Research
