import A166944.VerifiedLaterRecordExtension

/-! # Certified record replays through 2937930211

Continues the verified chain from `1468965061`. The replay from that record has four events

    1468965073,  1468965080,  1468965084,  1468965184

and terminates at horizon `2937930210`, so the NEXT record is `2937930211`.

The hit list and the ending horizon are kernel-checked by `decide +kernel`, following exactly the
pattern of `VerifiedLaterRecordExtension`: `recordReplayCheck` verifies the replay given the hit
list, and `recordReturnCheck` verifies that no further event occurs in the final window. The
latter checks only factors up to `isqrt (C+1)`, which is why the check is feasible at this size --
a naive scan of the window would be ~1.5e9 indices.

This extends the kernel-certified record prefix from `1468965061` to `2937930211`. It is a
computational result, not a step on the frontier: the frontier itself remains open.
-/

namespace A166944Research

private def hitsAfter1468965061 : List Nat := [
  1468965073, 1468965080, 1468965084, 1468965184
]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem replayAfter1468965061_accepted :
    recordReplayCheck 1468965061 1468965063 2937930120 hitsAfter1468965061 2937930210 = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem returnBefore2937930211_accepted : recordReturnCheck 2937930210 54202 = true := by
  decide +kernel

/-- **The next record after `1468965061` is `2937930211`**, kernel-checked. -/
theorem next_record_after_1468965061 :
    1468965061 < 2937930211 ∧ IsAttainedPreviousMaximum 1468965061 2937930212 ∧
      d 2937930213 = 2937930211 ∧ D 2937930212 = 2937930210 :=
  canonical_replay_next_record hitsAfter1468965061 (by decide) verified_prefix_through_1468965063.1
    verified_prefix_through_1468965063.2.1 replayAfter1468965061_accepted
    returnBefore2937930211_accepted

end A166944Research

#print axioms A166944Research.next_record_after_1468965061
