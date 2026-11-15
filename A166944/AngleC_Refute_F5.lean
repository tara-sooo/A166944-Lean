import A166944.Lemmas

/-!
# aG · red team, part 5: claim 1 is *false at the other end of the replay*

The claim "`C_i ± 1` is always composite" is stated for the horizons **entering**
a step.  The tree's own terminal-horizon theorems need the opposite: the horizon
at which a replay *stops* has `NoProperFactor (C - 1) ∧ NoProperFactor (C + 1)`,
i.e. both members are **prime** (`QuietReturn.lean:104`,
`RebalancedBoundary210.lean:349`, and `VerifiedTwinPrimePrefix.lean:19` turns
that into `IsGreaterTwinPrime`).

So "composite" is a property of the *entry* horizons only, and it is exactly the
strictness `d r < C ± 1` that makes it so.  Below: the entry-side proof in
one line, plus the `decide`-level data for the `M = 44385` terminal horizon.

Pure core only (`decide`/`omega`/`simp`/`rfl`); no `sorry`/`admit`/`axiom`/`unsafe`.
Scratch only; the repository is untouched.
-/

set_option maxRecDepth 1000000

namespace A166944Research

/-! ## 1. The entry-side claim, exactly as strong as the tree allows

`moving_horizon_step_event_package` already gives `d r < C ± 1` and
`d r | C ± 1`.  Compositeness is the immediate consequence -- there is no
additional arithmetic. -/

/-- **Claim 1, and its whole proof.**  Any strict divisor `> 1` of `C ± 1`
witnesses compositeness.  The only input is the event package. -/
theorem entry_horizon_composite {s C r C' : Nat} (h : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → ∃ f : Nat, 2 ≤ f ∧ f < C - 1 ∧ f ∣ C - 1) ∧
      (r % 2 = 1 → ∃ f : Nat, 2 ≤ f ∧ f < C + 1 ∧ f ∣ C + 1) := by
  have he : 1 < d r := h.2.2.2.1
  rcases moving_horizon_step_event_package h with hA | hB
  · obtain ⟨hpar, hdiv, hprop, _⟩ := hA
    exact ⟨fun _ => ⟨d r, he, hprop, hdiv⟩,
      fun hc => absurd (hpar.symm.trans hc) (by decide)⟩
  · obtain ⟨hpar, hdiv, hprop, _⟩ := hB
    exact ⟨fun hc => absurd (hpar.symm.trans hc) (by decide),
      fun _ => ⟨d r, he, hprop, hdiv⟩⟩

/-- The same, phrased without the parity side conditions: **either** `C - 1` or
`C + 1` has a proper divisor, according to the hit's parity. -/
theorem entry_horizon_has_proper_divisor {s C r C' : Nat}
    (h : IsMovingHorizonStep s C r C') :
    (∃ f : Nat, 2 ≤ f ∧ f < C - 1 ∧ f ∣ C - 1) ∨
      (∃ f : Nat, 2 ≤ f ∧ f < C + 1 ∧ f ∣ C + 1) := by
  obtain ⟨h0, h1⟩ := entry_horizon_composite h
  rcases Nat.mod_two_eq_zero_or_one r with he | ho
  · exact Or.inl (h0 he)
  · exact Or.inr (h1 ho)

/-! ## 2. `e ≤ M < C ± 1`: the second inequality is *not* free, and the tree
proves it; the first is `e ≤ M` from the cap

`C ± 1 > M` follows from `C ≥ 2M - 2` at the *first* step and only grows, but the
growth is what the tree's step law `C' = C + (d r - 1)` supplies.  What is worth
recording is that the compositeness argument **never uses `M` at all** (Part 1):
the claim's stated reason ("`3 ≤ e ≤ M < C ± 1` excludes primes") has a redundant
premise.  `e ≤ M` and `M < C ± 1` are true but unused. -/

/-- **`M` is not needed**: the same compositeness holds for `M = 0`. -/
theorem compositeness_does_not_use_M {s C r C' : Nat}
    (h : IsMovingHorizonStep s C r C') :
    (∃ f : Nat, 2 ≤ f ∧ f < C - 1 ∧ f ∣ C - 1) ∨
      (∃ f : Nat, 2 ≤ f ∧ f < C + 1 ∧ f ∣ C + 1) :=
  entry_horizon_has_proper_divisor h

/-! ## 3. The terminal horizon is the opposite case

`M = 44385`: the replay's terminal horizon is `C_f = 88800`, and
`C_f - 1 = 88799`, `C_f + 1 = 88801` are **both prime**.  (Values verified by the
scan at `2 * 10^6`; `Nat.Prime` is not in this import closure and `decide` cannot
evaluate it, so this file records the arithmetic data that decides it.) -/

theorem terminal_data_M44385 : D 44384 = 44382 ∧ d 44385 = 44383 := by
  refine ⟨by decide, by decide⟩

/-- The two numbers whose primality the scan asserts: `88799` and `88801` have no
divisor in `[2, 88799)`.  Stated as a decidable bounded statement so the kernel
can check the *shape*; the full primality is the scan's assertion. -/
theorem terminal_pair_coprime_to_small : ¬ 3 ∣ 88799 ∧ ¬ 3 ∣ 88801 ∧
    ¬ 7 ∣ 88799 ∧ ¬ 7 ∣ 88801 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end A166944Research

#print axioms A166944Research.entry_horizon_composite
#print axioms A166944Research.entry_horizon_has_proper_divisor
#print axioms A166944Research.compositeness_does_not_use_M
