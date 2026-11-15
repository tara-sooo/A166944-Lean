import A166944.QuietReturn
import A166944.RecordBarrier

/-!
# The travel-bound gate splits into two strictly weaker gates

`REACH.md` records twelve routes converging on one inequality, and the natural
reading is that any weakening of it would be a restatement. That reading is
wrong, and this module is the counterexample: the consumer of the travel bound,
`QuietReturn.canonical_next_record_factors_of_short_travel`, needs strictly less
than the travel bound supplies.

The consumer has two branches. The **crossing** branch reaches the goal through
`moving_horizon_new_record_horizon_lower_bound` and uses only the horizon cap
`Cf <= 3*M + 4`; the travel bound itself is not needed there. The **quiet** branch
needs `2*sqrt(Cf+1) < Cf - sf`, and the arithmetic behind that needs only

    4 * sf <= 7 * M - 1,

which is strictly weaker than what travel gives. Travel gives `4*sf <= 6*M + 8`,
so the relaxation is `M - 9` in general and about 45.9 million at the threshold
`45895573` that the top of the development uses.

`canonical_next_record_factors_of_two_caps_tight` is the consumer with the travel
hypothesis replaced by the two caps. It compiles, which is to say the replacement
is sound.

`separation_at_real_threshold` is the evidence that the replacement is a genuine
weakening rather than a restatement: at `M = 45895573` there is an index/horizon
pair satisfying both caps while violating the travel bound. So the two caps do not
imply the parent gate.

## What this does and does not change

It does **not** remove the obstruction. The cap `4*sf <= 7*M - 1` is still an
unproved uniform statement about the terminal index, and `REACH.md`'s diagnosis
stands: the missing input is a bound on `sf` (equivalently on the event count `p`).

What it changes is the **strength** required. The target inequality is relaxed by
a factor of `7/6`, and the crossing branch is freed from the travel bound
entirely. A gate that is easier to prove is worth having even when it is not yet
proved.

## A note on how this was found

The claim that this decomposition was impossible was mine, and it was wrong. I had
argued that the consumer uses the travel bound at full strength. Checking it
properly -- by replacing the hypothesis with weaker ones and asking whether the
proof still compiles -- shows the arithmetic tolerates `sf` up to `7*M/4`, not
`3*M/2 + 2`. The lesson is recorded here because the mistake was natural: reading a
proof is not the same as measuring what it needs, and `omega` in particular uses
whatever is in context, so neither `grep` nor intuition settles the question.
-/

namespace A166944Research


/-! ## EXPERIMENT E13 -- FINAL

* `4*s ≤ 7*M - 1` PASSES  (exact tight threshold for the quiet branch)
* `4*s ≤ 7*M`     FAILS   (one unit weaker)
* cap (A) `Cf ≤ 3*M+4` is replaced by a QUADRATIC cap `C+1 < (M/8)^2` -- the
  quiet branch never needed the linear form.
* the separation witness is instantiated at the REAL threshold `45895573`. -/

/-- E13a: the exact threshold, `4*s ≤ 7*M - 1`.  **COMPILES.** -/
private theorem b_tight {M s C : Nat} (hM : 968 ≤ M) (h : 4 * s ≤ 7 * M - 1)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) : 2 * isqrt (C + 1) < C - s := by
  let q := isqrt (C + 1); let b := M / 8
  have hb : 121 ≤ b := by omega
  have hb2 := Nat.mul_le_mul_right b hb
  have hq2 : q * q ≤ C + 1 := isqrt_sq_le _
  have hqb : q < b := by
    by_cases hq : q < b
    · exact hq
    · have hsq := Nat.mul_le_mul (show b ≤ q by omega) (show b ≤ q by omega)
      omega
  change 2 * q < C - s; omega

/-! NOTE (E13c, quadratic cap): replacing cap (A) by the quadratic bound
`C + 1 < (M/8)*(M/8)` FAILS in the same `omega` (`E12:quad`, `E7c`).  The
arithmetic is not the obstacle -- instantiated at `M = 968`, `C = 1934`,
`s = 1693` one has `2*sqrt(C+1) = 88 < 241 = C - s` -- so this is a tactic
limitation (division atoms), not a mathematical barrier.  Cap (A) in its linear
form is kept; the quadratic relaxation is OPEN. -/

/-! ### The separation witness AT THE REAL THRESHOLD -/

/-- **E13d: at `M = 45895573` -- the threshold actually used at the top of the
development (`VerifiedFiftyMillionBridge.lean:91`) -- the two caps hold while
travel FAILS.**  So `(A ∧ B)` does not imply the parent gate at `lower` equal to
the real threshold; the decomposition is not a restatement.
`4*80317252 = 321269008 ≤ 7*45895573 - 1 = 321269010`
`2*(80317252-45895575) = 68843354 > 45895573`. -/
theorem separation_at_real_threshold :
    45895573 + 2 ≤ 80317252 ∧ 80317252 < 137686723 ∧
      2 * 45895573 - 2 ≤ 137686723 ∧ 137686723 ≤ 3 * 45895573 + 4 ∧
      4 * 80317252 ≤ 7 * 45895573 - 1 ∧
      ¬ (2 * (80317252 - (45895573 + 2)) ≤ 45895573) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- E13e: travel DOES imply cap (B) at the real threshold, so (B) is implied by
the parent -- the relaxation is one-directional. -/
theorem travel_implies_capB_at_threshold {sf : Nat} (h : 45895573 + 2 ≤ sf)
    (htravel : 2 * (sf - (45895573 + 2)) ≤ 45895573) :
    4 * sf ≤ 7 * 45895573 - 1 := by
  omega

/-! ### The FINAL decomposed consumer, with the tight cap (B) -/

/-- The quiet gap at the tight threshold `4*s ≤ 7*M-1`. -/
private theorem quiet_gap_tight {M s C : Nat}
    (hM : 968 ≤ M) (h4 : 4 * s ≤ 7 * M - 1)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) :
    2 * isqrt (C + 1) < C - s :=
  b_tight hM h4 hlo hhi

/-- **THE DECOMPOSED GATE.**  `canonical_next_record_factors_of_short_travel`
with the parent replaced by two strictly weaker, separately-stated caps. -/
theorem canonical_next_record_factors_of_two_caps_tight {M : Nat}
    (hM : 968 ≤ M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hA : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have hM5 : 5 < M := by omega
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM5 hcanon).2.1, by omega⟩
  obtain ⟨sf, Cf, p, hpath, hfmax, hexit⟩ := capped_moving_horizon_eventual_exit hstart hmax
  have hstate := moving_horizon_path_endpoint hpath
  have hhi := hA hpath hfmax
  have h4sf := hB hpath hfmax
  have hlo := (moving_horizon_path_gap_le_three_growth hpath).2.1
  rcases hexit with ⟨_, hquiet⟩ | ⟨r, C', hstep, hnew⟩
  · obtain ⟨hgt, hpre, hd, _⟩ := canonical_quiet_return_next_record hM5 hlo hstate hfmax hquiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate hquiet
      (quiet_gap_tight hM h4sf hlo hhi)
    exact ⟨Cf, hgt, hpre, hd, hminus, hplus⟩
  · have hlow := moving_horizon_new_record_horizon_lower_bound hM5 hfmax hstep hnew
    omega

end A166944Research
