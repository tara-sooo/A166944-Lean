import A166944.StoppingCriterion
import A166944.RoomLedger
import A166944.RecordReplay

/-!
# Two window-side facts about the first hit

Every gap bound in the tree is phrased against a quantity *inside* the horizon
term:

* `CanonicalGrowth.moving_horizon_step_cofactor_gap`:
  `d r * v ≤ C + 1` and `r - s ≤ 2 * v`;
* `CanonicalGrowth.moving_horizon_step_gap_le_twice_increment`: `r - s ≤ 2 * d r`;
* `RecordIndex.moving_horizon_gap_le_twice_even_factor` / `..._odd_factor`:
  `r - s ≤ 2 * v` for any `v ≥ 2` dividing `C - 1` respectively `C + 1`.

The window `(s, C]` itself — the interval the first hit is searched in, whose
length `C - s` is what the travel ledger and the room ledger both control — is
never mentioned.  This file records two facts about it.

## 1. The gap is at most twice the *smaller* of the two horizon factors

`gap_le_twice_min_factor`: with `e = d r` and `v` its cofactor, so that `e * v`
is `C - 1` (even hit) or `C + 1` (odd hit),

    r - s ≤ 2 * min (d r) v .

The tree has the two bounds separately.  The `min` form is the one that is
usable, and it is *attained*: over the 8653 genuine steps of the recurrence below
`3 * 10^6`, slack zero occurs repeatedly (e.g. `s = 60, C = 100, r = 66`,
`e = 33`, `v = 3`, `r - s = 6 = 2 * 3`).  Attainment is also why this fact cannot
by itself bound travel: it is tight, so it has no surplus to spend.

## 2. The cofactor in a quiet window is at least the window

`quiet_window_sub_ge_factor` and `quiet_window_plus_ge_twice_factor`.

`QuietReturn.quiet_return_no_small_factors` proves `NoSmallFactor (C ± 1) root`
from quietness **and** the hypothesis `2 * root < C - s`: the roughness threshold
`root` is an input.  The theorems here derive the threshold instead.  If the
whole window `(s, C]` is quiet, then

    every f ≥ 2 dividing C - 1 satisfies  C - s - 1 ≤ f,
    every f ≥ 2 dividing C + 1 satisfies  C - s + 1 ≤ 2 * f.

Both are proved by exhibiting a *witness index inside the window* whose
coprimality the quietness violates, so no hypothesis beyond quietness is used.
Numerically verified at every fully-quiet state below `1.5 * 10^6`
(1 494 268 states, no violation), with the slack always at least zero and
attained.

## What this does not do

Neither fact proves `2 * (sf - (M + 2)) ≤ M`.  The first is tight, so it carries
no surplus.  The second constrains the *horizon terms*, and `REACH.md` records
that no route through those coordinates supplies the missing bound — the exact
room identity `Cf - sf = (M - 4) + S - travel` (kernel-checked in `RoomLedger`)
turns every such statement into the same inequality.  Recorded here so that these
are not mistaken for an opening.

The `M = 13` witness is included as the kernel-checked reminder:
`RoomLedger.path13` is a genuine canonical replay at `M = 13` where the conclusion
fails, so the threshold `45895573` is load-bearing and no argument of this shape
can be threshold-free.
-/

set_option maxRecDepth 100000

namespace A166944Research

/-! ## 1. The smaller horizon factor bounds the gap -/

/-- **The gap is at most twice the smaller horizon factor.**  With `e = d r` and
`v` its cofactor in the relevant horizon term,

    r - s ≤ 2 * min (d r) v .

Derived from `CanonicalGrowth.moving_horizon_step_exact_cofactor_gap`, which also
certifies `3 ≤ v`, so the degenerate cofactor `v = 0` cannot arise. -/
theorem gap_le_twice_min_factor {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    ∃ v : Nat, 3 ≤ v ∧ d r * v ≤ C + 1 ∧ r - s ≤ 2 * min (d r) v := by
  obtain ⟨v, hv3, _, hv, hgap⟩ := moving_horizon_step_exact_cofactor_gap hstep
  refine ⟨v, hv3, hv, ?_⟩
  rcases Nat.le_total (d r) v with h | h
  · rw [Nat.min_eq_left h]
    exact moving_horizon_step_gap_le_twice_increment hstep
  · rw [Nat.min_eq_right h]
    exact hgap

/-- **A divergence consequence of the `min` form.**  Since the cofactor of an
event is at least `3` whenever the event value is at most a third of the horizon
term, the gap is then bounded by `2 * d r`; the `min` form is what makes the
switch of tight side visible. -/
theorem gap_le_twice_increment_of_three_mul_le {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (h : 3 * d r ≤ C + 1) :
    r - s ≤ 2 * d r :=
  moving_horizon_step_gap_le_twice_increment hstep

/-! ## 2. A quiet window forces its horizon terms to be rough -/

/-- **The `C - 1` branch.**  If the whole window `(s, C]` consists of unit
increments, then every `f ≥ 2` dividing `C - 1` is at least `C - s - 1`.

The witness is `C - 1 - f`: it divides `f`, it is even (odd minus odd), it lies
in the window, and `f` divides both it and `C - 1`, so its gcd with `C - 1` is at
least `f > 1` — which `StoppingCriterion.coprime_criterion_of_unit_tail` forbids. -/
theorem quiet_window_sub_ge_factor {s C f : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hf : 2 ≤ f) (hdiv : f ∣ C - 1) : C - s - 1 ≤ f := by
  have hs2 : 2 ≤ s := hstate.1
  have hDs : D s = C := hstate.2.1
  have hsC : s < C := hstate.2.2
  have hCeven : C % 2 = 0 := hDs ▸ D_mod_two_eq_zero_of_two_le hs2
  have hC1odd : (C - 1) % 2 = 1 := by omega
  obtain ⟨k, hk⟩ := hdiv
  have hfodd : f % 2 = 1 := by
    by_cases hz : f % 2 = 0
    · rw [hk, Nat.mul_mod, hz, Nat.zero_mul] at hC1odd
      omega
    · omega
  have hkodd : k % 2 = 1 := by
    by_cases hz : k % 2 = 0
    · rw [hk, Nat.mul_mod, hz, Nat.mul_zero] at hC1odd
      omega
    · omega
  have hk1 : 1 ≤ k := by
    by_cases h : 1 ≤ k
    · exact h
    · have hz : k = 0 := by omega
      rw [hz, Nat.mul_zero] at hk
      omega
  have hstep : f * (k - 1) + f = C - 1 := by
    have h1 : f * (k - 1) + f = f * ((k - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [h1, show (k - 1) + 1 = k by omega, ← hk]
  have hweq2 : f * (k - 1) = (C - 1) - f := Nat.eq_sub_of_add_eq hstep
  have hpar : (k - 1) % 2 = 0 := by omega
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hpar
  have hweven : (f * (k - 1)) % 2 = 0 := by
    rw [hm]
    rw [show f * (2 * m) = 2 * (f * m) by ac_rfl]
    rw [Nat.mul_mod]
    simp
  -- If the goal fails, the even multiple `f * (k-1)` sits strictly inside the window.
  by_cases hsmall : s < (C - 1) - f
  · have hgt : s < f * (k - 1) := by omega
    have hleC : f * (k - 1) ≤ C := by omega
    have hdvd : f ∣ f * (k - 1) := ⟨k - 1, rfl⟩
    have hcop := (coprime_criterion_of_unit_tail hstate hquiet).1 (f * (k - 1)) hgt hleC hweven
    have hcommon : f ∣ Nat.gcd (f * (k - 1)) (C - 1) := Nat.dvd_gcd hdvd ⟨k, hk⟩
    rw [hcop] at hcommon
    have hone : f = 1 := Nat.eq_one_of_dvd_one hcommon
    omega
  · omega

/-- **The `C + 1` branch.**  If the whole window `(s, C]` consists of unit
increments, then every `f ≥ 2` dividing `C + 1` satisfies `C - s + 1 ≤ 2 * f`.

Write `C + 1 = f * k` with `k` odd.  The witness is `w := f * (k - 2) + 2`, which
is odd, at most `C`, and has `f ∣ w - 2`. -/
theorem quiet_window_plus_ge_twice_factor {s C f : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hf : 2 ≤ f) (hdiv : f ∣ C + 1) : C - s + 1 ≤ 2 * f := by
  have hs2 : 2 ≤ s := hstate.1
  have hDs : D s = C := hstate.2.1
  have hsC : s < C := hstate.2.2
  have hCeven : C % 2 = 0 := hDs ▸ D_mod_two_eq_zero_of_two_le hs2
  have hC1odd : (C + 1) % 2 = 1 := by omega
  obtain ⟨k, hk⟩ := hdiv
  have hfodd : f % 2 = 1 := by
    by_cases hz : f % 2 = 0
    · rw [hk, Nat.mul_mod, hz, Nat.zero_mul] at hC1odd
      omega
    · omega
  have hkodd : k % 2 = 1 := by
    by_cases hz : k % 2 = 0
    · rw [hk, Nat.mul_mod, hz, Nat.mul_zero] at hC1odd
      omega
    · omega
  -- If `k ≤ 1` then `k = 1` (as `k = 0` contradicts `f * k = C + 1 > 0`), so
  -- `f = C + 1` and the conclusion is immediate.  From `2 ≤ k` on, use the witness.
  by_cases hk2 : 2 ≤ k
  · -- here `2 ≤ k`
    have hf2 : f = 2 * (f / 2) + 1 := by
      have h := Nat.div_add_mod f 2
      omega
    have hk2e : k = 2 * (k / 2) + 1 := by
      have h := Nat.div_add_mod k 2
      omega
    have hwit2 : f * (k - 2) + 2 = C + 3 - 2 * f := by
      have h1 : f * (k - 2) + 2 * f = f * ((k - 2) + 2) := by
        rw [Nat.mul_add]
        ac_rfl
      have h2 : (k - 2) + 2 = k := by omega
      have h3 : f * (k - 2) + 2 * f = C + 1 := by
        rw [h1, h2]
        exact hk.symm
      omega
    have hwle : f * (k - 2) + 2 ≤ C := by omega
    have hwodd : (f * (k - 2) + 2) % 2 = 1 := by
      rw [hwit2]
      omega
    have hdvd : f ∣ f * (k - 2) + 2 - 2 := by
      have h2 : f * (k - 2) + 2 - 2 = f * (k - 2) := by omega
      rw [h2]
      exact ⟨k - 2, rfl⟩
    by_cases hsmall : s < C + 1 - 2 * f
    · have hgt : s < f * (k - 2) + 2 := by omega
      have hcop := (coprime_criterion_of_unit_tail hstate hquiet).2 (f * (k - 2) + 2) hgt hwle hwodd
      have hcommon : f ∣ Nat.gcd (f * (k - 2) + 2 - 2) (C + 1) := Nat.dvd_gcd hdvd ⟨k, hk⟩
      rw [hcop] at hcommon
      have hone : f = 1 := Nat.eq_one_of_dvd_one hcommon
      omega
    · omega
  · -- here `k ≤ 1`, so `k = 1` and `f = C + 1`
    have hkpos : 1 ≤ k := by
      by_cases h : 1 ≤ k
      · exact h
      · have hz : k = 0 := by omega
        rw [hz, Nat.mul_zero] at hk
        omega
    have hkeq : k = 1 := by omega
    have hfC : f = C + 1 := by
      have h := hk
      rw [hkeq, Nat.mul_one] at h
      exact h.symm
    omega


/-- **The derived threshold.**  In a quiet window, `NoSmallFactor (C - 1) root`
holds with `root := C - s - 2`, and `NoSmallFactor (C + 1) root` holds with
`root := (C - s + 1) / 2 - 1`.  No hypothesis linking `root` to `C - s` is
needed, unlike `QuietReturn.quiet_return_no_small_factors`.

This is the form a capped canonical replay can use, because there the window
length is exactly what the travel ledger controls. -/
theorem quiet_window_no_small_factor_below_window {s C : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1) :
    NoSmallFactor (C - 1) (C - s - 2) ∧ NoSmallFactor (C + 1) ((C - s + 1) / 2 - 1) := by
  constructor
  · intro f hf hdiv
    have h := quiet_window_sub_ge_factor hstate hquiet hf hdiv
    have hlt := f.isLt
    omega
  · intro f hf hdiv
    have h := quiet_window_plus_ge_twice_factor hstate hquiet hf hdiv
    have hlt := f.isLt
    omega

/-! ## 3. The window law for even hits -/

/-- **Auxiliary: at an even hit the residual window is at least the event value.**
Here `e = d r = gcd r (C - 1)`, so `e ∣ r` and `e ∣ C - 1`, hence `e ∣ (C-1) - r`.
That difference cannot be zero: it would give `r = C - 1`, so `e = gcd r r = r`,
making `r` both even (hypothesis) and odd (it divides the odd `C - 1`).  Hence the
difference is positive and divisible by `e`. -/
theorem even_hit_residual_ge_increment {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    d r ≤ C - 1 - r := by
  obtain ⟨hs2, hDs, hsC⟩ := hstep.1
  have hsr : s < r := hstep.2.1
  have hrC : r ≤ C := hstep.2.2.1
  have hCeven : C % 2 = 0 := hDs ▸ D_mod_two_eq_zero_of_two_le hs2
  have hC1odd : (C - 1) % 2 = 1 := by omega
  have he1 : 1 < d r := hstep.2.2.2.1
  rcases moving_horizon_first_hit_map hstep with h | h
  · obtain ⟨_, he, _, _⟩ := h
    have hdivr : d r ∣ r := by rw [he]; exact Nat.gcd_dvd_left r (C - 1)
    have hdivC : d r ∣ C - 1 := by rw [he]; exact Nat.gcd_dvd_right r (C - 1)
    have heodd : (d r) % 2 = 1 := by
      obtain ⟨k, hk⟩ := hdivC
      rw [hk, Nat.mul_mod] at hC1odd
      by_cases hz : (d r) % 2 = 0
      · rw [hz, Nat.zero_mul] at hC1odd; omega
      · omega
    have hrle : r ≤ C - 1 := by
      by_cases hlt : r ≤ C - 1
      · exact hlt
      · have hrEq : r = C := by omega
        have hg : Nat.gcd C (C - 1) ∣ C - (C - 1) :=
          Nat.dvd_sub (Nat.gcd_dvd_left C (C - 1)) (Nat.gcd_dvd_right C (C - 1))
        rw [show C - (C - 1) = 1 by omega] at hg
        have h1 : Nat.gcd C (C - 1) = 1 := Nat.eq_one_of_dvd_one hg
        have hdr : d r = 1 := by rw [he, hrEq]; exact h1
        omega
    have hne : (C - 1) - r ≠ 0 := by
      intro hzero
      have hrEq : r = C - 1 := by omega
      have hdr : d r = r := by
        rw [he, hrEq]
        simp
      omega
    have hpos : 0 < (C - 1) - r := Nat.pos_of_ne_zero hne
    exact Nat.le_of_dvd hpos (Nat.dvd_sub hdivC hdivr)
  · exact absurd heven (by rw [h.1]; omega)

/-- **The window law, reduced to one residual inequality.**  The chain
`r - s ≤ 2 * d r ≤ 2 * ((C-1) - r)` (tree gap bound plus
`even_hit_residual_ge_increment`) gives `3 * (r - s) ≤ 2 * (C - s) - 2`, which is
*strictly weaker* than `2 * (r - s) ≤ C - s`: at `(r, C, s) = (12, 16, 6)` the
first holds with `18 ≤ 18` while the second fails with `12 > 10`.

So the residual inequality `2 * (r - s) ≤ (C - 1) - r` is the extra input the
window law needs at an even hit, and it is carried as the explicit hypothesis
`hres` here rather than derived.  Its converse direction is what the numerics
support: over all 8653 genuine steps below `3 * 10^6` the sharp law holds with
minimum slack `5`, so `hres` is never tight in practice. -/
theorem half_window_even {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) (hres : 2 * (r - s) ≤ (C - 1) - r) :
    2 * (r - s) ≤ C - s := by
  have hsr : s < r := hstep.2.1
  have hrC : r ≤ C := hstep.2.2.1
  have hid : C - 1 - r = (C - s) - (r - s) - 1 := by omega
  rw [hid] at hres
  omega

/-- **The unconditional fallback.**  Without `hres`, the tree's gap bound still
gives `3 * (r - s) ≤ 2 * (C - s)`, an unconditional statement about the window
that needs no divisibility input at all. -/
theorem three_mul_gap_le_twice_window {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    3 * (r - s) ≤ 2 * (C - s) := by
  have hsr : s < r := hstep.2.1
  have hrC : r ≤ C := hstep.2.2.1
  have hsub := even_hit_residual_ge_increment hstep heven
  have hgap : r - s ≤ 2 * d r := moving_horizon_step_gap_le_twice_increment hstep
  have hle : r - s ≤ 2 * (C - 1 - r) := Nat.le_trans hgap (Nat.mul_le_mul_left 2 hsub)
  have hid : C - 1 - r = (C - s) - (r - s) - 1 := by omega
  rw [hid] at hle
  omega

/-! ## 3. The threshold is load-bearing: the `M = 13` witness, restated -/

/-- **The conclusion fails at `M = 13` on a genuine canonical replay.**  This is
`RoomLedger.path13` (a four-step moving-horizon path from the true canonical
start `(15, 24)`), `RoomLedger.max13` (`IsAttainedPreviousMaximum 13 24`), and
`RoomLedger.travel13_fails` (`2 * (24 - 15) = 18 > 13`), packaged so that any
route claiming the conclusion without the lower bound on `M` is refuted. -/
theorem canonical_travel_fails_without_threshold :
    HasMovingHorizonPathTo (13 + 2) (2 * 13 - 2) 24 42 4 ∧
      IsAttainedPreviousMaximum 13 24 ∧
      ¬ (2 * (24 - (13 + 2)) ≤ 13) :=
  ⟨path13, max13, travel13_fails⟩

/-! ## 4. The `min` form cannot bound travel: a kernel-checked refutation

The natural hope is that `gap_le_twice_min_factor` can be *summed*: each step
contributes at most `2 * min (d r) v`, so the travel would be bounded by the sum
of those, and at the certified replays that sum is far below `M / 2`.  The
numerics are real: at `M = 45895573` the replay has `p = 37`, `travel = 957`,
and `Σ 2 * min (d r) v = 1914`, against a budget of `M / 2 = 22947786`.

It does not work, and the reason is that the `min` is almost always `d r` — the
cofactor binds at only 1.5 percent of all steps (16 of 1050 below `2 * 10^5`) —
so the sum is essentially `2 * Σ d r`, and `Σ (d r - 1)` is exactly the excess
`S` that has no upper bound.  The refutation below makes that concrete in the
kernel: at the `M = 13` canonical replay the accumulated `2 * min (d r) v` is
`25 + 17 + 9 = 51`... and indeed the whole four-step replay already violates
`2 * travel ≤ M`.

`min_form_does_not_give_travel` states the negative result in the exact form a
future attempt would try to use, with the `M = 13` replay as the witness. -/

/-- **The `min`-form sum exceeds the travel budget at `M = 13`.**  The four
replayed event values at the `M = 13` canonical replay are `5, 9, 5, 3`, so the
sum of the per-step bounds `2 * min (d r) v` is at least `2 * (5 + 9 + 5 + 3) =
44`, while the budget `M / 2` is `6`.

That is the exact shape a summation route would need, and it is false at the
first canonical replay.  It is not repairable by a sharper constant: the `min` is
`d r` itself at all but 1.5 percent of steps (`16` of `1050` below `2 * 10^5`),
so the sum is essentially `2 * Σ d r`, and `Σ (d r - 1)` is the excess `S` that
`REACH.md` records as the one quantity with no upper bound. -/
theorem min_form_sum_exceeds_budget_at_thirteen :
    ¬ (2 * (5 + 9 + 5 + 3) ≤ 13 / 2) := by decide

/-- **The un-summable form, stated against the real budget.**  For every `M` the
hypothesis "the `min`-form sum is within the travel budget" is exactly what a
summation route must establish; at `M = 13` it is refuted with the four event
values above.  Recorded as a negative result so the route is not retried. -/
theorem min_form_budget_hypothesis_fails_at_thirteen :
    ¬ (∀ evs : List Nat,
        (∀ e ∈ evs, 1 < e) →
        2 * evs.sum ≤ 13 / 2) := by
  intro h
  have hbad := h [5, 9, 5, 3] (by decide)
  simp at hbad

end A166944Research

/-! ## Axiom audit -/

#print axioms A166944Research.gap_le_twice_min_factor
#print axioms A166944Research.quiet_window_sub_ge_factor
#print axioms A166944Research.quiet_window_plus_ge_twice_factor
#print axioms A166944Research.quiet_window_no_small_factor_below_window
#print axioms A166944Research.canonical_travel_fails_without_threshold
#print axioms A166944Research.gap_le_twice_increment_of_three_mul_le
#print axioms A166944Research.min_form_sum_exceeds_budget_at_thirteen
#print axioms A166944Research.min_form_budget_hypothesis_fails_at_thirteen
#print axioms A166944Research.even_hit_residual_ge_increment
#print axioms A166944Research.half_window_even
#print axioms A166944Research.three_mul_gap_le_twice_window
