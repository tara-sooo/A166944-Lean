import A166944.Lemmas

/-!
# aG · red team, part 2: the structural claims, settled in Lean

Pure core only (`decide`/`omega`/`simp`/`rfl`); no `sorry`/`admit`/`axiom`/`unsafe`.
Scratch only; the repository is untouched.
-/

namespace A166944Research

/-! ## 1. CLAIM 3/4: the independence corollary is *correct*, and it is a two-line
corollary of prior art

`Lemmas.moving_horizon_successive_event_gcd_dvd_three` (2026-09-07, commit
`fcd8f37`) gives `gcd (d r) (d u) | 3` with **no parity hypothesis**.  Everything
"parity decides the gcd" adds is a case split on that one theorem.  Below is the
part that was actually missing from the tree: the *consequence* for divisors
greater than three. -/

/-- Anything dividing both consecutive event values divides the gcd, hence `3`. -/
theorem common_divisor_dvd_three {s C r C' u C'' q : Nat}
    (h1 : IsMovingHorizonStep s C r C') (h2 : IsMovingHorizonStep r C' u C'')
    (hq1 : q ∣ d r) (hq2 : q ∣ d u) : q ∣ 3 :=
  Nat.dvd_trans (Nat.dvd_gcd hq1 hq2)
    (moving_horizon_successive_event_gcd_dvd_three h1 h2)

/-- **The independence claim, proved.**  A `q > 3` cannot divide two consecutive
event values.  So for every prime `q > 3`, the set of indices whose event value is
divisible by `q` contains no two consecutive replay steps: it is an independent set
in the path graph on the replay's steps. -/
theorem no_large_common_divisor {s C r C' u C'' q : Nat}
    (h1 : IsMovingHorizonStep s C r C') (h2 : IsMovingHorizonStep r C' u C'')
    (hq1 : q ∣ d r) (hq2 : q ∣ d u) : q ≤ 3 := by
  have hq3 : q ∣ 3 := common_divisor_dvd_three h1 h2 hq1 hq2
  rcases Nat.eq_zero_or_pos q with h | h
  · omega
  · exact Nat.le_of_dvd (by decide : 0 < 3) hq3

/-- Contrapositive in the shape a "no two adjacent" statement needs. -/
theorem not_dvd_both_of_three_lt {s C r C' u C'' q : Nat}
    (h1 : IsMovingHorizonStep s C r C') (h2 : IsMovingHorizonStep r C' u C'')
    (hq : 3 < q) : ¬ (q ∣ d r ∧ q ∣ d u) := by
  rintro ⟨a, b⟩
  have := no_large_common_divisor h1 h2 a b
  omega

/-- `gcd = 3` **does** force `3` to divide both values: "both divisible by 3" is
correct, and the `M = 43` replay realises it at index `66`. -/
theorem gcd_three_dvd_both {s C r C' u C'' : Nat}
    (h1 : IsMovingHorizonStep s C r C') (h2 : IsMovingHorizonStep r C' u C'')
    (hg : Nat.gcd (d r) (d u) = 3) : 3 ∣ d r ∧ 3 ∣ d u := by
  constructor
  · rw [← hg]; exact Nat.gcd_dvd_left _ _
  · rw [← hg]; exact Nat.gcd_dvd_right _ _

/-! ## 2. The `gcd = 3` witness: `e = 33` and the neighbouring `e = 7`

`M = 43`'s replay has events `5, 3, 7, 5, 33, 7` at indices `47, 48, 51, 60, 66,
79`.  The `33` is divisible by `3`, the `7` after it is not: `33 = 3 * 11`. -/

theorem M43_33_then_7 : d 66 = 33 ∧ d 79 = 7 ∧ 3 ∣ 33 ∧ ¬ 3 ∣ 7 ∧ 33 = 3 * 11 := by decide

/-- The raw sequence's smallest `gcd = 3` pair, `(88811, 88812)`, has **both**
values equal to `3`: even the "both divisible by 3" reading never produces a
large composite event in this pair. -/
theorem raw_gcd3_pair_both_three : d 88811 = 3 ∧ d 88812 = 3 := by
  constructor <;> (set_option maxRecDepth 1000000 in decide)

/-! ## 3. ANGLE C IS VACUOUS, in the same sense as angle A

`e | C ± 1` is `constant_D_event_map` plus `Nat.gcd_dvd_right` (see `F.lean`,
`e_dvd_C_even`/`e_dvd_C_odd`): it is the *definition* of the event value.  So the
only content in "`C ± 1` is always composite" beyond the definition is the
strictness `e < C ± 1`.  Below: strictness alone yields compositeness in one line,
for any `e`, with no arithmetic input whatsoever. -/

/-- **Compositeness from a proper divisor.**  If `1 < e`, `e ∣ n` and `e < n`,
then `n` has a proper factor, i.e. `n` is composite.  This is the entire
arithmetic content of claim 1 beyond the definition. -/
theorem e_dvd_C_of_step {s C r C' : Nat} (h : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r ∣ C - 1) ∧ (¬ r % 2 = 0 → d r ∣ C + 1) := by
  have hr2 : 2 ≤ r := Nat.le_trans h.1.1 (Nat.le_of_lt h.2.1)
  have hD : D (r - 1) = C := h.2.2.2.2.2.1
  have hmap := constant_D_event_map hr2 hD
  constructor
  · intro hpar
    rw [if_pos hpar] at hmap
    rw [hmap]; exact Nat.gcd_dvd_right _ _
  · intro hpar
    rw [if_neg hpar] at hmap
    rw [hmap]; exact Nat.gcd_dvd_right _ _

theorem e_dvd_C_even_of_step {s C r C' : Nat} (h : IsMovingHorizonStep s C r C')
    (hpar : r % 2 = 0) : d r ∣ C - 1 := (e_dvd_C_of_step h).1 hpar

theorem e_dvd_C_odd_of_step {s C r C' : Nat} (h : IsMovingHorizonStep s C r C')
    (hpar : ¬ r % 2 = 0) : d r ∣ C + 1 := (e_dvd_C_of_step h).2 hpar

theorem strictness_available {s C r C' : Nat} (h : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r < C - 1) ∧ (¬ r % 2 = 0 → d r < C + 1) := by
  rcases moving_horizon_step_event_package h with hA | hB
  · obtain ⟨he, _, hp, _⟩ := hA
    exact ⟨fun _ => hp, fun hc => absurd he hc⟩
  · obtain ⟨ho, _, hp, _⟩ := hB
    exact ⟨fun hc => by omega, fun _ => hp⟩

theorem composite_of_proper_divisor {e n : Nat} (he : 1 < e) (hd : e ∣ n) (hlt : e < n) :
    ∃ f : Nat, 2 ≤ f ∧ f < n ∧ f ∣ n :=
  ⟨e, he, hlt, hd⟩

/-- **Claim 1, reduced to its actual content.**  For a moving-horizon step,
`C ± 1` is composite **because** the event value is a proper divisor of it --
no bound involving `M` appears anywhere. -/
theorem horizon_term_composite_of_step {s C r C' : Nat}
    (h : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → ∃ f : Nat, 2 ≤ f ∧ f < C - 1 ∧ f ∣ C - 1) ∧
      (¬ r % 2 = 0 → ∃ f : Nat, 2 ≤ f ∧ f < C + 1 ∧ f ∣ C + 1) := by
  have he : 1 < d r := h.2.2.2.1
  have hproper := strictness_available h
  exact ⟨fun hpar => composite_of_proper_divisor he (e_dvd_C_even_of_step h hpar)
      (hproper.1 hpar),
    fun hpar => composite_of_proper_divisor he (e_dvd_C_odd_of_step h hpar)
      (hproper.2 hpar)⟩

end A166944Research
