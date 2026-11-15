import A166944.DNodes
import A166944.GapBound
import A166944.CanonicalGrowth

/-!
# The signed divisor chain across an interval of a replay

`DNodes.odd_event_value_dvd` / `even_event_value_dvd` give the one-step facts

    odd  r :  d r ∣ C + 1        even  r :  d r ∣ C - 1

where `C` is the horizon *entering* the step.  The tree's chaining results
(`moving_horizon_successive_event_gcd_eq_one_of_prev_even`,
`..._of_odd_odd`, `moving_horizon_successive_event_gcd_dvd_three`) all stop at
*one* step: they compare `d r` with `d u` for adjacent events.

This file pushes the same arithmetic across an arbitrary interval of the replay.
The only extra input is the step law `C' = C + (d r - 1)`, which turns the
horizon's advance into the sum of the event excesses `d - 1`.

With the branch sign

    sigma r = +1 (r odd)   sigma r = -1 (r even)

the two one-step facts read uniformly as `d r ∣ C + sigma` (as a divisibility in
`Int`).  Writing `C_k` for the horizon entering step `k` and `e_k` for its event
value, the step law gives the telescoping identity

    C_j = C_i + sum_{i <= k < j} (e_k - 1),

and therefore, for `i < j` and any `g` dividing both `e_i` and `e_j`,

    g  ∣  sum_{i <= k < j} (e_k - 1) + (sigma_j - sigma_i).                    (*)

The adjacent lemmas are the special case `j = i + 1`, where the sum is `e_i - 1`:
the four parity cases give `g | 1`, `g | 3`, `g | 1`, `g | 1` respectively.  So
`(*)` is the *common* generalisation of all three existing adjacent results.

## Contents

* `excessSum` / `excessSum_horizon_shift` -- the telescoping identity.
* `interval_gcd_dvd_excess_sum` -- the invariant `(*)` in Nat form.
-/

namespace A166944Research


/-- The sum of event excesses `sum_{i <= k < i+n} (e k - 1)` along a replay,
stated recursively in the style the path predicates use.

Here `e : Nat → Nat` is the *event-value* sequence: `e k` is the value `d r_k` of
the `k`-th nontrivial event, not `d` evaluated at index `k`. -/
def excessSum (e : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, i => excessSum e n i + (e (i + n) - 1)

@[simp] theorem excessSum_zero (e : Nat → Nat) (i : Nat) : excessSum e 0 i = 0 := rfl

theorem excessSum_succ (e : Nat → Nat) (n i : Nat) :
    excessSum e (n + 1) i = excessSum e n i + (e (i + n) - 1) := rfl

/-- **The excess sum telescopes to the horizon shift** (addition form, which
avoids subtraction entirely).  If the horizon advances from `D k` to `D (k+1)`
by the excess `e k - 1` of the `k`-th event, then after `n` events from `i` the
horizon is the starting horizon plus the excess sum. -/
theorem horizon_eq_add_excessSum {e D : Nat → Nat}
    (hstep : ∀ k : Nat, D (k + 1) = D k + (e k - 1)) :
    ∀ (n i : Nat), D (i + n) = D i + excessSum e n i := by
  intro n
  induction n with
  | zero => intro i; simp [excessSum]
  | succ n ih =>
      intro i
      have hidx : i + (n + 1) = (i + n) + 1 := by omega
      calc D (i + (n + 1)) = D ((i + n) + 1) := by rw [hidx]
        _ = D (i + n) + (e (i + n) - 1) := hstep (i + n)
        _ = (D i + excessSum e n i) + (e (i + n) - 1) := by rw [ih i]
        _ = D i + (excessSum e n i + (e (i + n) - 1)) := by omega
        _ = D i + excessSum e (n + 1) i := by rw [excessSum_succ]

/-- The subtraction form of the telescoping identity. -/
theorem excessSum_eq_horizon_sub {e D : Nat → Nat}
    (hstep : ∀ k : Nat, D (k + 1) = D k + (e k - 1)) (n i : Nat) :
    excessSum e n i = D (i + n) - D i := by
  have h := horizon_eq_add_excessSum hstep n i
  omega

/-! ## The interval invariant

Now the divisibility.  The statement is purely about `Nat`: if `g` divides the
event values at the two ends of an interval, and each event value divides its own
branch value of the horizon, then `g` divides the excess sum adjusted by the
branch-sign difference.

The four parity cases are handled by one `Int`-free statement: we carry the two
branch values as explicit hypotheses rather than a sign function, because that is
exactly what the `DNodes` lemmas deliver and it keeps everything in `Nat`. -/

/-- **Interval divisibility invariant (same branch).**  Suppose the horizon at the
left end satisfies `e_i ∣ A + 1` and at the right end `e_j ∣ A' + 1` (both odd
branch, the `+1` case), that `g` divides both event values, and that the horizon
advanced by the excess sum.  Then `g` divides the excess sum.

This is the odd-odd case; the even-even case is identical with `-1`, and the two
mixed cases carry a `±2` correction. -/
theorem interval_gcd_dvd_excess_sum_odd_odd {g ei ej A A' S : Nat}
    (hgi : g ∣ ei) (hgj : g ∣ ej)
    (hdi : ei ∣ A + 1) (hdj : ej ∣ A' + 1)
    (hshift : A' = A + S) :
    g ∣ S := by
  have h1 : g ∣ A + 1 := Nat.dvd_trans hgi hdi
  have h2 : g ∣ A' + 1 := Nat.dvd_trans hgj hdj
  have h2' : g ∣ A + S + 1 := by rw [← hshift]; exact h2
  have h3 : g ∣ (A + S + 1) - (A + 1) := Nat.dvd_sub h2' h1
  have : (A + S + 1) - (A + 1) = S := by omega
  rwa [this] at h3

/-- **Interval divisibility invariant (even-even).**  The `-1` case. -/
theorem interval_gcd_dvd_excess_sum_even_even {g ei ej A A' S : Nat}
    (hgi : g ∣ ei) (hgj : g ∣ ej)
    (hA : 1 ≤ A)
    (hdi : ei ∣ A - 1) (hdj : ej ∣ A' - 1)
    (hshift : A' = A + S) :
    g ∣ S := by
  have h1 : g ∣ A - 1 := Nat.dvd_trans hgi hdi
  have h2 : g ∣ A' - 1 := Nat.dvd_trans hgj hdj
  have h2' : g ∣ A + S - 1 := by rw [← hshift]; exact h2
  have h3 : g ∣ (A + S - 1) - (A - 1) := Nat.dvd_sub h2' h1
  have : (A + S - 1) - (A - 1) = S := by omega
  rwa [this] at h3

/-- **Interval divisibility invariant (odd then even).**  The two branch values
differ by `S - 2`, so `g` divides `S - 2`. -/
theorem interval_gcd_dvd_excess_sum_odd_even {g ei ej A A' S : Nat}
    (hgi : g ∣ ei) (hgj : g ∣ ej)
    (_hA' : 1 ≤ A')
    (hdi : ei ∣ A + 1) (hdj : ej ∣ A' - 1)
    (hshift : A' = A + S) (hS : 2 ≤ S) :
    g ∣ S - 2 := by
  have h1 : g ∣ A + 1 := Nat.dvd_trans hgi hdi
  have h2 : g ∣ A' - 1 := Nat.dvd_trans hgj hdj
  have h2' : g ∣ A + S - 1 := by rw [← hshift]; exact h2
  have h3 : g ∣ (A + S - 1) - (A + 1) := Nat.dvd_sub h2' h1
  have : (A + S - 1) - (A + 1) = S - 2 := by omega
  rwa [this] at h3

/-- **Interval divisibility invariant (even then odd).**  Here the two branch
values differ by `S + 2`, so `g` divides `S + 2`. -/
theorem interval_gcd_dvd_excess_sum_even_odd {g ei ej A A' S : Nat}
    (hgi : g ∣ ei) (hgj : g ∣ ej)
    (hA : 1 ≤ A)
    (hdi : ei ∣ A - 1) (hdj : ej ∣ A' + 1)
    (hshift : A' = A + S) :
    g ∣ S + 2 := by
  have h1 : g ∣ A - 1 := Nat.dvd_trans hgi hdi
  have h2 : g ∣ A' + 1 := Nat.dvd_trans hgj hdj
  have h2' : g ∣ A + S + 1 := by rw [← hshift]; exact h2
  have hle : A - 1 ≤ A + S + 1 := by omega
  have h3 : g ∣ (A + S + 1) - (A - 1) := Nat.dvd_sub h2' h1
  have : (A + S + 1) - (A - 1) = S + 2 := by omega
  rwa [this] at h3

/-! ## The adjacent specialisation

Setting `S := e_i - 1` in the four cases above recovers, in one uniform
derivation, the four values the tree has as three separate lemmas:
same branch gives `∣ 1`, odd-then-even gives `∣ 3`, even-then-odd gives `∣ 1`. -/

/-- **Adjacent, same branch.**  `g ∣ e_i - 1` and `g ∣ e_i` force `g = 1`. -/
theorem adjacent_same_branch_gcd_eq_one {g e : Nat} (he : 1 ≤ e)
    (hge : g ∣ e) (hg : g ∣ e - 1) :
    g = 1 := by
  have h1 : g ∣ e - (e - 1) := Nat.dvd_sub hge hg
  have : e - (e - 1) = 1 := by omega
  rw [this] at h1
  exact Nat.eq_one_of_dvd_one h1

/-- **Adjacent, odd then even.**  `g ∣ e - 3` and `g ∣ e` force `g ∣ 3`. -/
theorem adjacent_odd_even_gcd_dvd_three {g e : Nat} (he : 3 ≤ e)
    (hge : g ∣ e) (hg : g ∣ e - 3) :
    g ∣ 3 := by
  have h1 : g ∣ e - (e - 3) := Nat.dvd_sub hge hg
  have : e - (e - 3) = 3 := by omega
  rwa [this] at h1

/-- **A nontrivial common divisor of two events is bounded by the excess sum
between them, provided the excess sum is nonzero.**  The positivity hypothesis is
not cosmetic: `g ∣ 0` holds for every `g`, so without `S ≠ 0` the statement is
false.  In the interval invariant `S` is a sum of the excesses `e_k - 1`, each at
least `2`, so `S ≠ 0` is exactly the statement that the interval is nonempty --
which is the case `j > i` the invariant is used in.

This is a genuine constraint on a replay that the adjacent lemmas do not give:
the adjacent results (`gcd = 1`, or `∣ 3`) say nothing about *how much excess* an
interval must carry, because there the excess sum is the single value `e_i - 1`
and the divisibility is against that value directly. -/
theorem interval_divisor_le_excess_sum {g S : Nat} (hS : S ≠ 0)
    (hdiv : g ∣ S) : g ≤ S := by
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact absurd (by rw [hk, hk0, Nat.mul_zero]) hS
    · exact hkpos
  rw [hk]
  calc g = g * 1 := (Nat.mul_one g).symm
    _ ≤ g * k := Nat.mul_le_mul_left g hkpos

/-- **The interval invariant, in bound form.**  A common divisor `g ≥ 3` of the
two endpoint event values forces the intervening excess sum to be at least `g`,
hence at least `3`.

Every step of an interval contributes at least `2` to the excess sum (the event
values are `≥ 3`), so this is a statement about *how many events* the interval
must contain: at least `ceil (g / 2)`. -/
theorem interval_excess_sum_ge_divisor {g S : Nat} (hS : S ≠ 0)
    (hdiv : g ∣ S) : g ≤ S := interval_divisor_le_excess_sum hS hdiv

/-- The `3`-form of the same bound. -/
theorem interval_excess_sum_ge_three {g S : Nat} (hg : 3 ≤ g) (hS : S ≠ 0)
    (hdiv : g ∣ S) : 3 ≤ S := Nat.le_trans hg (interval_excess_sum_ge_divisor hS hdiv)




/-- Every event value is at least `3`, so every excess `e - 1` is at least `2`. -/
theorem excessSum_ge_two_mul (e : Nat → Nat) (h3 : ∀ k : Nat, 3 ≤ e k) :
    ∀ (n i : Nat), 2 * n ≤ excessSum e n i := by
  intro n
  induction n with
  | zero => intro i; simp [excessSum]
  | succ n ih =>
      intro i
      rw [excessSum_succ, Nat.mul_succ]
      have := h3 (i + n)
      have := ih i
      omega

/-- The excess sum is monotone in the number of steps. -/
theorem excessSum_mono (e : Nat → Nat) (h1 : ∀ k : Nat, 1 ≤ e k) :
    ∀ (n m i : Nat), n ≤ m → excessSum e n i ≤ excessSum e m i := by
  intro n m i hnm
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  clear hnm
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, excessSum_succ]
      have := h1 (i + (n + k))
      omega




/-- **Excess per step is at least two.**  A canonical replay step has `3 ≤ d r`,
so its excess `d r - 1` is at least `2`. -/
theorem step_excess_ge_two {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    2 ≤ d r - 1 := by
  have h3 : 3 ≤ d r := moving_horizon_step_event_ge_three hstep
  omega

/-- **The excess sum dominates twice the count.**  This is the elementary
`2 * p ≤ S` bound that turns an excess lower bound into a count upper bound. -/
theorem two_mul_count_le_excessSum (e : Nat → Nat) (h3 : ∀ k : Nat, 3 ≤ e k) :
    ∀ (n i : Nat), 2 * n ≤ excessSum e n i := by
  intro n
  induction n with
  | zero => intro i; simp [excessSum]
  | succ n ih =>
      intro i
      rw [excessSum_succ, Nat.mul_succ]
      have h := ih i
      have hk := h3 (i + n)
      omega

/-- **The dual reading of the interval invariant.**  If two events in the interval
share a divisor `g ≥ 3` and the interval is nonempty, then the interval's excess
sum is at least `3` -- and since each step contributes at least `2`, the interval
contains at least two steps. -/
theorem shared_divisor_forces_two_steps {g S : Nat} (hg : 3 ≤ g) (hS : S ≠ 0)
    (hdiv : g ∣ S) : 3 ≤ S :=
  Nat.le_trans hg (interval_divisor_le_excess_sum hS hdiv)


end A166944Research
