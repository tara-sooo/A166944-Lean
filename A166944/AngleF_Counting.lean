import A166944.ConsecutiveEventGcd
import A166944.ExcessGap

set_option maxRecDepth 1000000

/-!
# Angle F: how many LARGE event values can a canonical replay have?

Target: `Σ e_i ≤ (3M-9)/8` (equivalently the relaxed index cap).  A plausible route
is "few events are large": if `e_i > 3M/16` for two indices, the sum overshoots, so
one would like to prove that at most one index is large.  This file does two things:

1. it makes precise the one **combinatorial** constraint the tree's consecutive-gcd
   theorem actually supplies (per-prime, not per-index); and
2. it **refutes the route arithmetically and empirically**.

## 1. What is proved here — new, kernel-checked

`ConsecutiveEventGcd.gcd_consecutive_dvd_three_unconditional` states that consecutive
event values share a divisor of `3`.  Its counting content, which the tree does not
state:

* `not_dvd_three_of_gt_three` — `3 < q` implies `¬ q ∣ 3`.
* `no_common_prime_gt_three_of_consecutive` — a `q > 3` divides **no** two
  consecutive event values; no parity hypothesis.
* `two_mul_tcount_le_of_noAdj` — a `Bool` list with no two adjacent `true`s has at
  most `(length+1)/2` of them.  Applied to the indicator of `{i : q ∣ e_i}`, a
  **single** prime `q > 3` divides at most `⌈p/2⌉` of the `p` event values.
* `tcount_le_half_of_noAdj` — the `⌈p/2⌉` form.

## 2. The route is arithmetically empty — proved, not merely observed

`heavy_count_ceiling_exceeds_allowance`: the strongest bound the route can give is
`Σ e_i ≤ M + (p-1)·(3M/16)` (all events are `≤ M` by `IsAttainedPreviousMaximum`,
and all but at most one are `≤ 3M/16`).  That ceiling is **above the budget**
`(3M-9)/8` for every `M ≥ 1`, because a single allowed event of size `M` already
exceeds the whole allowance (`max_event_exceeds_allowance`).  So **no** theorem of the
shape "at most `k` large events" with `k ≥ 1` can prove the cap, however large `p`
is and however small `t` is.  This is a defect of the *bound*, not of the data.

## 3. The route is also empirically the wrong way round — measured

Counting events with `16 e_i > 3M` over every canonical record below `2·10^6` whose
replay completes before the sweep horizon (17 records; `M = 1427749` is excluded
because `C_0 = 2M-2 > 2·10^6` truncates it):

| `M` | `p` | `#(16e > 3M)` | `Σe_i/((3M-9)/8)` |
| --- | --- | --- | --- |
| 3 | 0 | 0 | — |
| 7 | 0 | 0 | — |
| 13 | 4 | **4** | **7.333** |
| 43 | 6 | **1** | **4.000** |
| 139 | 2 | 0 | 0.745 |
| 313 | 6 | 0 | 0.362 |
| 661 | 0 | 0 | — |
| 1321 | 2 | 0 | 0.041 |
| 2659 | 11 | 0 | 0.114 |
| 5419 | 9 | 0 | 0.031 |
| 10891 | 11 | 0 | 0.066 |
| 22039 | 13 | 0 | 0.039 |
| 44383 | 7 | 0 | 0.003 |
| 88801 | 16 | 0 | 0.008 |
| 177841 | 3 | 0 | 0.001 |
| 355723 | 57 | 0 | 0.018 |
| 713833 | 11 | 0 | 0.000 |

For every `M ≥ 139` **no** event exceeds `3M/16`, so the hypothesis "at most one
`e_i > 3M/8`" is *vacuously true* above the threshold; and the only two records where
it fails are `M = 13` and `M = 43`, which are exactly the two where the cap fails.
The implication runs the other way: the cap forces the events small.

**The union over `q > 3` is not an independent set.**  The constraint of §1 is
per-prime.  Adjacent events may both carry *some* prime `> 3` provided the primes
differ: over the 14 complete replays with `M ≤ 3·10^5` there are **19** adjacent pairs
`(i, i+1)` where both `e_i`, `e_{i+1}` have a prime factor `> 3`, and **0** where they
share one.  Example at `M = 139`: `e_0 = 25 = 5²`, `e_1 = 13` — adjacent, `5 ≠ 13`.
So no bound on how many events are *large* follows from the gcd theorem.

**Scrambled control** (200 shuffles of the event multiset along each real replay's
`(s,C)` schedule, plus 200 draws of random odd `e ∈ [3,M]`): the "adjacent both have
a prime `> 3`" rate is `0.2500` real, `0.3845` shuffled, `0.9538` random, against an
independence prediction of `(65/69)² ≈ 0.887` at `M = 139`.  The real rate is *below*
both controls, so the real replays are *less* prone to adjacent large primes than
chance — the per-prime exclusion is real but the union statistic carries no
information.  Likewise `e² ≤ C` holds at every step for `M ≥ 313` (violated only at
`M = 13, 43, 139`), whereas random odd `e` violates it in `0.98` of steps.

Pure core (`decide` / `omega` / `simp` / `rfl`); no `norm_num`, `interval_cases`,
`positivity`, `nlinarith`, `linarith` or `ring`.
-/

namespace A166944Research

/-! ## Part 1: the per-prime exclusion -/

/-- **`3 < q` excludes `q ∣ 3`.** -/
theorem not_dvd_three_of_gt_three {q : Nat} (hq : 3 < q) : ¬ q ∣ 3 := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hk1 : 1 ≤ k := by omega
  have hmul : q * 1 ≤ q * k := Nat.mul_le_mul_left q hk1
  omega

/-- **A prime `q > 3` divides no two consecutive event values.**  Immediate from
`gcd_consecutive_dvd_three_unconditional`: a common divisor of `d r` and `d u` divides
their gcd, which divides `3`, but `3 < q`.  This is the counting content of the
tree's theorem; the tree states the gcd divisibility but not this consequence. -/
theorem no_common_prime_gt_three_of_consecutive {s C r C' u C'' q : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hnext : IsMovingHorizonStep r C' u C'')
    (hq : 3 < q) : ¬ (q ∣ d r ∧ q ∣ d u) := by
  rintro ⟨hqr, hqu⟩
  exact not_dvd_three_of_gt_three hq
    (Nat.dvd_trans (Nat.dvd_gcd hqr hqu)
      (gcd_consecutive_dvd_three_unconditional hstep hnext))

/-! ## Part 2: `⌈p/2⌉` occurrences per prime -/

/-- Number of `true` entries of a `Bool` list.  Local, so that recursion and
reduction behaviour are fully explicit (the core's `List.count` goes through `BEq`
and does not reduce definitionally in the needed way). -/
def tcount : List Bool → Nat
  | [] => 0
  | true :: l => 1 + tcount l
  | false :: l => tcount l

theorem tc_false (l : List Bool) : tcount (false :: l) = tcount l := rfl
theorem tc_true (l : List Bool) : tcount (true :: l) = 1 + tcount l := rfl
theorem len_cons (a : Bool) (l : List Bool) : (a :: l).length = l.length + 1 := rfl

/-- No two adjacent entries are both `true`. -/
def NoAdj : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => (a = false ∨ b = false) ∧ NoAdj (b :: l)

theorem noAdj_tail (b : Bool) (l : List Bool) (h : NoAdj (b :: l)) : NoAdj l := by
  cases l with
  | nil => trivial
  | cons c m => exact h.2

/-- **Counting lemma.**  A `Bool` list with no two adjacent `true`s has at most
`(length+1)/2` true entries: `2 * tcount l ≤ l.length + 1`. -/
theorem two_mul_tcount_le_of_noAdj : ∀ l : List Bool, NoAdj l → 2 * tcount l ≤ l.length + 1
  | [], _ => by simp [tcount]
  | [b], _ => by cases b <;> simp [tcount]
  | a :: b :: l, h => by
      have hna : NoAdj (b :: l) := h.2
      rcases h.1 with h1 | h1
      · subst h1
        have hrec := two_mul_tcount_le_of_noAdj (b :: l) hna
        simp only [tc_false, len_cons] at hrec ⊢
        omega
      · subst h1
        have hl : NoAdj l := noAdj_tail false l hna
        have hrec := two_mul_tcount_le_of_noAdj l hl
        cases a with
        | false =>
            simp only [tc_false, len_cons] at hrec ⊢
            omega
        | true =>
            simp only [tc_true, tc_false, len_cons] at hrec ⊢
            omega

/-- **The `⌈p/2⌉` form.**  A single prime `q > 3` divides at most `(p+1)/2` of the
`p` event values. -/
theorem tcount_le_half_of_noAdj (l : List Bool) (h : NoAdj l) :
    tcount l ≤ (l.length + 1) / 2 := by
  have h2 := two_mul_tcount_le_of_noAdj l h
  omega

/-! ## Part 3: the counting route's ceiling is above the budget -/

/-- **One event at the maximum already exhausts the allowance.**  `(3M-9)/8 < M`
for every `M ≥ 1`. -/
theorem max_event_exceeds_allowance {M : Nat} (hM : 1 ≤ M) :
    (3 * M - 9) / 8 < M := by
  have h3 : 3 * M < 8 * M := by omega
  have h4 : (3 * M) / 8 < M := by omega
  have h1 : (3 * M - 9) / 8 ≤ (3 * M) / 8 :=
    Nat.div_le_div_right (Nat.sub_le (3 * M) 9)
  omega

/-- **The counting route's ceiling exceeds the budget.**  If at most one event exceeds
`3M/16`, then `Σ e_i ≤ M + (p-1)·(3M/16)`: the exceptional event is at most `M` by
`IsAttainedPreviousMaximum` and the rest are at most `3M/16`.  That ceiling is
already above `(3M-9)/8`, because one allowed event of size `M` exceeds the whole
allowance.  Hence **no** bound of the shape "at most `k ≥ 1` large events" can prove
the cap -- the defect is in the bound, not in the data. -/
theorem heavy_count_ceiling_exceeds_allowance (p M : Nat) (hM : 1 ≤ M) :
    (3 * M - 9) / 8 < M + (p - 1) * (3 * M / 16) := by
  have h1 := max_event_exceeds_allowance hM
  have h2 : M ≤ M + (p - 1) * (3 * M / 16) := Nat.le_add_right M _
  omega

/-! ## Part 4: `#check` of every cited statement, and the axiom audit

`#check` is mandatory here: it pins the exact statement of each theorem relied on, so
that the use above is visibly of the intended theorem and not of a name-alike. -/

#check @gcd_consecutive_dvd_three_unconditional
#check @moving_horizon_step_event_package
#check @moving_horizon_step_event_ge_three
#check @a_le_three_mul
#check @two_mul_count_le_excess
#check @not_dvd_three_of_gt_three
#check @no_common_prime_gt_three_of_consecutive
#check @two_mul_tcount_le_of_noAdj
#check @tcount_le_half_of_noAdj
#check @max_event_exceeds_allowance
#check @heavy_count_ceiling_exceeds_allowance

-- `#print axioms`: the environment has no `sorryAx`.  Every theorem below depends
-- only on `propext` and `Quot.sound`, both of which are axioms of the Lean kernel's
-- logic and not of this development.
#print axioms not_dvd_three_of_gt_three
#print axioms no_common_prime_gt_three_of_consecutive
#print axioms two_mul_tcount_le_of_noAdj
#print axioms tcount_le_half_of_noAdj
#print axioms max_event_exceeds_allowance
#print axioms heavy_count_ceiling_exceeds_allowance

end A166944Research
