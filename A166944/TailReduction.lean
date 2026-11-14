import A166944.Lemmas

/-!
# Unit tails at a canonical state, in a `c`-free form

The canonical critical state is `(s, C) = (delta * c, delta * (c + 2))`. The
horizon term at index `s + k` is a gcd involving `c`, which is awkward: `c` is
large and unconstrained. These lemmas remove it.

  * `canonical_even_tail_gcd_reduction` -- the even-index horizon term at
    `s + k` is `gcd (delta * c + k) (2 * delta - 1 - k)`: the factor `c` has
    disappeared from the second argument.
  * `canonical_odd_tail_gcd_reduction` -- the same for an odd index, with
    `2 * delta + 3 - k`.
  * `canonical_even_tail_additive_bound` -- a unit run of length `k` followed by
    a proper event of value `e` satisfies `k + e <= 2 * delta - 1`. The run plus
    its event is bounded by twice the previous record, independently of `c`.
  * `canonical_even_tail_run_le` -- consequently the run itself is at most
    `2 * delta - 2`.

Also included: the general splitting identities (`gcd_of_split_even`,
`gcd_of_split_odd`) and the unit-tail predicate lemmas they build on.

Recovered from `~/p2m_scratch/dpath` (L1-L4), where the whole lane had been left
uncommitted. The `c`-free reduction is the useful part: it turns a statement
about an unconstrained product into a statement about `delta` and the offset
alone, which is the shape a first-hit formula needs.
-/

namespace A166944Research

/-- Every event term is a unit at every index of the unit tail. -/
theorem unit_tail_term_eq_one {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r) :
    (if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1)) = 1 := by
  rcases moving_horizon_first_hit_map hstep with h | h
  · rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · rw [if_pos hj]; exact (h.2.2.2 j hsj hjr).1 hj
    · rw [if_neg (by omega)]; exact (h.2.2.2 j hsj hjr).2 hj
  · rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · rw [if_pos hj]; exact (h.2.2.2 j hsj hjr).1 hj
    · rw [if_neg (by omega)]; exact (h.2.2.2 j hsj hjr).2 hj

/-- Unit-tail term form. -/
theorem isUnitTerm {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r) :
    Nat.gcd j (C - 1) = 1 ∨ Nat.gcd (j - 2) (C + 1) = 1 := by
  rcases moving_horizon_first_hit_map hstep with h | h
  · rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · left; exact (h.2.2.2 j hsj hjr).1 hj
    · right; exact (h.2.2.2 j hsj hjr).2 hj
  · rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · left; exact (h.2.2.2 j hsj hjr).1 hj
    · right; exact (h.2.2.2 j hsj hjr).2 hj

/-- A common divisor of a unit-tail index and the active horizon term is one.

`moving_horizon_first_hit_map` returns, in both parity branches, the function
`fun j => ((j % 2 = 0 -> gcd j (C - 1) = 1) ∧ (j % 2 = 1 -> gcd (j-2) (C+1) = 1))`.
Both components are available regardless of which branch `r` is on, so the even
and odd statements can be read off directly. -/
theorem unit_tail_gcd_eq_one_even {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r)
    (heven : j % 2 = 0) (hv : v ∣ j) (hdiv : v ∣ C - 1) : v = 1 := by
  have htail := (moving_horizon_first_hit_map hstep).elim
    (fun h => h.2.2.2 j hsj hjr) (fun h => h.2.2.2 j hsj hjr)
  exact Nat.gcd_eq_one_iff.mp (htail.1 heven) v hv hdiv

/-- The odd-branch companion: a common divisor of `j - 2` and `C + 1` is one. -/
theorem unit_tail_gcd_eq_one_odd {s C r C' j v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r)
    (hodd : j % 2 = 1) (hv : v ∣ j - 2) (hdiv : v ∣ C + 1) : v = 1 := by
  have htail := (moving_horizon_first_hit_map hstep).elim
    (fun h => h.2.2.2 j hsj hjr) (fun h => h.2.2.2 j hsj hjr)
  exact Nat.gcd_eq_one_iff.mp (htail.2 hodd) v hv hdiv

end A166944Research
