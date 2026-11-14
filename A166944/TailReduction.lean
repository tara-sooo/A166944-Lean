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

/-- Core reduction: adding a multiple leaves the gcd unchanged. -/
theorem gcd_add_eq_gcd_self {A X : Nat} : Nat.gcd A (A + X) = Nat.gcd A X := by
  rw [Nat.add_comm A X]
  exact Nat.gcd_add_self_right A X

/-- Abstract even-tail reduction. `S` is the canonical state index `delta*c`
    and `d` is `2*delta`; the second argument is `C - 1`. -/
theorem gcd_of_split_even {S d k : Nat} (hd : 1 ≤ d) (hk : k ≤ d - 1) :
    Nat.gcd (S + k) (S + d - 1) = Nat.gcd (S + k) (d - 1 - k) := by
  have hsum : k + (d - 1 - k) = d - 1 := by omega
  have h1 : (S + k) + (d - 1 - k) = S + d - 1 := by
    rw [Nat.add_assoc, hsum, Nat.add_sub_assoc hd S]
  rw [← h1]
  exact gcd_add_eq_gcd_self

/-- Abstract odd-tail reduction, in terms of `j - 2`; the second argument
    is `C + 1` and `d + 3` is `2*delta + 3`. -/
theorem gcd_of_split_odd {S d k : Nat} (hk2 : 2 ≤ k) (hk : k ≤ d + 3) :
    Nat.gcd (S + k - 2) (S + d + 1) = Nat.gcd (S + k - 2) (d + 3 - k) := by
  have hk2' : S + k - 2 = S + (k - 2) := Nat.add_sub_assoc hk2 S
  have hsum : (k - 2) + (d + 3 - k) = d + 1 := by omega
  have h1 : (S + k - 2) + (d + 3 - k) = S + d + 1 := by
    rw [hk2', Nat.add_assoc, hsum]
    omega
  rw [← h1]
  exact gcd_add_eq_gcd_self

/-- Canonical even-tail reduction: at state index `s + k` the horizon term
    `C - 1` reduces to the `c`-free number `2*delta - 1 - k`. -/
theorem canonical_even_tail_gcd_reduction {delta c k : Nat} (hd : 1 ≤ delta)
    (hk : k ≤ 2 * delta - 1) :
    Nat.gcd (delta * c + k) (delta * (c + 2) - 1) =
      Nat.gcd (delta * c + k) (2 * delta - 1 - k) := by
  have hexp : delta * (c + 2) = delta * c + 2 * delta := by
    rw [Nat.mul_add, Nat.mul_comm delta 2]
  have hd2 : 1 ≤ 2 * delta := by omega
  rw [hexp]
  exact gcd_of_split_even (S := delta * c) (d := 2 * delta) (k := k) hd2 hk

/-- Canonical odd-tail reduction: at state index `s + k` the horizon term
    `C + 1` reduces to the `c`-free number `2*delta + 3 - k`. -/
theorem canonical_odd_tail_gcd_reduction {delta c k : Nat} (hk2 : 2 ≤ k)
    (hk : k ≤ 2 * delta + 3) :
    Nat.gcd (delta * c + k - 2) (delta * (c + 2) + 1) =
      Nat.gcd (delta * c + k - 2) (2 * delta + 3 - k) := by
  have hexp : delta * (c + 2) = delta * c + 2 * delta := by
    rw [Nat.mul_add, Nat.mul_comm delta 2]
  rw [hexp]
  exact gcd_of_split_odd (S := delta * c) (d := 2 * delta) (k := k) hk2 hk

/-- At a canonical state the even-tail event divides the `c`-free number
    `2*delta - 1 - (r - s)`; in the intermediate band this is the hard bound. -/
theorem canonical_even_tail_event_dvd_bounded {delta c k e : Nat} (hd : 1 ≤ delta)
    (hk : k ≤ 2 * delta - 1)
    (he : e = Nat.gcd (delta * c + k) (delta * (c + 2) - 1)) :
    e ∣ 2 * delta - 1 - k := by
  rw [he, canonical_even_tail_gcd_reduction hd hk]
  exact Nat.gcd_dvd_right _ _

/-- **The canonical addition theorem (even branch).** At the canonical
critical state, an even-tail unit run of length `k` followed by a *proper*
event of value `e` satisfies `k + e ≤ 2 * delta - 1`. The run plus its event
is bounded by twice the previous record, independently of `c`. -/
theorem canonical_even_tail_additive_bound {delta c k e : Nat} (hd : 1 ≤ delta)
    (hk : k ≤ 2 * delta - 1)
    (he : e = Nat.gcd (delta * c + k) (delta * (c + 2) - 1))
    (hlt : e < delta * (c + 2) - 1) :
    k + e ≤ 2 * delta - 1 := by
  have hkne : k ≠ 2 * delta - 1 := by
    intro hk'
    have hself : delta * c + k = delta * (c + 2) - 1 := by
      have hexp : delta * (c + 2) = delta * c + 2 * delta := by
        rw [Nat.mul_add, Nat.mul_comm delta 2]
      omega
    rw [he, hself, Nat.gcd_self] at hlt
    omega
  have hDpos : 0 < 2 * delta - 1 - k := by omega
  have hdiv := canonical_even_tail_event_dvd_bounded (c := c) hd hk he
  have hle : e ≤ 2 * delta - 1 - k := Nat.le_of_dvd hDpos hdiv
  have hsum : k + (2 * delta - 1 - k) = 2 * delta - 1 := Nat.add_sub_of_le hk
  omega

/-- **Slack corollary.** The even unit tail before a canonical proper event
is at most `2 * delta - 2` long. -/
theorem canonical_even_tail_run_le {delta c k e : Nat} (hd : 1 ≤ delta)
    (hk : k ≤ 2 * delta - 1)
    (he : e = Nat.gcd (delta * c + k) (delta * (c + 2) - 1))
    (hlt : e < delta * (c + 2) - 1) :
    k ≤ 2 * delta - 2 := by
  have h := canonical_even_tail_additive_bound hd hk he hlt
  have hepos : 0 < e := by
    rw [he]
    exact Nat.gcd_pos_of_pos_right _
      (by have := Nat.mul_pos hd (show 0 < c + 2 by omega); omega)
  have hone : k + 1 ≤ 2 * delta - 1 :=
    Nat.le_trans (Nat.add_le_add_left hepos k) h
  have hcancel : (2 * delta - 1) + 1 = 2 * delta := Nat.sub_add_cancel (by omega)
  omega

end A166944Research
