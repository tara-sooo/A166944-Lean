import A166944.Lemmas

namespace A166944Research

/-! ## A. `t = 2` forces `3 ∣ delta` -/

/-- At a critical record the q = 3 slack identity is
`2 * delta = t + 1 + 3 * e`.  In the smallest-gap sub-case `t = 2` this
reads `2 * delta = 3 * (e + 1)`, so the critical increment is a multiple
of three. -/
theorem critical_q3_gap_two_mult_three {delta e : Nat}
    (hslack : 2 * delta = 2 + 1 + 3 * e) : 3 ∣ delta := by
  have hmod : delta % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hmod

/-- Consequently, in the gap-two sub-case the post-record increment is not
divisible by three. -/
theorem critical_q3_gap_two_not_three_dvd_event {delta e : Nat}
    (hslack : 2 * delta = 2 + 1 + 3 * e) (hcop : Nat.gcd delta e = 1) :
    ¬ 3 ∣ e := by
  intro h3
  have hd3 : 3 ∣ delta := critical_q3_gap_two_mult_three hslack
  have hg : 3 ∣ Nat.gcd delta e := Nat.dvd_gcd hd3 h3
  rw [hcop] at hg
  omega

/-! ## B. Integrality barrier: `delta` never divides the post-record index -/

/-- The post-record first hit sits at index `delta * c + t` with `t < delta`.
Hence `delta` does **not** divide that index.  Equivalently: the increment
that fired at the critical record cannot divide the next event index. -/
theorem critical_q3_index_not_dvd_delta
    {delta c t : Nat} (ht1 : 1 ≤ t) (ht : t < delta) :
    ¬ delta ∣ delta * c + t := by
  intro h
  have hdc : delta ∣ delta * c := Nat.dvd_mul_right delta c
  have hdt : delta ∣ t := by
    have hsub := Nat.dvd_sub h hdc
    have hval : delta * c + t - delta * c = t := by omega
    rwa [hval] at hsub
  have htpos : 0 < t := by omega
  exact absurd (Nat.le_of_dvd htpos hdt) (by omega)

/-! ## C. The exact "closure" identity for the *next* horizon -/

/-- The q = 3 slack identity is exactly the statement that the next slack
grows by `t + 4 * e`; the next critical predecessor form would need
`delta ∣ e - 1`, which the intermediate band forbids unless `e = 1`. -/
theorem critical_q3_closure_not_divides
    {delta e t : Nat} (he : 1 < e) (hed : e < delta)
    (hslack : 2 * delta = t + 1 + 3 * e) :
    ¬ delta ∣ e - 1 := by
  intro h
  have hlt : e - 1 < delta := by omega
  rcases Nat.eq_zero_or_pos (e - 1) with hz | hp
  · omega
  · exact absurd (Nat.le_of_dvd hp h) (by omega)

/-! ## D. Cofactor gap: `v - u = 3` is forced, and `3 ∤ e` -/

/-- From the two q = 3 post-step identities together with the slack identity
the cofactor gap is exactly three. -/
theorem critical_q3_cofactor_gap
    {delta c e v u t : Nat}
    (hpost₁ : e * u = delta * c + t)
    (hpost₂ : e * v + 1 = delta * (c + 2))
    (hslack : 2 * delta = t + 1 + 3 * e)
    (hepos : 0 < e) :
    v = u + 3 := by
  have hexp : delta * (c + 2) = delta * c + 2 * delta := by
    rw [Nat.mul_add]
    omega
  have hkey : e * v = e * u + 3 * e := by
    rw [hexp] at hpost₂
    omega
  have hfac : e * v = e * (u + 3) := by
    rw [hkey, Nat.mul_add]
    omega
  exact Nat.mul_left_cancel hepos hfac

/-- Hence the smaller cofactor is coprime to three. -/
theorem critical_q3_cofactor_not_three
    {delta c e v u t : Nat}
    (hpost₁ : e * u = delta * c + t)
    (hpost₂ : e * v + 1 = delta * (c + 2))
    (hslack : 2 * delta = t + 1 + 3 * e)
    (hepos : 0 < e) (hcop : Nat.gcd u v = 1) :
    ¬ 3 ∣ u := by
  have hv : v = u + 3 :=
    critical_q3_cofactor_gap hpost₁ hpost₂ hslack hepos
  intro h3
  have h3v : 3 ∣ v := by rw [hv]; omega
  have hg : 3 ∣ Nat.gcd u v := Nat.dvd_gcd h3 h3v
  rw [hcop] at hg
  omega

end A166944Research

/-!
# Barriers on the `q = 3` branch

Elementary consequences of the `q = 3` slack normal form

  2 * delta = t + 1 + 3 * e

They are tools, not an elimination: the local system still admits survivors
(see the notes in the PR description). The useful content is that `t = 2`
forces `3 ∣ delta`, that the post-event index is never divisible by `delta`,
and that the cofactor gap is exactly three.
-/
