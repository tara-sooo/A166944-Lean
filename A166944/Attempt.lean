import A166944.ResearchDefs
import A166944.Lemmas

/-!
# A166944 active proof attempt

This file stays on the lightweight recurrence path. The reusable Milestone 3
proofs live in `Lemmas.lean`; these examples keep their public names
kernel-checked here. The history-bounded envelope remains unproved.
-/

namespace A166944Research

example {m : Nat} (hm : 2 ≤ m) :
    B m = 2 ↔ a m = 2 * m := fundamental_point_iff hm

example {l t : Nat} (hl : 2 ≤ l)
    (hone : ∀ j : Nat, l < j → j ≤ l + t → d j = 1) :
    D (l + t) = D l ∧ B (l + t) + t = B l :=
  one_interval_const_D_B hl hone

example {rho m : Nat} (hrho : 2 ≤ rho) (hbelow : rho < m)
    (hfund : B m = 2)
    (hone : ∀ j : Nat, rho < j → j ≤ m → d j = 1) :
    ∃ t : Nat, 0 < t ∧ m = rho + t ∧ D m = D rho ∧ B rho = 2 + t :=
  last_nontrivial_telescope hrho hbelow hfund hone

example {k : Nat} (hk : 2 ≤ k) (hB : B k = 2) :
    d (k + 1) = 1 ∧ B (k + 1) = 1 := B_two_transition hk hB

example {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1) (hB : B k = 1) :
    (d (k + 1) = 1 ∧ B (k + 1) = 0) ∨
      (d (k + 1) = 3 ∧ B (k + 1) = 2) :=
  B_one_transition hk hk1 hB

example {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1) (hB : B k = 3) :
    d (k + 1) = 1 ∧ B (k + 1) = 2 := B_three_transition hk hk1 hB

example {k : Nat} (hk : 2 ≤ k) (hB : B k = 0) :
    d (k + 1) = k - 1 ∧ B (k + 1) + 2 = k - 1 :=
  B_zero_transition hk hB

example {k M m : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hbelow : k + 1 < m) (hfund : B m = 2)
    (hone : ∀ j : Nat, k + 1 < j → j ≤ m → d j = 1) :
    m = k + 1 + 2 * d (k + 1) :=
  odd_failure_fundamental_distance hk hIH hnew hfail hbelow hfund hone

example {k M m : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hrho : IsLastNontrivialBefore (k + 1) m) (hfund : B m = 2) :
    m = k + 1 + 2 * d (k + 1) :=
  odd_failure_distance_of_last_nontrivial hk hIH hnew hfail hrho hfund

example {k m rho : Nat} (hcrit : 1 < d (k + 1))
    (hbelow : k + 1 < m)
    (hrho : IsLastNontrivialBefore rho m) :
    k + 1 ≤ rho :=
  critical_index_le_last_nontrivial hcrit hbelow hrho

example {k M m rho : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hcrit : 1 < d (k + 1)) (hbelow : k + 1 < m)
    (hfund : B m = 2) (hrho : IsLastNontrivialBefore rho m) :
    m = k + 1 + 2 * d (k + 1) ∨ k + 1 < rho :=
  odd_failure_distance_or_later_nontrivial hk hIH hnew hfail hcrit hbelow hfund hrho

example {m : Nat} (hm : d m = 1)
    (hex : ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q) :
    ∃ rho : Nat, IsLastNontrivialBefore rho m :=
  exists_last_nontrivial_before hm hex

example {m : Nat} :
    (∃ rho : Nat, IsLastNontrivialBefore rho m) ↔
      (d m = 1 ∧ ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q) :=
  exists_last_nontrivial_before_iff

example {rho sigma m : Nat}
    (hrho : IsLastNontrivialBefore rho m)
    (hsigma : IsLastNontrivialBefore sigma m) :
    rho = sigma := last_nontrivial_before_unique hrho hsigma

example {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    3 * rho ≤ 2 * m ↔ m + 6 ≤ 3 * B rho :=
  rho_bound_iff_B_bound hrho hfund

example {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    B rho + rho = m + 2 :=
  last_nontrivial_telescope_addition hrho hfund

example {rho m : Nat}
    (hrho : IsLastNontrivialBefore rho m) (hfund : B m = 2) :
    3 ≤ B rho ∧ B rho ≤ m :=
  last_nontrivial_B_bounds hrho hfund

example {k m rho : Nat} (hk : 2 ≤ k) (hlater : k + 1 < rho)
    (hrho : IsLastNontrivialBefore rho m) :
    3 ≤ d rho ∧ B rho + 2 = B (rho - 1) + d rho ∧
      ((rho % 2 = 0 ∧
          ((B (rho - 1) = 1 ∧ d rho = 3) ∨
            (4 ≤ B (rho - 1) ∧
              ∃ t : Nat, B (rho - 1) - 4 = d rho * t ∧
                t % 2 = 1 ∧ d rho + 4 ≤ B (rho - 1)))) ∨
        (rho % 2 = 1 ∧
          ∃ t : Nat, B (rho - 1) = d rho * t ∧
            t % 2 = 0 ∧
            (B (rho - 1) = 0 ∨ 2 * d rho ≤ B (rho - 1)))) :=
  later_nontrivial_residual_transport hk hlater hrho

example {n : Nat} (hn : 2 ≤ n) : B n + n = D n + 2 :=
  B_add_index_eq_D_add_two hn

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    k % 2 = 1 ∧ 4 ≤ B k ∧ B k = d (k + 1) + 4 ∧
      B (k + 1) + 2 = 2 * d (k + 1) + 4 ∧
      d (k + 1) + 6 ≤ 2 * M :=
  new_max_failure_reduction hk hIH hnew hfail

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    B (k + 1) = 2 * d (k + 1) + 2 :=
  new_max_failure_next_B_eq hk hIH hnew hfail

example {k M m rho : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hlater : k + 1 < rho) (hrho : IsLastNontrivialBefore rho m) :
    2 * d (k + 1) + k + 3 < B rho + rho :=
  critical_later_strict_transport hk hIH hnew hfail hlater hrho

example {k M m rho : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hbelow : k + 1 < m) (hfund : B m = 2)
    (hrho : IsLastNontrivialBefore rho m) (hlater : k + 1 < rho) :
    k + 1 + 2 * d (k + 1) < m :=
  critical_later_distance_strict hk hIH hnew hfail hbelow hfund hrho hlater

example {n : Nat} : D (n + 1) = D n + (d (n + 1) - 1) := by
  rw [D_succ_eq_add_d_sub_one n]
  exact Nat.add_sub_assoc (one_le_d_succ n) (D n)

example {start finish s : Nat} (hstart : 2 ≤ start)
    (hchain : HasNontrivialChain start finish s) :
    D start + 2 * s ≤ D finish :=
  D_growth_of_nontrivial_chain hstart hchain

example {m : Nat} (hm : 2 ≤ m) (hfund : B m = 2) :
    D m = m := D_eq_self_of_fundamental hm hfund

example {k M m s : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hbelow : k + 1 < m) (hfund : B m = 2)
    (hchain : HasNontrivialChain (k + 1) m s) :
    k + 1 + 2 * d (k + 1) + 2 * s ≤ m :=
  critical_endpoint_lower_bound hk hIH hnew hfail hbelow hfund hchain

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    9 ≤ d (k + 1) := critical_new_increment_lower_bound hk hIH hnew hfail

example : ¬ D 0 + 2 ≤ D 1 := by decide

example : ¬ D 1 + 2 ≤ D 2 := by decide

example : HasNontrivialChain 2 5 1 := by
  refine ⟨5, by decide, by decide, by decide, ?_⟩
  simp [HasNontrivialChain]

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∃ c : Nat, k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      a k = d (k + 1) * (2 * c + 1) ∧
      D (k + 1) = d (k + 1) * (c + 2) ∧
      (2 * c + 1) % 2 = 1 ∧ Nat.gcd c (2 * c + 1) = 1 :=
  critical_even_quotient_normal_form hk hIH hnew hfail

example {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hsep : 2 * P ≤ d (k + 1) + 1) : False :=
  critical_failure_impossible_of_separation hk hIH hnew hfail hsep

example {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) (hPsmall : P ≤ 5) : False :=
  critical_failure_impossible_of_small_previous_max hk hIH hnew hfail hPsmall

example {P k : Nat} (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      ∀ j : Nat, 2 ≤ j → j < r → d j < P :=
  attained_previous_maximum_first_occurrence hP

example {P k : Nat} (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧ IsDifferenceRecord P :=
  attained_previous_maximum_record hP

example {P k : Nat} (hP : IsAttainedPreviousMaximum P k) (hP5 : 5 < P) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      ((r % 2 = 0 ∧
          ∃ c q : Nat, r = P * c ∧ a (r - 1) = P * q ∧
            c % 2 = 0 ∧ q % 2 = 1 ∧ Nat.gcd c q = 1 ∧ 2 ≤ c) ∨
        (r % 2 = 1 ∧
          ∃ c q : Nat, r - 2 = P * c ∧ a (r - 1) = P * q ∧
            c % 2 = 1 ∧ q % 2 = 0 ∧ Nat.gcd c q = 1 ∧
            1 ≤ c ∧ (c = 1 ∨ 3 ≤ c))) := by
  exact attained_previous_maximum_quotient_structure hP hP5

example {k M : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∃ p c u v : Nat,
      2 ≤ p ∧ p ≤ k ∧ d p = M ∧
      (∀ j : Nat, 2 ≤ j → j < p → d j < M) ∧
      5 < M ∧
      (p = M + 2 ∨
        (M + 2 < p ∧ d (M + 2) < M ∧
          d (M + 2) = Nat.gcd M (a (M + 1)) ∧
          Nat.gcd M (a (M + 1)) < M ∧ ¬ M ∣ a (M + 1))) ∧
      ((p % 2 = 0 ∧ p = M * u ∧ a (p - 1) = M * v ∧
          u % 2 = 0 ∧ v % 2 = 1 ∧ Nat.gcd u v = 1 ∧ 2 ≤ u) ∨
        (p % 2 = 1 ∧ p - 2 = M * u ∧ a (p - 1) = M * v ∧
          u % 2 = 1 ∧ v % 2 = 0 ∧ Nat.gcd u v = 1 ∧
          1 ≤ u ∧ (u = 1 ∨ 3 ≤ u))) ∧
      k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      a k = d (k + 1) * (2 * c + 1) ∧
      D (k + 1) = d (k + 1) * (c + 2) :=
  critical_previous_maximum_prefix hk hP hIH hnew hfail

example {R n s : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R)
    (hns : n < s) (henv : HasHistoryEnvelopeBefore s) :
    n = R + 2 :=
  record_index_eq_of_history_envelope_before hR hn hd hprior hns henv

example {R n s : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R)
    (hns : n < s) (henv : HasHistoryEnvelopeBefore s) :
    n = R + 2 ∧ a (R + 1) = 2 * R :=
  canonical_record_value_of_history_envelope_before hR hn hd hprior hns henv

example {R n s : Nat} (hR : 5 < R) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R)
    (hns : n < s) (henv : HasHistoryEnvelopeBefore s) :
    B n + 2 = R :=
  canonical_record_excess_eq_of_history_envelope_before hR hn hd hprior hns henv

example {k M : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (henv : HasHistoryEnvelopeBefore (k + 1)) :
    ∃ p c : Nat,
      2 ≤ p ∧ p ≤ k ∧ d p = M ∧
      (∀ j : Nat, 2 ≤ j → j < p → d j < M) ∧
      5 < M ∧ p = M + 2 ∧ a (M + 1) = 2 * M ∧
      B p + 2 = M ∧ D p + p = M * 3 ∧ D p = 2 * M - 2 ∧
      k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      a k = d (k + 1) * (2 * c + 1) ∧
      D (k + 1) = d (k + 1) * (c + 2) :=
  critical_previous_maximum_canonical hk hP hIH hnew hfail henv

example {r C : Nat} (hr : 2 ≤ r) (hD : D (r - 1) = C) :
    d r = if r % 2 = 0 then Nat.gcd r (C - 1)
      else Nat.gcd (r - 2) (C + 1) :=
  constant_D_event_map hr hD

example {s C : Nat} (hs : 1 ≤ s) (hD : D s = C) :
    d (s + 1) = if (s + 1) % 2 = 0 then Nat.gcd (s + 1) (C - 1)
      else Nat.gcd (s - 1) (C + 1) := by
  have hr : 2 ≤ s + 1 := Nat.succ_le_succ hs
  have hpred : s + 1 - 1 = s := Nat.add_sub_cancel s 1
  have hpred2 : s + 1 - 2 = s - 1 := by
    cases s with
    | zero => simp at hs
    | succ s => simp [Nat.add_assoc]
  simpa [hpred, hpred2] using constant_D_event_map hr (by simpa [hpred] using hD)

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (heven : r % 2 = 0) :
    d r < C - 1 ↔ ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hqpos : 0 < C - 1 := by
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right r hqpos)
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (hodd : r % 2 ≠ 0) :
    d r < C + 1 ↔ ¬ (C + 1) ∣ r - 2 := by
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right (r - 2) (by simp))
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

example {x q : Nat} (hxodd : x % 2 = 1) (hqodd : q % 2 = 1)
    (hxgt : 1 < x) (hdiv : x ∣ q) (hproper : x < q) :
    3 * x ≤ q := by
  rcases hdiv with ⟨t, ht⟩
  have htodd : t % 2 = 1 := by
    calc
      t % 2 = (x * t) % 2 := quotient_mod_two_of_left_odd hxodd
      _ = q % 2 := by rw [ht]
      _ = 1 := hqodd
  rcases one_or_three_le_of_mod_two_eq_one htodd with ht1 | ht3
  · have heq : q = x := by
      calc
        q = x * t := ht
        _ = x := by rw [ht1]; simp
    have : x < x := by simpa [heq] using hproper
    exact False.elim (Nat.lt_irrefl x this)
  · calc
      3 * x = x * 3 := by simp [Nat.mul_comm]
      _ ≤ x * t := Nat.mul_le_mul_left x ht3
      _ = q := ht.symm

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (heven : r % 2 = 0) (hnontriv : 1 < d r)
    (hproper : d r < C - 1) :
    3 * d r ≤ C - 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hCstep : C - 1 + 1 = C := Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
  have hqmod : (C - 1) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdiv : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  rcases hdiv with ⟨t, ht⟩
  have htmod : t % 2 = 1 := by
    calc
      t % 2 = (d r * t) % 2 := quotient_mod_two_of_left_odd hdmod
      _ = (C - 1) % 2 := by rw [ht]
      _ = 1 := hqmod
  rcases one_or_three_le_of_mod_two_eq_one htmod with ht1 | ht3
  · have heq : C - 1 = d r := by
      calc
        C - 1 = d r * t := ht
        _ = d r := by rw [ht1]; simp
    have : d r < d r := by simpa [heq] using hproper
    exact False.elim (Nat.lt_irrefl _ this)
  · calc
      3 * d r = d r * 3 := by simp [Nat.mul_comm]
      _ ≤ d r * t := Nat.mul_le_mul_left _ ht3
      _ = C - 1 := ht.symm

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (hodd : r % 2 ≠ 0) (hnontriv : 1 < d r)
    (hproper : d r < C + 1) :
    3 * d r ≤ C + 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hqmod : (C + 1) % 2 = 1 := by simp [Nat.add_mod, hCmod]
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  have hdiv : d r ∣ C + 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  rcases hdiv with ⟨t, ht⟩
  have htmod : t % 2 = 1 := by
    calc
      t % 2 = (d r * t) % 2 := quotient_mod_two_of_left_odd hdmod
      _ = (C + 1) % 2 := by rw [ht]
      _ = 1 := hqmod
  rcases one_or_three_le_of_mod_two_eq_one htmod with ht1 | ht3
  · have heq : C + 1 = d r := by
      calc
        C + 1 = d r * t := ht
        _ = d r := by rw [ht1]; simp
    have : d r < d r := by simpa [heq] using hproper
    exact False.elim (Nat.lt_irrefl _ this)
  · calc
      3 * d r = d r * 3 := by simp [Nat.mul_comm]
      _ ≤ d r * t := Nat.mul_le_mul_left _ ht3
      _ = C + 1 := ht.symm

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (heven : r % 2 = 0) (hle : r ≤ C) (hnontriv : 1 < d r) :
    ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hCpos : 0 < C - 1 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdvd : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hdle : d r ≤ C - 1 := Nat.le_of_dvd hCpos hdvd
  have hd2 : 2 ≤ d r := Nat.succ_le_of_lt hnontriv
  have hq2 : 2 ≤ C - 1 := Nat.le_trans hd2 hdle
  have hqodd : (C - 1) % 2 = 1 := by
    have hCstep : C - 1 + 1 = C := Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  intro hdiv
  have hqle : C - 1 ≤ r := Nat.le_of_dvd (Nat.lt_of_lt_of_le (by simp) hr) hdiv
  have hupper : r ≤ (C - 1) + 1 := by
    calc
      r ≤ C := hle
      _ = (C - 1) + 1 := (Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)).symm
  rcases Nat.lt_or_eq_of_le hqle with hlt | heq
  · have hreq : r = (C - 1) + 1 :=
      Nat.le_antisymm hupper (Nat.succ_le_of_lt hlt)
    have hone : C - 1 ∣ 1 := by
      have hsub := Nat.dvd_sub hdiv (Nat.dvd_refl (C - 1))
      rw [hreq] at hsub
      simpa [Nat.add_sub_cancel_left] using hsub
    have hqone : C - 1 = 1 := Nat.eq_one_of_dvd_one hone
    have : (2 : Nat) ≤ 1 := by simpa [hqone] using hq2
    simp at this
  · have hbad : (1 : Nat) = 0 := by
      calc
        1 = (C - 1) % 2 := hqodd.symm
        _ = r % 2 := by rw [heq]
        _ = 0 := heven
    cases hbad

example {r C : Nat} (hr : 3 ≤ r) (hle : r ≤ C) :
    ¬ (C + 1) ∣ r - 2 := by
  intro hdiv
  have hr2 : 0 < r - 2 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hr)
  have hqle : C + 1 ≤ r - 2 := Nat.le_of_dvd hr2 hdiv
  have hbad : C + 1 ≤ C :=
    Nat.le_trans hqle (Nat.le_trans (Nat.sub_le r 2) hle)
  exact (Nat.not_succ_le_self C) hbad

example {delta c r : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = delta * (c + 2)) :
    Nat.gcd delta (d r) = 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hC2 : 2 ≤ delta * (c + 2) := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hCpos : 1 ≤ delta * (c + 2) := Nat.le_trans (by simp) hC2
  by_cases heven : r % 2 = 0
  · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
    rw [if_pos heven] at hmap
    have hdvd : d r ∣ delta * (c + 2) - 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    let g := Nat.gcd delta (d r)
    have hgdelta : g ∣ delta := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d r := Nat.gcd_dvd_right _ _
    have hgq : g ∣ delta * (c + 2) - 1 := Nat.dvd_trans hgd hdvd
    have hgC : g ∣ delta * (c + 2) :=
      Nat.dvd_mul_right_of_dvd hgdelta (c + 2)
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hgC hgq
      have hdiff : delta * (c + 2) -
          (delta * (c + 2) - 1) = 1 :=
        Nat.sub_sub_self hCpos
      rw [hdiff] at hsub
      exact hsub
    exact Nat.eq_one_of_dvd_one hg1

  · have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
    rw [if_neg heven] at hmap
    have hdvd : d r ∣ delta * (c + 2) + 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    let g := Nat.gcd delta (d r)
    have hgdelta : g ∣ delta := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d r := Nat.gcd_dvd_right _ _
    have hgq : g ∣ delta * (c + 2) + 1 := Nat.dvd_trans hgd hdvd
    have hgC : g ∣ delta * (c + 2) :=
      Nat.dvd_mul_right_of_dvd hgdelta (c + 2)
    have hg1 : g ∣ 1 := by
      have hsub := Nat.dvd_sub hgq hgC
      simpa using hsub
    exact Nat.eq_one_of_dvd_one hg1

example {n : Nat} (hn : 2 ≤ n) : D n % 2 = 0 :=
  D_mod_two_eq_zero_of_two_le hn

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (heven : r % 2 = 0) (hle : r ≤ C) (hnontriv : 1 < d r) :
    3 * d r ≤ C - 1 :=
  constant_D_event_even_size_bound_of_le hr hD heven hle hnontriv

example {r C : Nat} (hr : 3 ≤ r) (hD : D (r - 1) = C)
    (hodd : r % 2 ≠ 0) (hle : r ≤ C) :
    3 * d r ≤ C + 1 :=
  constant_D_event_odd_size_bound_of_le hr hD hodd hle

example {delta c r : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = delta * (c + 2)) :
    Nat.gcd delta (d r) = 1 :=
  constant_D_event_coprime_of_critical_form hr hD

example {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hno : ∀ j : Nat, k + 1 < j → j ≤ D (k + 1) → d j = 1) :
    B (D (k + 1)) = 2 ∧ D (D (k + 1)) = D (k + 1) := by
  exact critical_failure_no_event_to_fundamental hk hIH hnew hfail hno

example {n C : Nat} (hn : 2 ≤ n) :
    (∀ j : Nat, n < j → j ≤ C → d j = 1) ∨
      ∃ r : Nat, n < r ∧ r ≤ C ∧ 1 < d r ∧
        ∀ j : Nat, n < j → j < r → d j = 1 :=
  first_later_nontrivial_dichotomy hn

example {n C r : Nat} (hn : 2 ≤ n) (hC : D n = C) (hnr : n < r)
    (hfirst : ∀ j : Nat, n < j → j < r → d j = 1) :
    D (r - 1) = C :=
  first_later_event_D_eq hn hC hnr hfirst

example {k P : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    (B (D (k + 1)) = 2 ∧ D (D (k + 1)) = D (k + 1)) ∨
      ∃ r : Nat, k + 1 < r ∧ r ≤ D (k + 1) ∧ 1 < d r ∧
        ∀ j : Nat, k + 1 < j → j < r → d j = 1 :=
  critical_failure_first_event_dichotomy hk hIH hnew hfail

example {k M C r : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hC : D (k + 1) = C) (hr : k + 1 < r) (hrC : r ≤ C)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    ∃ c : Nat, k + 1 = d (k + 1) * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      D (r - 1) = C ∧
      ((r % 2 = 0 ∧ d r ∣ C - 1 ∧ d r < C - 1 ∧
          3 * d r ≤ C - 1 ∧ Nat.gcd (d (k + 1)) (d r) = 1) ∨
        (r % 2 = 1 ∧ d r ∣ C + 1 ∧ d r < C + 1 ∧
          3 * d r ≤ C + 1 ∧ Nat.gcd (d (k + 1)) (d r) = 1)) ∧
      B r + 2 = B (r - 1) + d r ∧
      D r = C + (d r - 1) ∧
      C + 2 ≤ D r ∧
      B (r - 1) + (r - 1) = C + 2 ∧
      B r + r = D r + 2 :=
  critical_first_event_transfer hk hIH hnew hfail hC hr hrC hdr hfirst

example {k M P C r : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k)
    (hIH : B k + 2 ≤ 2 * P) (hnew : P < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hC : D (k + 1) = C) (hr : k + 1 < r) (hrC : r ≤ C)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    d r ≤ P ∨ (P < d r ∧ d r < d (k + 1)) ∨
      IsAttainedPreviousMaximum (d r) r :=
  critical_first_event_previous_or_new_max hk hP hIH hnew hfail hC hr hrC hdr hfirst

example {r C finish s : Nat} (hr : 2 ≤ r)
    (hstep : D r = C + (d r - 1))
    (hchain : HasNontrivialChain r finish s) :
    C + (d r - 1) + 2 * s ≤ D finish :=
  D_growth_after_D_step hr hstep hchain

example {s C : Nat} (hs : IsMovingHorizonState s C)
    (hno : ∀ j : Nat, s < j → j ≤ C → d j = 1) :
    D C = C ∧ B C + (C - s) = B s :=
  moving_horizon_no_event_telescope hs hno

example {s C : Nat} (hs : IsMovingHorizonState s C) :
    B s = (C - s) + 2 :=
  moving_horizon_slack_coordinate hs

example {s C : Nat} (hs : IsMovingHorizonState s C)
    (hex : ∃ j : Nat, s < j ∧ j ≤ C ∧ 1 < d j) :
    ∃ r C', IsMovingHorizonStep s C r C' :=
  moving_horizon_step_of_exists hs hex

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) = (C - s) + (d r - 1) :=
  moving_horizon_slack_transition hstep

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    d r + s ≤ C :=
  moving_horizon_step_size_add_le hstep

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C' - r + 2 ≤ 2 * (C - s) :=
  moving_horizon_next_slack_upper hstep

example {s C : Nat} (hs : IsMovingHorizonState s C) :
    (∀ j : Nat, s < j → j ≤ C → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep s C r C' :=
  moving_horizon_dichotomy hs

example {P s : Nat} (hs : 2 ≤ s)
    (hP : IsAttainedPreviousMaximum P (s - 1)) (hnew : P < d s) :
    IsAttainedPreviousMaximum (d s) s :=
  attained_previous_maximum_extend hs hP hnew

example {P s r : Nat} (hP : IsAttainedPreviousMaximum P s)
    (hsr : s < r) (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, s < j → j < r → d j = 1) :
    (d r ≤ P ∧ IsAttainedPreviousMaximum P r) ∨
      (P < d r ∧ IsAttainedPreviousMaximum (d r) r) :=
  moving_horizon_max_transfer hP hsr hdr hfirst

example {s C q : Nat} (hchain : HasMovingHorizonChain s C q) :
    ∃ sf Cf, IsMovingHorizonState sf Cf ∧ C + 2 * q ≤ Cf :=
  moving_horizon_chain_growth hchain

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r ∣ C - 1 ∧ d r < C - 1 ∧ 3 * d r ≤ C - 1) ∨
      (r % 2 = 1 ∧ d r ∣ C + 1 ∧ d r < C + 1 ∧ 3 * d r ≤ C + 1) :=
  moving_horizon_step_event_package hstep

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    d r ≤ C - s :=
  moving_horizon_step_size_le_slack hstep

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    IsMovingHorizonState (k + 1) (D (k + 1)) :=
  critical_failure_moving_horizon_state hk hIH hnew hfail

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    k + 1 + 2 * d (k + 1) = D (k + 1) :=
  critical_initial_slack hk hIH hnew hfail

example {k M : Nat} (hk : 2 ≤ k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    (∀ j : Nat, k + 1 < j → j ≤ D (k + 1) → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep (k + 1) (D (k + 1)) r C' :=
  critical_failure_moving_horizon_dichotomy hk hIH hnew hfail

example {k P : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k) (hnew : P < d (k + 1)) :
    IsAttainedPreviousMaximum (d (k + 1)) (k + 1) :=
  critical_failure_current_maximum hk hP hnew

example {k P r : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum P k) (hnew : P < d (k + 1))
    (hr : k + 1 < r) (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, k + 1 < j → j < r → d j = 1) :
    (d r ≤ d (k + 1) ∧ IsAttainedPreviousMaximum (d (k + 1)) r) ∨
      (d (k + 1) < d r ∧ IsAttainedPreviousMaximum (d r) r) :=
  critical_first_event_current_or_new_max hk hP hnew hr hdr hfirst

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (heven : r % 2 = 0) :
    ∃ q : Nat, C - s = (r - s) + 1 + d r * q ∧ q % 2 = 1 ∧
      1 ≤ q ∧ C' - r = d r * (q + 1) :=
  moving_horizon_even_quotient_normal_form hstep heven

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hodd : r % 2 = 1) :
    ∃ q : Nat, C - s + 3 = (r - s) + d r * q ∧ q % 2 = 0 ∧
      2 ≤ q ∧ C' - r + 4 = d r * (q + 1) :=
  moving_horizon_odd_quotient_normal_form hstep hodd

example {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hnew : P < d r) (hPodd : P % 2 = 1) :
    r % 2 = 0 ∧ C' - r = 2 * d r :=
  moving_horizon_normalized_new_max_even hstep hnorm hnew hPodd

example {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hP : IsAttainedPreviousMaximum P s) (hP5 : 5 < P)
    (hnorm : C - s = 2 * P) (hnew : P < d r) :
    ∃ c : Nat, r = d r * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      IsAttainedPreviousMaximum (d r) r ∧
      C' = d r * (c + 2) ∧ D r = d r * (c + 2) :=
  moving_horizon_record_state_regeneration hstep hP hP5 hnorm hnew

example {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hfar : d r + 3 ≤ r - s) :
    B r + 2 ≤ 2 * P :=
  moving_horizon_far_old_event_envelope hstep hnorm hfar

example {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hold : d r ≤ P) :
    (d r ≤ P ∧ r - s ≤ d r + 2) ∨ B r + 2 ≤ 2 * P :=
  moving_horizon_old_event_dichotomy hstep hnorm hold

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    C' = C + (d r - 1) :=
  moving_horizon_step_update hstep

example {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') :
    Nat.gcd (d r) (d u) ∣ 3 :=
  moving_horizon_successive_event_gcd_dvd_three hstep hnext

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (B r + 2) + (r - s) + 1 = (B s + 2) + d r :=
  moving_horizon_excess_transition hstep

example {P X s C r C' X' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hXs : B s + 2 = 2 * P + X)
    (hXr : B r + 2 = 2 * P + X') :
    X' + (r - s) + 1 = X + d r :=
  moving_horizon_excess_coordinates hstep hXs hXr

example {P Y Y' s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hYs : B s + 2 + Y = 2 * P)
    (hYr : B r + 2 + Y' = 2 * P) :
    Y' + d r = Y + (r - s) + 1 :=
  moving_horizon_deficit_transition hstep hYs hYr

example {M : Nat} (hM : 5 < M) (hodd : M % 2 = 1)
    (hD : D (M + 2) = 2 * M - 2) :
    d (M + 3) = Nat.gcd (M + 3) (2 * M - 3) ∧
      d (M + 3) ∣ 9 :=
  canonical_start_next_step_gcd_dvd_nine hM hodd hD

example {M r : Nat} (hM : 5 < M)
    (hrange : r ≤ 2 * M - 2) (hafter : M + 2 < r)
    (hD : D (r - 1) = 2 * M - 2) (hnew : M < d r) : False :=
  canonical_start_event_not_larger_before_horizon hM hrange hafter hD hnew

example {P s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hnorm : C - s = 2 * P) (hclose : r - s ≤ d r + 2) :
    B r + 2 = 2 * P + (d r + 3 - (r - s)) :=
  moving_horizon_normalized_close_old_excess hstep hnorm hclose

example {P s C r C' c c' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcanon_s : s = P * c) (hcanon_C : C = P * (c + 2))
    (hnew : P < d r)
    (hregen : r = d r * c' ∧ c' % 2 = 0 ∧ 2 ≤ c' ∧
      C' = d r * (c' + 2)) :
    r - s + d r + 1 = 2 * P ∧
      d r * (c' + 1) + 1 = P * (c + 2) ∧ c' ≤ c :=
  moving_horizon_regenerated_record_quotient_transition
    hstep hcanon_s hcanon_C hnew hregen

example {P e c : Nat} (hPpos : 1 ≤ P) (hnew : P < e)
    (hquot : e * (c + 1) + 1 = P * (c + 2)) :
    P - 1 = (e - P) * (c + 1) :=
  moving_horizon_same_quotient_plateau hPpos hnew hquot

example {P e f c : Nat} (hPpos : 1 ≤ P) (hPe : P < e) (hef : e < f)
    (hquot₁ : e * (c + 1) + 1 = P * (c + 2))
    (hquot₂ : f * (c + 1) + 1 = e * (c + 2)) :
    (c + 1) ^ 2 ∣ P - 1 :=
  moving_horizon_same_quotient_two_step_dvd hPpos hPe hef hquot₁ hquot₂

example {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'') (hre : r % 2 = 0) :
    Nat.gcd (d r) (d u) = 1 :=
  moving_horizon_successive_event_gcd_eq_one_of_prev_even hstep hnext hre

example {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (hro : r % 2 = 1) (huo : u % 2 = 1) :
    Nat.gcd (d r) (d u) = 1 :=
  moving_horizon_successive_event_gcd_eq_one_of_odd_odd hstep hnext hro huo

example {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (hro : r % 2 = 1) (hue : u % 2 = 0) :
    Nat.gcd (d r) (d u) ∣ 3 :=
  moving_horizon_successive_event_gcd_dvd_three_of_odd_even hstep hnext hro hue

example {s C r C' u C'' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (heq : d r = d u) : d r = 3 :=
  moving_horizon_equal_successive_event_is_three hstep hnext heq

example {s C r C' u C'' v C''' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (hlast : IsMovingHorizonStep u C'' v C''')
    (heq1 : d r = d u) (heq2 : d u = d v) : False :=
  moving_horizon_no_three_equal_successive_events hstep hnext hlast heq1 heq2

example {P s C X E T q : Nat}
    (hchain : HasMovingHorizonCloseChain P s C X E T q) :
    ∃ sf Cf Xf, IsMovingHorizonState sf Cf ∧
      B sf + 2 = 2 * P + Xf ∧ Xf + T = X + E :=
  moving_horizon_close_chain_excess_telescope hchain

example {P s C X E T q : Nat}
    (hP : IsAttainedPreviousMaximum P s)
    (hchain : HasMovingHorizonCloseChain P s C X E T q) :
    ∃ sf Cf Xf, IsMovingHorizonState sf Cf ∧
      IsAttainedPreviousMaximum P sf ∧ B sf + 2 = 2 * P + Xf ∧
      Xf + T = X + E :=
  moving_horizon_close_chain_preserves_maximum hP hchain

example {delta M e t q : Nat}
    (hdeltaodd : delta % 2 = 1) (heodd : e % 2 = 1)
    (hMe : M < e) (hEd : e < delta)
    (hbound : delta + 6 ≤ 2 * M) (hclose : t ≤ e + 2)
    (hform : 2 * delta = t + 1 + e * q)
    (hqodd : q % 2 = 1) : q = 3 :=
  critical_intermediate_even_quotient_eq_three
    hdeltaodd heodd hMe hEd hbound hclose hform hqodd

example {delta M e t q : Nat}
    (hMe : M < e) (hbound : delta + 6 ≤ 2 * M)
    (hform : 2 * delta + 3 = t + e * q)
    (hqeven : q % 2 = 0) (hq2 : 2 ≤ q) : q = 2 :=
  critical_intermediate_odd_quotient_eq_two hMe hbound hform hqeven hq2

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r = Nat.gcd r (C - 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) ∨
      (r % 2 = 1 ∧ d r = Nat.gcd (r - 2) (C + 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) :=
  moving_horizon_first_hit_map hstep

example {s₁ C₁ r₁ C₁' s₂ C₂ r₂ C₂' e : Nat}
    (hstep₁ : IsMovingHorizonStep s₁ C₁ r₁ C₁')
    (hstep₂ : IsMovingHorizonStep s₂ C₂ r₂ C₂')
    (he₁ : d r₁ = e) (he₂ : d r₂ = e)
    (hpar : r₁ % 2 = r₂ % 2) :
    e ∣ r₂ - r₁ ∧ e ∣ C₂ - C₁ :=
  moving_horizon_same_parity_event_drift hstep₁ hstep₂ he₁ he₂ hpar

example {e₁ e₂ : Nat} (he₁ : 3 ≤ e₁) (he₂ : 3 ≤ e₂)
    (h₁ : e₁ ∣ e₁ + e₂ - 2) (h₂ : e₂ ∣ e₁ + e₂ - 2) : False :=
  moving_horizon_no_two_event_drift_cycle he₁ he₂ h₁ h₂

example {s₀ C₀ r₁ C₁ r₂ C₂ r₃ C₃ r₄ C₄ e₁ e₂ : Nat}
    (hstep₁ : IsMovingHorizonStep s₀ C₀ r₁ C₁)
    (hstep₂ : IsMovingHorizonStep r₁ C₁ r₂ C₂)
    (hstep₃ : IsMovingHorizonStep r₂ C₂ r₃ C₃)
    (hstep₄ : IsMovingHorizonStep r₃ C₃ r₄ C₄)
    (he₁ : d r₁ = e₁) (he₂ : d r₂ = e₂)
    (he₃ : d r₃ = e₁) (he₄ : d r₄ = e₂)
    (hp₁ : r₁ % 2 = r₃ % 2) (hp₂ : r₂ % 2 = r₄ % 2) : False :=
  moving_horizon_no_repeated_two_event_block
    hstep₁ hstep₂ hstep₃ hstep₄ he₁ he₂ he₃ he₄ hp₁ hp₂

example {P X s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hP : IsAttainedPreviousMaximum P s) (hP5 : 5 < P)
    (hXs : B s + 2 = 2 * P + X) (hX : X ≤ 5)
    (hnew : P < d r) :
    ∃ c : Nat, r = d r * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      IsAttainedPreviousMaximum (d r) r ∧
      C' = d r * (c + 2) ∧ D r = d r * (c + 2) :=
  moving_horizon_small_excess_new_max hstep hP hP5 hXs hX hnew

example {P c q : Nat} (hPpos : 1 ≤ P)
    (hchain : HasSameQuotientRegenerationChain P c q) :
    (c + 1) ^ q ∣ P - 1 :=
  moving_horizon_same_quotient_plateau_power hPpos hchain

example {n : Nat} (hn : 2 ≤ n) :
    IsDTransition n (D (n - 1)) (D n) :=
  isDTransition_of_two_le hn

example {k M : Nat} (hP : IsAttainedPreviousMaximum M k)
    (hnew : M < d (k + 1)) :
    ∃ p : Nat, 2 ≤ p ∧ p ≤ k ∧ d p = M ∧
      (∀ j : Nat, 2 ≤ j → j < p → d j < M) ∧
      IsCappedDPath p (k + 1) M (d (k + 1)) :=
  attained_previous_maximum_capped_D_path hP hnew rfl

example {k M : Nat} (hk : 2 ≤ k)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∃ p delta c : Nat,
      IsCappedDPath p (k + 1) M delta ∧
      d (k + 1) = delta ∧
      k + 1 = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      D (k + 1) = delta * (c + 2) := by
  rcases attained_previous_maximum_capped_D_path hP hnew rfl with
    ⟨p, _, _, _, _, hpath⟩
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, hcmod, hc2, _, hD, _, _⟩
  exact ⟨p, d (k + 1), c, hpath, rfl, hc, hcmod, hc2, hD⟩

example {M p v : Nat} (hp : 2 ≤ p) (hd : d p = M)
    (hav : a (p - 1) = M * v) :
    D p + p = M * (v + 1) :=
  previous_record_D_coordinate hp hd hav

example {k delta c : Nat} (hD : D (k + 1) = delta * (c + 2))
    (hdelta : d (k + 1) = delta) :
    D k = delta * (c + 1) + 1 :=
  critical_previous_D_coordinate hD hdelta

example {m : Nat} (hm : 2 ≤ m) (hfund : B m = 2) :
    (d (m + 1) = 1 ∧ d (m + 2) = 1 ∧ B (m + 2) = 0 ∧
      d (m + 3) = m + 1 ∧ B (m + 3) + 2 = m + 1) ∨
    (d (m + 1) = 1 ∧ d (m + 2) = 3 ∧ B (m + 2) = 2 ∧
      d (m + 3) = 1 ∧ d (m + 4) = 1 ∧ B (m + 4) = 0 ∧
      d (m + 5) = m + 3 ∧ B (m + 5) + 2 = m + 3) :=
  fundamental_reset hm hfund

example {M delta s C r C' c Y : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hYs : B s + 2 + Y = 2 * M) (hModd : M % 2 = 1)
    (hnew : M < delta)
    (hcrit : d r = delta ∧ r = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      C' = delta * (c + 2)) :
    r % 2 = 0 ∧ C' - r = 2 * delta ∧
      Y + (r - s) + delta + 5 = 2 * M ∧ Y + 8 ≤ M :=
  moving_horizon_critical_entry_barrier hstep hYs hModd hnew hcrit

example {M s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hslack : C - s ≤ M) (hcross : M < C' - r) :
    r - s + 2 ≤ d r :=
  moving_horizon_first_dangerous_crossing hstep hslack hcross

example {delta s C r C' c : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcrit : d r = delta ∧ r = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      C' = delta * (c + 2)) :
    ∃ q : Nat, C - s = (r - s) + 1 + delta * q ∧ q % 2 = 1 ∧
      1 ≤ q ∧ C' - r = delta * (q + 1) ∧ q = 1 :=
  moving_horizon_critical_even_q_one hstep hcrit

example {m : Nat} (hm : 2 ≤ m) (hfund : B m = 2) :
    (d (m + 3) = m + 1 ∧ D (m + 3) = 2 * (m + 1) - 2) ∨
    (d (m + 5) = m + 3 ∧ D (m + 5) = 2 * (m + 3) - 2) :=
  fundamental_reset_coordinate hm hfund

example {M delta Y E T t : Nat} (hModd : M % 2 = 1)
    (hdeltaodd : delta % 2 = 1) (hnew : M < delta) (ht : 1 ≤ t)
    (htel : Y + E = M + T)
    (hentry : Y + t + delta + 5 = 2 * M) :
    M + E = T + t + delta + 5 ∧ T + 8 ≤ E :=
  critical_entry_cumulative_compression hModd hdeltaodd hnew ht htel hentry

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) + 1 = (C - s) + d r := by
  have h := moving_horizon_slack_transition hstep
  have hd : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  omega

example {s C r C' kappa : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hk : d r = (r - s) + 1 + kappa) :
    C' - r = C - s + kappa := by
  have h := moving_horizon_slack_transition hstep
  have hd : 1 ≤ d r := one_le_d_of_two_le
    (Nat.le_trans hstep.1.1 (Nat.le_of_lt hstep.2.1))
  omega

example {P Y Y' s C r C' kappa : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hYs : B s + 2 + Y = 2 * P)
    (hYr : B r + 2 + Y' = 2 * P)
    (hk : d r = (r - s) + 1 + kappa) :
    Y' + kappa = Y := by
  exact moving_horizon_deficit_compression hstep hYs hYr hk

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hpos : (r - s) + 1 ≤ d r) :
    ∃ kappa : Nat, d r = (r - s) + 1 + kappa ∧
      C' - r = C - s + kappa :=
  moving_horizon_positive_compression_exists hstep hpos

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q) :
    IsMovingHorizonState sf Cf ∧ Cf - sf ≤ M ∧ B sf ≠ 2 :=
  moving_horizon_capped_old_path_endpoint hpath

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q) :
    (C - s) + E = (Cf - sf) + T :=
  moving_horizon_capped_old_path_telescope hpath

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q)
    (hET : T ≤ E) :
    ∃ kappa : Nat, E = T + kappa ∧ Cf - sf = C - s + kappa :=
  moving_horizon_capped_old_path_total_compression hpath hET

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q) :
    Cf + q = C + E ∧ sf + q = s + T :=
  moving_horizon_capped_old_path_ledger hpath

example {M s C E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M (M + 2) (2 * M - 2)
      s C E T q) :
    C + q = (2 * M - 2) + E ∧ s + q = (M + 2) + T :=
  moving_horizon_capped_old_path_canonical_ledger hpath

example {M s C E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M (M + 2) (2 * M - 2)
      s C E T q) :
    D s + q = (2 * M - 2) + E ∧ s + q = (M + 2) + T :=
  moving_horizon_capped_old_path_canonical_absolute_ledger hpath

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q) :
    3 * q ≤ E ∧ E ≤ M * q ∧ 2 * q ≤ T :=
  moving_horizon_capped_old_path_count_bounds hpath

example {M sf Cf r C' E T q : Nat} (hM : 5 < M)
    (hpath : HasMovingHorizonCappedOldPath M (M + 2) (2 * M - 2)
      sf Cf E T q)
    (hstep : IsMovingHorizonStep sf Cf r C')
    (hold : d r ≤ M) (hcross : M < C' - r) :
    ∃ kappa : Nat,
      d r = (r - sf) + 1 + kappa ∧ 1 ≤ kappa ∧ d r ≤ M ∧
      C' - r = Cf - sf + kappa ∧ 5 + T ≤ E + kappa :=
  moving_horizon_capped_old_path_first_crossing hM hpath hstep hold hcross

example {M s C sf Cf q : Nat} (hM : 5 < M)
    (hsuffix : HasMovingHorizonDangerousSuffix M s C sf Cf q) :
    IsMovingHorizonState sf Cf ∧ M < Cf - sf ∧
      Cf - sf ≤ 2 * M - 4 ∧ B sf ≠ 2 :=
  moving_horizon_dangerous_suffix_endpoint_band hM hsuffix

example {M s C sf Cf q : Nat} (hM : 5 < M)
    (hsuffix : HasMovingHorizonDangerousSuffix M s C sf Cf q) :
    IsMovingHorizonState s C ∧ M < C - s ∧
      C - s ≤ 2 * M - 4 ∧ B s ≠ 2 :=
  moving_horizon_dangerous_suffix_start_band hM hsuffix

example {M delta sf Cf rf Cf' c : Nat} (hM : 5 < M)
    (hpath : HasMovingHorizonTerminalDangerousExcursion
      M delta sf Cf rf Cf' c) :
    IsMovingHorizonState sf Cf ∧ M < Cf - sf ∧
      Cf - sf ≤ 2 * M - 4 ∧ B sf ≠ 2 :=
  moving_horizon_terminal_dangerous_excursion_endpoint_band hM hpath

example {M s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hslack : C - s ≤ M) (hcross : M < C' - r) :
    (r % 2 = 0 ∧
        ∃ q : Nat, C - s = (r - s) + 1 + d r * q ∧
          q % 2 = 1 ∧ 1 ≤ q ∧ C' - r = d r * (q + 1) ∧
          d r * q + 2 ≤ M ∧ M < d r * (q + 1)) ∨
      (r % 2 = 1 ∧
        ∃ q : Nat, C - s + 3 = (r - s) + d r * q ∧
          q % 2 = 0 ∧ 2 ≤ q ∧ C' - r + 4 = d r * (q + 1) ∧
          d r * q ≤ M + 2 ∧ M + 4 < d r * (q + 1)) :=
  moving_horizon_terminal_crossing_threshold hstep hslack hcross

example {delta s C r C' c : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcrit : d r = delta ∧ r = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      C' = delta * (c + 2)) :
    r % 2 = 0 ∧ C - 1 = r + delta ∧
      C - 1 = delta * (c + 1) ∧ (c + 1) % 2 = 1 ∧ 3 ≤ c + 1 :=
  moving_horizon_critical_predecessor_factorization hstep hcrit

example {M delta Y s C r C' c : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hYs : B s + 2 + Y = 2 * M) (hModd : M % 2 = 1)
    (hnew : M < delta)
    (hcrit : d r = delta ∧ r = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      C' = delta * (c + 2)) :
    M + 2 ≤ delta ∧ Y + (r - s) + 7 ≤ M ∧ r - s < delta :=
  moving_horizon_critical_short_tail hstep hYs hModd hnew hcrit

example {delta s C r C' c : Nat} (hstep : IsMovingHorizonStep s C r C')
    (hcrit : d r = delta ∧ r = delta * c ∧ c % 2 = 0 ∧ 2 ≤ c ∧
      C' = delta * (c + 2)) :
    C - 1 = delta * (c + 1) ∧
      delta = Nat.gcd r (C - 1) ∧
      (∀ j : Nat, s < j → j < r →
        (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1)) :=
  moving_horizon_critical_predecessor_first_hit hstep hcrit

example {M delta sf Cf rf Cf' c : Nat}
    (hpath : HasMovingHorizonTerminalDangerousExcursion
      M delta sf Cf rf Cf' c) :
    ∃ s C r C' e,
      IsMovingHorizonStep s C r C' ∧ d r = e ∧
      ((r % 2 = 0 ∧
          Nat.gcd e (delta * c) ∣ rf - r ∧
          Nat.gcd e (delta * (c + 1)) ∣ Cf - C ∧
          Nat.gcd e delta ∣ rf - r ∧ Nat.gcd e delta ∣ Cf - C) ∨
        (r % 2 = 1 ∧
          Nat.gcd e (delta * c) ∣ rf - r + 2 ∧
          Nat.gcd e (delta * (c + 1)) ∣ Cf - C - 2 ∧
          2 ≤ Cf - C ∧
          Nat.gcd e delta ∣ rf - r + 2 ∧
            Nat.gcd e delta ∣ Cf - C - 2)) :=
  moving_horizon_terminal_crossing_debt_pullback hpath

/-- Abstract event-map/history witnesses only; these do not assert `D s = C`. -/
def IsAbstractFirstEvent (s C r e : Nat) : Prop :=
  2 ≤ s ∧ s < r ∧ r ≤ C ∧ 1 < e ∧
    ((r % 2 = 0 ∧ e = Nat.gcd r (C - 1)) ∨
      (r % 2 = 1 ∧ e = Nat.gcd (r - 2) (C + 1))) ∧
    (∀ j : Nat, s < j → j < r →
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))

example :
    IsAbstractFirstEvent 41 50 42 7 ∧
      50 + 7 - 1 = 56 ∧ 9 < 56 - 42 ∧ 56 - 42 ≤ 2 * 9 - 4 ∧
      IsAbstractFirstEvent 42 56 44 11 ∧
      44 = 11 * 4 ∧ 56 - 1 = 11 * (4 + 1) ∧ 56 + 11 - 1 = 11 * 6 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      omega
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      have hj : j = 43 := by omega
      subst j
      decide

example :
    IsAbstractFirstEvent 33 46 36 9 ∧
      46 + 9 - 1 = 54 ∧ 13 < 54 - 36 ∧ 54 - 36 ≤ 2 * 13 - 4 ∧
      IsAbstractFirstEvent 36 54 37 5 ∧
      54 + 5 - 1 = 58 ∧ 13 < 58 - 37 ∧ 58 - 37 ≤ 2 * 13 - 4 ∧
      IsAbstractFirstEvent 37 58 38 19 ∧
      38 = 19 * 2 ∧ 58 - 1 = 19 * (2 + 1) ∧ 58 + 19 - 1 = 19 * 4 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide,
    by decide, ?_, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      have hj : j = 34 ∨ j = 35 := by omega
      rcases hj with rfl | rfl <;> decide
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · intro j hsj hjr
      omega
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      have hj : j = 51 := by omega
      subst j
      decide

example :
    IsAbstractFirstEvent 50 66 52 13 ∧
      66 + 13 - 1 = 78 ∧ 19 < 78 - 52 ∧ 78 - 52 ≤ 2 * 19 - 4 ∧
      IsAbstractFirstEvent 52 78 56 7 ∧
      78 + 7 - 1 = 84 ∧ 19 < 84 - 56 ∧ 84 - 56 ≤ 2 * 19 - 4 ∧
      IsAbstractFirstEvent 56 84 57 5 ∧
      84 + 5 - 1 = 88 ∧ 19 < 88 - 57 ∧ 88 - 57 ≤ 2 * 19 - 4 ∧
      IsAbstractFirstEvent 57 88 58 29 ∧
      58 = 29 * 2 ∧ 88 - 1 = 29 * (2 + 1) ∧ 88 + 29 - 1 = 29 * 4 := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide,
    by decide, ?_, by decide, by decide, by decide, ?_, by decide, by decide,
    by decide⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      have hj : j = 51 := by omega
      subst j
      decide
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      have hj : j = 53 ∨ j = 54 ∨ j = 55 := by omega
      rcases hj with rfl | rfl | rfl <;> decide
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inr ⟨by decide, by decide⟩
    · intro j hsj hjr
      omega
  · refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · intro j hsj hjr
      omega

example : D 41 = 42 ∧ D 33 ≠ 46 ∧ D 50 ≠ 66 := by decide

example :
    ¬ ∃ E T q, HasMovingHorizonCappedOldPath 9 11 16 41 50 E T q := by
  rintro ⟨E, T, q, hpath⟩
  have hD : D 41 = 50 :=
    (moving_horizon_capped_old_path_endpoint hpath).1.2.1
  exact (by decide : D 41 ≠ 50) hD

example :
    ¬ ∃ E T q, HasMovingHorizonCappedOldPath 13 15 24 33 46 E T q := by
  rintro ⟨E, T, q, hpath⟩
  have hD : D 33 = 46 :=
    (moving_horizon_capped_old_path_endpoint hpath).1.2.1
  exact (by decide : D 33 ≠ 46) hD

example :
    ¬ ∃ E T q, HasMovingHorizonCappedOldPath 19 21 36 50 66 E T q := by
  rintro ⟨E, T, q, hpath⟩
  have hD : D 50 = 66 :=
    (moving_horizon_capped_old_path_endpoint hpath).1.2.1
  exact (by decide : D 50 ≠ 66) hD

example :
    D 15 = 24 ∧ d 17 = 5 ∧ D 17 = 28 ∧ d 18 = 9 ∧ D 18 = 36 ∧
      B 15 = 11 ∧ B 17 = 13 ∧ B 18 = 20 := by decide

example {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    3 ≤ d r := moving_horizon_step_event_ge_three hstep

example {s C r C' e : Nat} (hstep : IsMovingHorizonStep s C r C')
    (he : d r = e) :
    (r % 2 = 0 ∧ e ∣ r ∧ e ∣ C') ∨
      (r % 2 = 1 ∧ e ∣ r - 2 ∧ e ∣ C' + 2) :=
  moving_horizon_step_endpoint_anchor hstep he

example {M r C' e : Nat}
    (hstep : IsMovingHorizonStep (M + 2) (2 * M - 2) r C')
    (he : d r = e) (hold : e ≤ M) :
    3 ≤ e ∧ e ≤ M ∧
      ((r % 2 = 0 ∧ e ∣ 2 * M - 3) ∨
        (r % 2 = 1 ∧ e ∣ 2 * M - 1)) :=
  moving_horizon_canonical_first_old_event_factorization hstep he hold

example {M s C r C' E T q e : Nat}
    (hpath : HasMovingHorizonCappedOldPath M (M + 2) (2 * M - 2)
      s C E T q)
    (hstep : IsMovingHorizonStep s C r C')
    (he : d r = e) (hold : e ≤ M) :
    3 ≤ e ∧ e ≤ M ∧
      ((r % 2 = 0 ∧
          ∃ v : Nat, C - 1 = e * v ∧
            e * v + (q + 1) = (2 * M - 2) + E) ∨
        (r % 2 = 1 ∧
          ∃ v : Nat, C + 1 = e * v ∧
            e * v + (q + 1) = (2 * M - 2) + E + 2)) :=
  moving_horizon_canonical_event_factor_ledger hpath hstep he hold

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q)
    (hq : 1 ≤ q) :
    ∃ e : Nat, e = d sf ∧ 3 ≤ e ∧ e ≤ M ∧
      ((sf % 2 = 0 ∧ e ∣ sf ∧ e ∣ Cf) ∨
        (sf % 2 = 1 ∧ e ∣ sf - 2 ∧ e ∣ Cf + 2)) :=
  moving_horizon_capped_old_path_last_event_anchor hpath hq

-- The genuine M=13 first event is the odd positive control: 5 divides 25.
example :
    IsMovingHorizonStep 15 24 17 28 ∧
      5 ∣ (2 * 13 - 1) ∧
      5 * 5 + (0 + 1) = (2 * 13 - 2) + 0 + 2 := by
  refine ⟨?_, by decide, by decide⟩
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide,
    by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    have hj : j = 16 := by omega
    subst j
    decide
  · simp [IsMovingHorizonState, D, a]

-- The odd endpoint shifts are necessary: the unshifted divisibilities fail
-- on the same genuine event.
example :
    5 ∣ (17 - 2) ∧ 5 ∣ (28 + 2) ∧
      ¬ 5 ∣ 17 ∧ ¬ 5 ∣ 28 := by decide

-- The smallest known factor-ancestry-compatible terminal survivors remain
-- abstract event-map/history states, not full recurrence prefixes.
example :
    (7 ∣ 42 ∧ 7 ∣ 56) ∧
      (9 ∣ 36 ∧ 9 ∣ 54) ∧ (5 ∣ 35 ∧ 5 ∣ 60) ∧
      (13 ∣ 52 ∧ 13 ∣ 78) ∧ (7 ∣ 56 ∧ 7 ∣ 84) ∧
      (5 ∣ 55 ∧ 5 ∣ 90) := by decide

example {s C r C' e : Nat} (hstep : IsMovingHorizonStep s C r C')
    (he : d r = e) (hpar : r % 2 = 0) :
    ∃ u v : Nat, r = e * u ∧ C - 1 = e * v ∧
      Nat.gcd u v = 1 ∧ (v - u) % 2 = 1 ∧ 1 ≤ v - u ∧
      C' = e * (v + 1) :=
  moving_horizon_even_factor_pair hstep he hpar

example {s C r C' e : Nat} (hstep : IsMovingHorizonStep s C r C')
    (he : d r = e) (hpar : r % 2 = 1) :
    ∃ u v : Nat, r - 2 = e * u ∧ C + 1 = e * v ∧
      Nat.gcd u v = 1 ∧ (v - u) % 2 = 0 ∧ 2 ≤ v - u ∧
      C' + 2 = e * (v + 1) :=
  moving_horizon_odd_factor_pair hstep he hpar

example {s C r C' u C'' e f : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hnext : IsMovingHorizonStep r C' u C'')
    (he : d r = e) (hf : d u = f) :
    (r % 2 = 0 ∧ u % 2 = 0 ∧
        ∃ v w : Nat, C - 1 = e * v ∧ C' - 1 = f * w ∧
          f * w + 1 = e * (v + 1)) ∨
      (r % 2 = 0 ∧ u % 2 = 1 ∧
        ∃ v w : Nat, C - 1 = e * v ∧ C' + 1 = f * w ∧
          f * w = e * (v + 1) + 1) ∨
      (r % 2 = 1 ∧ u % 2 = 0 ∧
        ∃ v w : Nat, C + 1 = e * v ∧ C' - 1 = f * w ∧
          f * w + 3 = e * (v + 1)) ∨
      (r % 2 = 1 ∧ u % 2 = 1 ∧
        ∃ v w : Nat, C + 1 = e * v ∧ C' + 1 = f * w ∧
          f * w + 1 = e * (v + 1)) :=
  moving_horizon_adjacent_factor_transition hstep hnext he hf

example {e f v w : Nat} (h : f * w + 1 = e * (v + 1)) :
    Nat.gcd e f = 1 ∧ Nat.gcd e w = 1 ∧
      Nat.gcd (v + 1) f = 1 ∧ Nat.gcd (v + 1) w = 1 :=
  moving_horizon_factor_pair_coprimality h

example {e f v w : Nat} (h : f * w + 3 = e * (v + 1)) :
    Nat.gcd e f ∣ 3 ∧ Nat.gcd e w ∣ 3 ∧
      Nat.gcd (v + 1) f ∣ 3 ∧ Nat.gcd (v + 1) w ∣ 3 :=
  moving_horizon_factor_pair_gcd_dvd_three h

example {s₀ C₀ r₁ C₁ r₂ C₂ r₃ C₃ e f : Nat}
    (hstep₁ : IsMovingHorizonStep s₀ C₀ r₁ C₁)
    (hstep₂ : IsMovingHorizonStep r₁ C₁ r₂ C₂)
    (hstep₃ : IsMovingHorizonStep r₂ C₂ r₃ C₃)
    (he₁ : d r₁ = e) (he₂ : d r₂ = f) (he₃ : d r₃ = e)
    (hpar : r₁ % 2 = r₃ % 2) :
    e ∣ f - 2 ∧ e + 2 ≤ f :=
  moving_horizon_aba_ascent hstep₁ hstep₂ hstep₃ he₁ he₂ he₃ hpar

-- The genuine M=13 odd factor pair is (e,u,v)=(5,3,5).
example :
    IsMovingHorizonStep 15 24 17 28 ∧
      15 = 5 * 3 ∧ 25 = 5 * 5 ∧ Nat.gcd 3 5 = 1 ∧
      (5 - 3) % 2 = 0 ∧ 2 ≤ 5 - 3 ∧ 30 = 5 * (5 + 1) := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide⟩
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · simp [IsMovingHorizonState, D, a]
  · intro j hsj hjr
    have hj : j = 16 := by omega
    subst j
    decide
  · simp [IsMovingHorizonState, D, a]

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q)
    (hq : 1 ≤ q) :
    ∃ e h, e = d sf ∧ 3 ≤ e ∧ e ≤ M ∧
      ((sf % 2 = 0 ∧ e ∣ sf ∧ e ∣ Cf ∧
          Cf - sf = e * h ∧ h % 2 = 0 ∧ 2 ≤ h) ∨
        (sf % 2 = 1 ∧ e ∣ sf - 2 ∧ e ∣ Cf + 2 ∧
          Cf - sf + 4 = e * h ∧ h % 2 = 1 ∧ 3 ≤ h)) :=
  moving_horizon_capped_old_path_endpoint_slack hpath hq

example {M s C sf Cf E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M s C sf Cf E T q)
    (hq : 1 ≤ q) :
    ∃ e h, e = d sf ∧ 3 ≤ e ∧ e ≤ M ∧ Cf - sf ≤ M ∧
      ((sf % 2 = 0 ∧ e ∣ sf ∧ e ∣ Cf ∧
          Cf - sf = e * h ∧ h % 2 = 0 ∧ 2 ≤ h ∧
          2 * e ≤ Cf - sf ∧ 2 * e ≤ M) ∨
        (sf % 2 = 1 ∧ e ∣ sf - 2 ∧ e ∣ Cf + 2 ∧
          Cf - sf + 4 = e * h ∧ h % 2 = 1 ∧ 3 ≤ h ∧
          3 * e ≤ Cf - sf + 4 ∧ 3 * e ≤ M + 4)) :=
  moving_horizon_capped_old_path_endpoint_slack_bounds hpath hq

example {M s C E T q : Nat}
    (hpath : HasMovingHorizonCappedOldPath M (M + 2) (2 * M - 2)
      s C E T q) :
    (q = 0 ∧ s = M + 2 ∧ C = 2 * M - 2) ∨
      (1 ≤ q ∧
        ∃ e h, e = d s ∧ 3 ≤ e ∧ e ≤ M ∧
          ((s % 2 = 0 ∧ e ∣ s ∧ e ∣ C ∧
              C - s = e * h ∧ h % 2 = 0 ∧ 2 ≤ h) ∨
            (s % 2 = 1 ∧ e ∣ s - 2 ∧ e ∣ C + 2 ∧
              C - s + 4 = e * h ∧ h % 2 = 1 ∧ 3 ≤ h))) :=
  moving_horizon_canonical_endpoint_slack_or_zero hpath

example : ¬ ∃ E T q,
    HasMovingHorizonCappedOldPath 9 11 16 41 50 E T q :=
  moving_horizon_no_canonical_prefix_A

example : ¬ ∃ E T q,
    HasMovingHorizonCappedOldPath 13 15 24 33 46 E T q :=
  moving_horizon_no_canonical_prefix_B

example : ¬ ∃ E T q,
    HasMovingHorizonCappedOldPath 19 21 36 50 66 E T q :=
  moving_horizon_no_canonical_prefix_C

example
    {M s₀ C₀ r₁ C₁ r₂ C₂ r₃ C₃ E T q e : Nat}
    (hstep₁ : IsMovingHorizonStep s₀ C₀ r₁ C₁)
    (hmid : HasMovingHorizonCappedOldPath M r₁ C₁ r₂ C₂ E T q)
    (hstep₂ : IsMovingHorizonStep r₂ C₂ r₃ C₃)
    (he₁ : d r₁ = e) (he₂ : d r₃ = e)
    (hpar : r₁ % 2 = r₃ % 2) (hq : 1 ≤ q) :
    e ∣ E - q - 1 ∧ e + q + 1 ≤ E :=
  moving_horizon_same_parity_return_ledger
    hstep₁ hmid hstep₂ he₁ he₂ hpar hq

-- Smallest bounded abstract grammar survivor for the strict middle-event
-- ascent candidate; this is not a recurrence path or a Lean path witness.
example :
    (65 - 2 = 7 * 9 ∧ 118 + 1 = 7 * 17 ∧ Nat.gcd 9 17 = 1 ∧
      (17 - 9) % 2 = 0 ∧ 2 ≤ 17 - 9 ∧
      124 + 2 = 7 * (17 + 1) ∧ 124 - 65 + 4 = 7 * (17 - 9 + 1)) ∧
    (66 = 3 * 22 ∧ 124 - 1 = 3 * 41 ∧ Nat.gcd 22 41 = 1 ∧
      (41 - 22) % 2 = 1 ∧ 1 ≤ 41 - 22 ∧
      126 = 3 * (41 + 1) ∧ 126 - 66 = 3 * (41 - 22 + 1)) ∧
    (70 = 5 * 14 ∧ 126 - 1 = 5 * 25 ∧ Nat.gcd 14 25 = 1 ∧
      (25 - 14) % 2 = 1 ∧ 1 ≤ 25 - 14 ∧
      130 = 5 * (25 + 1) ∧ 130 - 70 = 5 * (25 - 14 + 1)) ∧
    (72 = 3 * 24 ∧ 130 - 1 = 3 * 43 ∧ Nat.gcd 24 43 = 1 ∧
      (43 - 24) % 2 = 1 ∧ 1 ≤ 43 - 24 ∧
      132 = 3 * (43 + 1) ∧ 132 - 72 = 3 * (43 - 24 + 1)) ∧
    (79 - 2 = 7 * 11 ∧ 132 + 1 = 7 * 19 ∧ Nat.gcd 11 19 = 1 ∧
      (19 - 11) % 2 = 0 ∧ 2 ≤ 19 - 11 ∧
      138 + 2 = 7 * (19 + 1) ∧ 138 - 79 + 4 = 7 * (19 - 11 + 1)) ∧
    (7 ∣ 11 - 3 - 1 ∧ 7 + 3 + 1 ≤ 11 ∧
      ¬ (3 > 7 ∨ 5 > 7 ∨ 3 > 7)) := by decide

example {e f : Nat} (h : e ∣ f - 1 - 1) : e ∣ f - 2 := by
  omega

example {s C r C' u U' : Nat}
    (hstep₁ : IsMovingHorizonStep s C r C')
    (hstep₂ : IsMovingHorizonStep s C u U') :
    r = u ∧ C' = U' :=
  moving_horizon_step_unique hstep₁ hstep₂

example
    {M s C sf₁ Cf₁ E₁ T₁ sf₂ Cf₂ E₂ T₂ q : Nat}
    (hpath₁ : HasMovingHorizonCappedOldPath M s C sf₁ Cf₁ E₁ T₁ q)
    (hpath₂ : HasMovingHorizonCappedOldPath M s C sf₂ Cf₂ E₂ T₂ q) :
    sf₁ = sf₂ ∧ Cf₁ = Cf₂ ∧ E₁ = E₂ ∧ T₁ = T₂ :=
  moving_horizon_capped_old_path_unique hpath₁ hpath₂

-- The genuine M=13 first event passes the canonical offset sieve.
example :
    (17 % 2 = 0 ∧ 2 % 2 = 1 ∧ 5 ∣ 2 * 2 + 7) ∨
      (17 % 2 = 1 ∧ 2 % 2 = 0 ∧ 5 ∣ 2 * 2 + 1) := by
  apply moving_horizon_canonical_first_event_offset_sieve
    (M := 13) (t := 2) (r := 17) (C' := 28) (e := 5)
  · decide
  · decide
  · decide
  · refine ⟨?_, by decide, by decide, by decide, ?_, by decide,
      by decide, by decide, ?_⟩
    · simp [IsMovingHorizonState, D, a]
    · intro j hsj hjr
      have hj : j = 16 := by omega
      subst j
      decide
    · simp [IsMovingHorizonState, D, a]
  · decide

-- An even value above 5 cannot be an attained previous record.
example : ¬ ∃ k : Nat, IsAttainedPreviousMaximum 60 k := by
  intro h
  rcases h with ⟨k, hP⟩
  exact no_even_attained_previous_maximum hP (by decide) (by decide)

-- Positive control for the proposed fundamental-predecessor chain.
example :
    B 12 = 2 ∧ B 13 = 1 ∧ B 14 = 0 ∧ d 13 = 1 ∧ d 14 = 1 ∧
      d 15 = 13 ∧ B 15 + 2 = 13 := by decide

example :
    B (13 - 1) = 2 ∧ B 13 = 1 ∧ B (13 + 1) = 0 ∧
      d (13 + 1) = 1 ∧ d 13 = 1 ∧ d (13 + 2) = 13 ∧
      B (13 + 2) + 2 = 13 := by
  exact canonical_record_fundamental_predecessor
    (M := 13) (by decide) (by decide) (by decide) (by decide) (by decide)

-- No fundamental state can occur between the canonical previous record and
-- the actual critical edge.  This is the first replay-extraction gate.
theorem attempt_no_fundamental_before_final {k M : Nat} (hk : 2 ≤ k) (hM5 : 5 < M)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1)) :
    ∀ m : Nat, M + 2 ≤ m → m < k + 1 → B m ≠ 2 := by
  intro m hm hmk hfund
  have hm2 : 2 ≤ m := by omega
  rcases critical_even_quotient_normal_form hk hIH hnew hfail with
    ⟨c, hc, hcmod, hc2, hak, hD, _, _⟩
  rcases fundamental_reset hm2 hfund with hleft | hright
  · rcases hleft with ⟨hd1, hd2, hB2, hdreset, hBreset⟩
    have hDreset : D (m + 3) = 2 * (m + 1) - 2 := by
      have hrel := B_add_index_eq_D_add_two (n := m + 3) (by omega)
      omega
    by_cases hbefore : m + 3 < k + 1
    · have hcap := hP.1 (m + 3) (by omega) (by omega)
      rw [hdreset] at hcap
      omega
    · by_cases heq : m + 3 = k + 1
      · have hdelta : d (k + 1) = m + 1 := by
          simpa [heq] using hdreset
        have hDreset' : D (k + 1) = 2 * (m + 1) - 2 := by
          simpa [heq] using hDreset
        have hfour : 4 * d (k + 1) ≤ D (k + 1) := by
          rw [hD]
          have hmul := Nat.mul_le_mul_left (d (k + 1)) (show 4 ≤ c + 2 by omega)
          simpa [Nat.mul_comm] using hmul
        rw [hdelta, hDreset'] at hfour
        omega
      · have hafter : k + 1 < m + 3 := by omega
        have hcases : k + 1 = m + 1 ∨ k + 1 = m + 2 := by omega
        rcases hcases with hcase | hcase
        · rw [hcase, hd1] at hnew
          omega
        · rw [hcase, hd2] at hnew
          omega
  · rcases hright with
      ⟨hd1, hd3, hB2, hd4, hd5, hB4, hdreset, hBreset⟩
    have hDreset : D (m + 5) = 2 * (m + 3) - 2 := by
      have hrel := B_add_index_eq_D_add_two (n := m + 5) (by omega)
      omega
    by_cases hbefore : m + 5 < k + 1
    · have hcap := hP.1 (m + 5) (by omega) (by omega)
      rw [hdreset] at hcap
      omega
    · by_cases heq : m + 5 = k + 1
      · have hdelta : d (k + 1) = m + 3 := by
          simpa [heq] using hdreset
        have hDreset' : D (k + 1) = 2 * (m + 3) - 2 := by
          simpa [heq] using hDreset
        have hfour : 4 * d (k + 1) ≤ D (k + 1) := by
          rw [hD]
          have hmul := Nat.mul_le_mul_left (d (k + 1)) (show 4 ≤ c + 2 by omega)
          simpa [Nat.mul_comm] using hmul
        rw [hdelta, hDreset'] at hfour
        omega
      · have hafter : k + 1 < m + 5 := by omega
        have hcases : k + 1 = m + 1 ∨ k + 1 = m + 2 ∨
            k + 1 = m + 3 ∨ k + 1 = m + 4 := by omega
        rcases hcases with hcase | hcase | hcase | hcase
        · rw [hcase, hd1] at hnew
          omega
        · rw [hcase, hd3] at hnew
          omega
        · rw [hcase, hd4] at hnew
          omega
        · rw [hcase, hd5] at hnew
          omega

-- An actual moving-horizon state before the critical edge always has a next
-- first-hit event at or before that edge.
example {k M s C : Nat} (hk : 2 ≤ k) (hM5 : 5 < M)
    (hP : IsAttainedPreviousMaximum M k)
    (hIH : B k + 2 ≤ 2 * M) (hnew : M < d (k + 1))
    (hfail : ¬ B (k + 1) + 2 ≤ 2 * d (k + 1))
    (hstate : IsMovingHorizonState s C)
    (hs : M + 2 ≤ s) (hsfinal : s < k + 1) :
    ∃ r C', IsMovingHorizonStep s C r C' ∧ r ≤ k + 1 := by
  rcases moving_horizon_dichotomy hstate with hno | hstep
  · have htel := moving_horizon_no_event_telescope hstate hno
    rcases htel with ⟨hDC, hBCtel⟩
    have hBC : B C = 2 := by
      have hrel := B_add_index_eq_D_add_two hstate.1
      have hcoord := moving_horizon_slack_coordinate hstate
      omega
    by_cases hCfinal : C < k + 1
    · have hsc : s < C := hstate.2.2
      have hMC : M + 2 ≤ C := by omega
      exact False.elim
        (attempt_no_fundamental_before_final hk hM5 hP hIH hnew hfail
          C hMC hCfinal hBC)
    · have hCge : k + 1 ≤ C := Nat.le_of_not_gt hCfinal
      have hbad := hno (k + 1) (by omega) hCge
      omega
  · rcases hstep with ⟨r, C', hstep⟩
    rcases hstep with
      ⟨hstate', hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hstateR⟩
    refine ⟨r, C', ⟨hstate', hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hstateR⟩, ?_⟩
    by_cases hle : r ≤ k + 1
    · exact hle
    · have hfinal_lt : k + 1 < r := Nat.lt_of_not_ge hle
      have hunit := hfirst (k + 1) (by omega) hfinal_lt
      omega

-- The final predecessor is dangerous once the transported B-envelope is
-- combined with the critical short-tail inequality.
example {k M delta sf Cf c : Nat} (hM5 : 5 < M)
    (hBenv : B sf + 2 ≤ 2 * M) (hModd : M % 2 = 1)
    (hnew : M < delta)
    (hstep : IsMovingHorizonStep sf Cf (k + 1) (D (k + 1)))
    (hcrit : d (k + 1) = delta ∧ k + 1 = delta * c ∧
      c % 2 = 0 ∧ 2 ≤ c ∧ D (k + 1) = delta * (c + 2)) :
    M < Cf - sf := by
  rcases Nat.exists_eq_add_of_le hBenv with ⟨Y, hY⟩
  have hYs : B sf + 2 + Y = 2 * M := hY.symm
  have hshort := moving_horizon_critical_short_tail hstep hYs hModd hnew hcrit
  have hcoord := moving_horizon_slack_coordinate hstep.1
  omega

-- A genuine replay can leave and later re-enter the capped band; the single
-- terminal-suffix package therefore needs an additional no-reentry argument.
example :
    IsMovingHorizonStep 48 90 51 96 ∧
      IsMovingHorizonStep 51 96 60 100 ∧
      IsMovingHorizonStep 60 100 66 132 ∧
      90 - 48 ≤ 43 ∧ 43 < 96 - 51 ∧
      100 - 60 ≤ 43 ∧ 43 < 132 - 66 := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · refine ⟨by simp [IsMovingHorizonState, D, a], by decide, by decide,
      by decide, ?_, by decide, by decide, by decide,
      by simp [IsMovingHorizonState, D, a]⟩
    intro j hsj hjr
    have hj : j = 49 ∨ j = 50 := by omega
    rcases hj with rfl | rfl <;> decide
  · refine ⟨by simp [IsMovingHorizonState, D, a], by decide, by decide,
      by decide, ?_, by decide, by decide, by decide,
      by simp [IsMovingHorizonState, D, a]⟩
    intro j hsj hjr
    have hj : j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨
        j = 57 ∨ j = 58 ∨ j = 59 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨by simp [IsMovingHorizonState, D, a], by decide, by decide,
      by decide, ?_, by decide, by decide, by decide,
      by simp [IsMovingHorizonState, D, a]⟩
    intro j hsj hjr
    have hj : j = 61 ∨ j = 62 ∨ j = 63 ∨ j = 64 ∨ j = 65 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide

end A166944Research
