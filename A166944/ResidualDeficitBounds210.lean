import A166944.ResidualIntervals210

/-! # Size and recurrence constraints of a residual deficient window -/

open Finset

namespace A166944Research.ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

def MinimalDeficit (a b : Nat) : Prop :=
  a ≤ b ∧ trace.Deficit a b ∧
    ∀ a' b', a ≤ a' → a' ≤ b' → b' ≤ b → (a < a' ∨ b' < b) → ¬ trace.Deficit a' b'

theorem minimal_deficit_of_not_windows (failure : ¬ trace.Windows) :
    ∃ a b, trace.MinimalDeficit a b :=
  credit_minimal_deficit_window210 trace.left_le_right
    (fun hall => failure (credit_windows_of_hall210 hall))

theorem minimal_deficit_cut {a b t : Nat} (minimal : trace.MinimalDeficit a b)
    (hat : a ≤ t) (htb : t < b) :
    ∃ (i : Fin n) (positive : 0 < trace.demand i), a ≤ trace.left i ∧ trace.right i ≤ b ∧
      trace.left i ≤ t ∧ t < trace.right i ∧ (trace.reuse i positive).Constraints := by
  obtain ⟨i, hmem, hpos, hl, hr⟩ := minimal_credit_deficit_crosses_every_cut210
    trace.left_le_right minimal.2.1 minimal.2.2 t hat htb
  have hwindow := (Finset.mem_filter.mp hmem).2
  exact ⟨i, hpos, hwindow.1, hwindow.2, hl, hr, same_phase_credit_interval_constraints210 _⟩

theorem hit_strict_mono : StrictMono (fun i : Fin n => (trace.event i).hit) := by
  intro i j hij
  exact (trace.ordered hij).trans_lt (trace.event j).step.2.1

theorem eligible_iff_event_interval (i j : Fin n) :
    trace.Eligible i j ↔ trace.anchor i < j ∧ j ≤ i := by
  have hlt : (trace.event (trace.anchor i)).hit < (trace.event j).hit ↔ trace.anchor i < j :=
    trace.hit_strict_mono.lt_iff_lt
  have hle : (trace.event j).hit ≤ (trace.event i).hit ↔ j ≤ i :=
    trace.hit_strict_mono.le_iff_le
  rw [← hlt, ← hle]
  unfold Eligible left right time
  omega

theorem minimal_deficit_event_endpoints {a b : Nat} (minimal : trace.MinimalDeficit a b) :
    ∃ i j : Fin n, i < j ∧ a = trace.right i ∧ b = trace.right j := by
  obtain ⟨⟨i, hi, hpos, hleft⟩, ⟨j, _, _, hright⟩⟩ :=
    minimal_credit_deficit_has_boundary_requests210 trace.left_le_right
      minimal.1 minimal.2.1 minimal.2.2
  have hb := (Finset.mem_filter.mp hi).2.2
  have hlt : (trace.event (trace.anchor i)).hit < (trace.event i).hit :=
    trace.hit_strict_mono (trace.demand_anchor_lt_key hpos).1
  refine ⟨trace.anchor i, j, ?_, hleft.symm, hright.symm⟩
  by_contra h
  have hle : (trace.event j).hit ≤ (trace.event (trace.anchor i)).hit :=
    trace.hit_strict_mono.monotone (le_of_not_gt h)
  unfold left at hleft
  unfold right at hright hb
  omega

private theorem unsupported_period_ge_630 {e : Nat} (he : 0 < e) (h : ¬ e ∣ 210) :
    630 ≤ Nat.lcm 210 (2 * e) := by
  have hpos := Nat.lcm_pos (by decide : 0 < 210) (by omega : 0 < 2 * e)
  obtain ⟨k, hk⟩ := Nat.dvd_lcm_left 210 (2 * e)
  have hd := Nat.dvd_lcm_right 210 (2 * e)
  by_contra hs
  have hcases : Nat.lcm 210 (2 * e) = 210 ∨ Nat.lcm 210 (2 * e) = 420 := by omega
  have h420 : 2 * e ∣ 420 := by
    rcases hcases with h210 | h420
    · exact (h210 ▸ hd).trans (by decide : 210 ∣ 420)
    · exact h420 ▸ hd
  exact h (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h420)

theorem demand_horizon_span {i : Fin n} (hpos : 0 < trace.demand i) :
    630 ≤ (trace.event i).horizon - (trace.event (trace.anchor i)).horizon := by
  let reuse := trace.reuse i hpos
  have hstep := reuse.earlier.2.2.2.1
  have hn := (trace.event i).positive_unsupported (trace.demand_positive_cost hpos)
  have hunsupported : ¬ d reuse.r ∣ 210 := by
    rw [reuse.same_increment]
    exact hn
  exact (unsupported_period_ge_630 (by omega) hunsupported).trans
    (same_phase_credit_interval_constraints210 reuse).2.2.1

theorem consecutive_horizon {i j : Fin n} (h : j.val = i.val + 1) :
    (trace.event j).horizon = (trace.event i).nextHorizon := by
  rw [← (trace.event j).step.1.2.1, trace.consecutive h]
  exact (trace.event i).step.2.2.2.2.2.2.1.symm

theorem demand_event_span {i : Fin n} (hpos : 0 < trace.demand i) :
    (trace.anchor i).val + 2 ≤ i.val := by
  let reuse := trace.reuse i hpos
  have hlt := (trace.demand_anchor_lt_key hpos).1
  have hperiod := (same_phase_credit_interval_constraints210 reuse).2.2.1
  have he := reuse.earlier.2.2.2.1
  have hlcm := Nat.le_of_dvd (Nat.lcm_pos (by decide : 0 < 210) (by omega : 0 < 2 * d reuse.r))
    (Nat.dvd_lcm_right 210 (2 * d reuse.r))
  by_contra hsmall
  have hnext := trace.consecutive_horizon (by omega : i.val = (trace.anchor i).val + 1)
  have hup := moving_horizon_step_update reuse.earlier
  change reuse.H = reuse.C' at hnext
  omega

theorem windows_of_small_horizon_span
    (hspan : ∀ i j, (trace.event j).horizon - (trace.event i).horizon < 630) : trace.Windows := by
  intro a b _
  have hz (i : Fin n) : trace.demand i = 0 := by
    by_contra hi
    exact (Nat.not_lt_of_ge (trace.demand_horizon_span (Nat.pos_of_ne_zero hi))) (hspan (trace.anchor i) i)
  simp [hz]

private theorem coprime_210_of_no_proper_factor {e : Nat} (he : 1 < e)
    (hprime : NoProperFactor e) (hunsupported : ¬ e ∣ 210) : Nat.Coprime 210 e := by
  let g := Nat.gcd 210 e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by decide)
  have hd : g ∣ e := Nat.gcd_dvd_right _ _
  have hle := Nat.le_of_dvd (by omega : 0 < e) hd
  have hne : g ≠ e := fun h => hunsupported (h ▸ Nat.gcd_dvd_left 210 e)
  change g = 1
  by_contra h
  have hg1 : 1 < g := by omega
  exact hprime ⟨g, lt_of_le_of_ne hle hne⟩ hg1 hd

private theorem long_prime_reuse_width (w : SamePhaseCreditInterval210)
    (hprime : NoProperFactor (d w.r)) (hunsupported : ¬ d w.r ∣ 210) :
    210 * d w.r ≤ w.H - w.C := by
  have he := w.earlier.2.2.2.1
  have ⟨_, hperiod, hspan, _⟩ := same_phase_credit_interval_constraints210 w
  have hpos := Nat.lcm_pos (by decide : 0 < 210) (by omega : 0 < 2 * d w.r)
  have hed : d w.r ∣ Nat.lcm 210 (2 * d w.r) :=
    (show d w.r ∣ 2 * d w.r from ⟨2, Nat.mul_comm _ _⟩).trans (Nat.dvd_lcm_right _ _)
  exact Nat.le_of_dvd (by omega)
    ((coprime_210_of_no_proper_factor he hprime hunsupported).mul_dvd_of_dvd_of_dvd
      ((Nat.dvd_lcm_left _ _).trans hperiod) (hed.trans hperiod))

private theorem residual_cost_le_increment (event : ResidualPhaseEvent210) (h : ¬ d event.hit ∣ 210) :
    event.cost ≤ 37 * (d event.hit : Int) + 1326 := by
  have hgap := moving_horizon_step_gap_le_twice_increment event.step
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hpotential := (supported_excess_and_potential210_bounds event.hit event.nextHorizon heven).2
  simp only [ResidualPhaseEvent210.cost, residualPhaseSeparatorBalance210, if_neg h]
  omega

private theorem large_event_credit (event : ResidualPhaseEvent210) (hlarge : 463 ≤ d event.hit)
    (hnew : ¬ (event.LongPrime ∧ event.phaseKey ∈ event.seen)) :
    event.cost ≤ 1315 - 7 * ((d event.hit - 1 : Nat) : Int) := by
  have hunsupported : ¬ d event.hit ∣ 210 := fun h => by
    have := Nat.le_of_dvd (by decide : 0 < 210) h
    omega
  have hstate := event.step.2.2.2.2.2.2.2.2
  have heven := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hpotential := (supported_excess_and_potential210_bounds event.hit event.nextHorizon heven).2
  have htravel : 24 * (event.hit - event.start - event.firstGap) ≤ 4 * (d event.hit - 1) := by
    by_cases hlong : 10 < event.hit - event.start
    · by_cases hp : NoProperFactor (d event.hit)
      · have hfirst : IsFirstLongPrimePhase residualHorizonPhase210 event.seen
            event.start event.horizon event.hit :=
          ⟨hlong, hp, fun hm => hnew ⟨⟨hlong, hp⟩, hm⟩⟩
        rw [ResidualPhaseEvent210.firstGap, firstLongPrimePhaseGap, if_pos hfirst]
        omega
      · obtain ⟨p, hp1, hpdvd, hsquare⟩ := exists_small_factor_of_composite hp
        have hgap := moving_horizon_step_gap_le_twice_increment_factor event.step hp1 hpdvd
        by_cases hsmall : p ≤ 12
        · omega
        · have hprod := (Nat.mul_le_mul_right p (by omega : 13 ≤ p)).trans hsquare
          omega
    · omega
  simp only [ResidualPhaseEvent210.cost, residualPhaseSeparatorBalance210, if_neg hunsupported]
  unfold ResidualPhaseEvent210.firstGap at htravel
  omega

private theorem one_middle_event_bounds {j k : Fin n} (positive : 0 < trace.demand j)
    (hk : k.val = (trace.anchor j).val + 1) (hj : j.val = k.val + 1) :
    463 ≤ d (trace.event k).hit ∧
      d (trace.event j).hit < d (trace.event k).hit ∧
      (trace.event j).cost ≤ 7 * ((d (trace.event k).hit - 1 : Nat) : Int) - 1315 := by
  let w := trace.reuse j positive
  let f := d (trace.event k).hit
  have hwidth := trace.demand_horizon_span positive
  change 630 ≤ w.H - w.C at hwidth
  have hdrift : w.H = w.C + (d w.r - 1) + (f - 1) := by
    change (trace.event j).horizon = (trace.event (trace.anchor j)).horizon +
      (d (trace.event (trace.anchor j)).hit - 1) + (f - 1)
    rw [trace.consecutive_horizon hj, moving_horizon_step_update (trace.event k).step,
      trace.consecutive_horizon hk, moving_horizon_step_update (trace.event (trace.anchor j)).step]
  have heq : d w.r = d (trace.event j).hit := w.same_increment
  have hpos := trace.demand_positive_cost positive
  change 463 ≤ f ∧ d (trace.event j).hit < f ∧
    (trace.event j).cost ≤ 7 * ((f - 1 : Nat) : Int) - 1315
  by_cases hlong : (trace.event j).LongPrime ∧ (trace.event j).phaseKey ∈ (trace.event j).seen
  · have hunsupported := (trace.event j).positive_unsupported hpos
    have hprime := hlong.1.2
    have hwide := long_prime_reuse_width w (heq.symm ▸ hprime) (heq.symm ▸ hunsupported)
    have hlast := residual_cost_le_increment (trace.event j) hunsupported
    have hevent := (trace.event j).step.2.2.2.1
    have hthree : 3 ≤ d (trace.event j).hit := by
      by_contra h
      have heq2 : d (trace.event j).hit = 2 := by omega
      apply hunsupported
      rw [heq2]
      decide
    omega
  · have ⟨hsmall, hcap⟩ := residual_phase_startup_bounds210 (phase := residualHorizonPhase210)
      (seen := (trace.event j).seen) (trace.event j).step
      (fun ⟨hg, hp, hs⟩ => hlong ⟨⟨hg, hp⟩, hs⟩) hpos
    change (trace.event j).cost.toNat ≤ 1478 at hcap
    omega

/-- A single intervening event pays the entire repeated request when
the middle event is composite, short, or first in its long-prime phase. -/
theorem one_middle_event_pays {j k : Fin n} (positive : 0 < trace.demand j)
    (hk : k.val = (trace.anchor j).val + 1) (hj : j.val = k.val + 1)
    (hnew : ¬ ((trace.event k).LongPrime ∧ (trace.event k).phaseKey ∈ (trace.event k).seen)) :
    trace.demand j ≤ trace.supply k := by
  have hrequired := trace.one_middle_event_bounds positive hk hj
  have hmid := large_event_credit (trace.event k) hrequired.1 hnew
  have hlast := hrequired.2.2
  rw [trace.demand_eq_cost positive]
  unfold supply
  omega

/-- In a deficient window spanning at most three events, the two
endpoints belong to the only positive request in the window. Its
middle event must be a long prime with an earlier use of its phase. -/
theorem short_deficit_middle_reused_long {i j : Fin n} (hshort : j.val ≤ i.val + 2)
    (deficit : trace.Deficit (trace.right i) (trace.right j)) :
    ∃ k : Fin n, k.val = i.val + 1 ∧ j.val = k.val + 1 ∧ 463 ≤ d (trace.event k).hit ∧
      d (trace.event i).hit < d (trace.event k).hit ∧
      (trace.event k).LongPrime ∧
      (trace.event k).phaseKey ∈ (trace.event k).seen := by
  classical
  let requests := creditWindowRequests210 trace.left trace.right (trace.right i) (trace.right j)
  let sources := creditWindowSources210 trace.time (trace.right i) (trace.right j)
  change (∑ k ∈ sources, trace.supply k) < ∑ u ∈ requests, trace.demand u at deficit
  have hrequest {u : Fin n} (hu : u ∈ requests) (hpos : 0 < trace.demand u) :
      u = j ∧ trace.anchor u = i ∧ j.val = i.val + 2 := by
    have hmem := (Finset.mem_filter.mp hu).2
    have ha : i ≤ trace.anchor u := by
      apply le_of_not_gt
      intro h
      have hhit : (trace.event (trace.anchor u)).hit < (trace.event i).hit := trace.hit_strict_mono h
      have hl := hmem.1
      unfold right left at hl
      omega
    have hb : u ≤ j := by
      apply le_of_not_gt
      intro h
      have hhit : (trace.event j).hit < (trace.event u).hit := trace.hit_strict_mono h
      have hr := hmem.2
      unfold right at hr
      omega
    have hspan := trace.demand_event_span hpos
    exact ⟨Fin.ext (by omega), Fin.ext (by omega), by omega⟩
  have hexists : ∃ u ∈ requests, 0 < trace.demand u := by
    by_contra hn
    have hz : (∑ u ∈ requests, trace.demand u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact Nat.eq_zero_of_not_pos (fun h => hn ⟨u, hu, h⟩)
    omega
  obtain ⟨u, hu, hpos⟩ := hexists
  obtain ⟨heq, hanchor, hj⟩ := hrequest hu hpos
  subst u
  let k : Fin n := ⟨i.val + 1, by have := j.isLt; omega⟩
  have hk : k.val = (trace.anchor j).val + 1 := by rw [hanchor]
  have hjk : j.val = k.val + 1 := by change _ = i.val + 1 + 1; omega
  have hsum : (∑ u ∈ requests, trace.demand u) = trace.demand j := by
    rw [Finset.sum_eq_single_of_mem j hu]
    intro u hu' hne
    exact Nat.eq_zero_of_not_pos (fun h => hne (hrequest hu' h).1)
  have hleft : (trace.event i).hit < (trace.event k).hit :=
    trace.hit_strict_mono (show i < k by change i.val < i.val + 1; omega)
  have hright : (trace.event k).hit < (trace.event j).hit :=
    trace.hit_strict_mono (show k < j by change i.val + 1 < j.val; omega)
  have hsource : k ∈ sources := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_univ _, by unfold right time; omega⟩
  have hcredit := Finset.single_le_sum (f := trace.supply) (fun _ _ => Nat.zero_le _) hsource
  obtain ⟨hsize, hinc, _⟩ := trace.one_middle_event_bounds hpos hk hjk
  have hreuse := (trace.reuse j hpos).same_increment
  change d (trace.event (trace.anchor j)).hit = d (trace.event j).hit at hreuse
  rw [hanchor] at hreuse
  refine ⟨k, rfl, hjk, hsize, hreuse ▸ hinc, ?_⟩
  by_contra hnew
  have hpaid := trace.one_middle_event_pays hpos hk hjk hnew
  omega

theorem short_deficit_requires_large_prior_drift {i j : Fin n} (hshort : j.val ≤ i.val + 2)
    (deficit : trace.Deficit (trace.right i) (trace.right j)) :
    ∃ k l : Fin n, k < i ∧ l.val = i.val + 1 ∧
      97230 ≤ (trace.event l).horizon - (trace.event k).horizon := by
  obtain ⟨l, hl, _, hsize, hinc, hlong, hseen⟩ := trace.short_deficit_middle_reused_long hshort deficit
  obtain ⟨k, hkl, _, hkey⟩ := ((trace.seen_iff l _).mp hseen).resolve_left (by simp)
  let earlier := trace.event k
  let later := trace.event l
  let w : SamePhaseCreditInterval210 := ⟨earlier.start, earlier.horizon, earlier.hit, earlier.nextHorizon,
    later.start, later.horizon, later.hit, later.nextHorizon, earlier.step, later.step,
    trace.ordered hkl, congrArg Prod.fst hkey.symm, congrArg Prod.snd hkey.symm⟩
  have hlarge : 463 ≤ d w.r := w.same_increment.symm ▸ hsize
  have hprime : NoProperFactor (d w.r) := w.same_increment.symm ▸ hlong.2
  have hunsupported : ¬ d w.r ∣ 210 := fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 210) hd
    omega
  have hspan := long_prime_reuse_width w hprime hunsupported
  have hki : k < i := by
    by_contra h
    have heq : k = i := Fin.ext (by omega)
    have hevent := congrArg Prod.fst hkey
    change d (trace.event l).hit = d (trace.event k).hit at hevent
    rw [heq] at hevent
    omega
  refine ⟨k, l, hki, hl, ?_⟩
  change 97230 ≤ w.H - w.C
  omega

end A166944Research.ResidualPhaseTrace210
