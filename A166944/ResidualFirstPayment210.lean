import A166944.ResidualRebalancedCosts210

/-! # An explicit cutoff bound for the capped first payments -/

open Finset

namespace A166944Research

namespace ResidualPhaseEvent210

theorem first_phase_of_positive_capped_payment (event : ResidualPhaseEvent210)
    (positive : 0 < event.cappedFirstPayment) :
    IsFirstLongPrimePhase residualHorizonPhase210 event.seen event.start event.horizon event.hit := by
  have hle := min_le_left (24 * event.scaledFirstGap) event.rebalancedNetCost.toNat
  change event.cappedFirstPayment ≤ _ at hle
  have h : 0 < event.scaledFirstGap := by omega
  unfold scaledFirstGap at h
  split at h
  · omega
  · unfold firstGap firstLongPrimePhaseGap at h
    split at h
    · assumption
    · omega

theorem capped_first_payment_le_increment (event : ResidualPhaseEvent210) :
    event.cappedFirstPayment ≤ min (48 * d event.hit) (37 * d event.hit + 1047) := by
  refine Nat.le_min.mpr ⟨?_, ?_⟩
  · have hp := event.capped_first_payment_le_cofactor
    let e := d event.hit
    let g := min (2 * e) (2 * (event.horizon + 1) / e)
    change event.cappedFirstPayment ≤ min (24 * g) (24 * g + 1036 - 11 * (e - 1)) at hp
    have hg : g ≤ 2 * e := min_le_left _ _
    change event.cappedFirstPayment ≤ 48 * e
    exact (hp.trans (min_le_left _ _)).trans (by omega)
  · exact (min_le_right _ _).trans event.rebalanced_net_cost_positive_part_le

private theorem capped_first_payment_large_weighted (event : ResidualPhaseEvent210) {L U : Nat}
    (large : L < d event.hit) (horizon : event.horizon ≤ U) :
    (L * (L + 1)) * event.cappedFirstPayment ≤
      (48 * (U + 1) + 1036 * (L + 1) - 11 * (L * (L + 1))) * (d event.hit - 1) := by
  let W := L * (L + 1)
  let g := d event.hit - 1
  let gap := event.hit - event.start
  have hu := moving_horizon_step_update event.step
  have hgap := moving_horizon_large_increment_gap event.step large horizon
  rw [hu, Nat.add_sub_cancel_left] at hgap
  have hg : W * gap ≤ 2 * (U + 1) * g := hgap
  have hfirst : W * (24 * gap) ≤ 48 * (U + 1) * g := by
    calc
      _ = 24 * (W * gap) := by ac_rfl
      _ ≤ 24 * (2 * (U + 1) * g) := Nat.mul_le_mul_left 24 hg
      _ = _ := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  have hL : L ≤ g := by unfold g; omega
  have hpot : W * 1036 ≤ (1036 * (L + 1)) * g := by
    calc
      _ = (1036 * (L + 1)) * L := by unfold W; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ hL
  have hp : event.cappedFirstPayment ≤ 24 * gap + 1036 - 11 * g := event.capped_first_payment_le_gap_cost
  change W * event.cappedFirstPayment ≤ (48 * (U + 1) + 1036 * (L + 1) - 11 * W) * g
  calc
    _ ≤ W * (24 * gap + 1036 - 11 * g) := Nat.mul_le_mul_left W hp
    _ = W * (24 * gap) + W * 1036 - W * (11 * g) := by rw [Nat.mul_sub, Nat.mul_add]
    _ ≤ 48 * (U + 1) * g + (1036 * (L + 1)) * g - W * (11 * g) :=
      Nat.sub_le_sub_right (Nat.add_le_add hfirst hpot) _
    _ = _ := by rw [Nat.sub_mul, Nat.add_mul]; congr 1; ac_rfl

end ResidualPhaseEvent210

def firstPaymentCutoffBound210 (L U growth : Nat) : Nat :=
  210 * (∑ p ∈ Nat.primesLE L, min (48 * p) (37 * p + 1047)) +
    ((48 * (U + 1) + 1036 * (L + 1) - 11 * (L * (L + 1))) * growth) / (L * (L + 1))

namespace ResidualPhaseTrace210

variable {s sf n first : Nat} {balance : Int}
variable (trace : ResidualPhaseTrace210 s sf [] n first balance)

theorem sum_horizon_growth_of_delta210
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    (∑ i, (d (trace.event i).hit - 1)) = D sf - D s := by
  have h : (∑ i, ((d (trace.event i).hit - 1 : Nat) : Int)) = (D sf : Int) - D s := by
    rw [← delta (fun x => (D x : Int))]
    apply Finset.sum_congr rfl
    intro i _
    have hup := moving_horizon_step_update (trace.event i).step
    have hs := (trace.event i).step.1.2.1
    have hr := (trace.event i).step.2.2.2.2.2.2.1
    change _ = (D (trace.event i).hit : Int) - D (trace.event i).start
    omega
  rw [← Nat.cast_sum] at h
  omega

/-- Low increments are counted once per reachable phase. For the tail,
the event's own growth is subtracted before allocating the remaining
cost to the total horizon growth. -/
theorem rebalanced_first_payment_bound210 (L U : Nat) (hL : 0 < L)
    (hU : ∀ i, (trace.event i).horizon ≤ U)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f sf - f s) :
    trace.totalCappedFirstPayment ≤ firstPaymentCutoffBound210 L U (D sf - D s) := by
  classical
  let payment (i : Fin n) := (trace.event i).cappedFirstPayment
  let low := univ.filter fun i : Fin n => 0 < payment i ∧ d (trace.event i).hit ≤ L
  let high := (univ : Finset (Fin n)) \ low
  let W := L * (L + 1)
  let A := 48 * (U + 1) + 1036 * (L + 1) - 11 * W
  have hphase {i : Fin n} (hi : i ∈ low) :=
    (trace.event i).first_phase_of_positive_capped_payment (Finset.mem_filter.mp hi).2.1
  have hlow : (∑ i ∈ low, payment i) ≤ 210 * (∑ p ∈ Nat.primesLE L, min (48 * p) (37 * p + 1047)) := by
    apply phase_sum_le_of_weights210 trace.event low (Nat.primesLE L) payment (fun p => min (48 * p) (37 * p + 1047))
    · intro i hi
      have hstep := (trace.event i).step.2.2.2.1
      exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hi).2.2,
        prime_of_no_proper_factor (by omega) (hphase hi).2.1⟩
    · intro i hi j hj hkey
      change (trace.event i).phaseKey = (trace.event j).phaseKey at hkey
      rcases lt_trichotomy i j with hij | h | hji
      · have hs := (trace.seen_iff j _).mpr (Or.inr ⟨i, hij, ⟨(hphase hi).1, (hphase hi).2.1⟩, hkey.symm⟩)
        exact ((hphase hj).2.2 hs).elim
      · exact h
      · have hs := (trace.seen_iff i _).mpr (Or.inr ⟨j, hji, ⟨(hphase hj).1, (hphase hj).2.1⟩, hkey⟩)
        exact ((hphase hi).2.2 hs).elim
    · intro i _
      exact (trace.event i).capped_first_payment_le_increment
  have hhigh : (∑ i ∈ high, payment i) ≤ A * (D sf - D s) / W := by
    have hW : 0 < W := Nat.mul_pos hL (by omega)
    apply (Nat.le_div_iff_mul_le hW).mpr
    rw [Nat.mul_comm (∑ i ∈ high, payment i), Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ high, A * (d (trace.event i).hit - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzero : payment i = 0
        · simp [hzero]
        · have he : L < d (trace.event i).hit := by
            by_contra h
            exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨mem_univ _, by omega, by omega⟩)
          exact (trace.event i).capped_first_payment_large_weighted he (hU i)
      _ = A * (∑ i ∈ high, (d (trace.event i).hit - 1)) := (Finset.mul_sum _ _ _).symm
      _ ≤ A * (D sf - D s) := by
        rw [← trace.sum_horizon_growth_of_delta210 delta]
        exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
  have hsplit := Finset.sum_sdiff (f := payment) (Finset.subset_univ low)
  change (∑ i ∈ high, payment i) + (∑ i ∈ low, payment i) = trace.totalCappedFirstPayment at hsplit
  change trace.totalCappedFirstPayment ≤ _ + A * (D sf - D s) / W
  omega

end ResidualPhaseTrace210

/-- The cutoff estimate can be evaluated using just the record and
endpoint horizon of a short prefix. -/
theorem rebalanced_crossing_budget_of_cutoff210 {M s C r p first L : Nat} {balance : Int}
    (hM : 50000000 ≤ M) (canonical : d (M + 2) = M)
    (ledger : HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
      (M + 2) (2 * M - 2) s C [] p first balance)
    (short : 2 * (s - (M + 2)) ≤ M) (gap : r - s ≤ Nat.sqrt (4 * (3 * M + 4)))
    (trace : ResidualPhaseTrace210 (M + 2) s [] p first balance)
    (delta : ∀ f : Nat → Int, (∑ i, (f (trace.event i).hit - f (trace.event i).start)) = f s - f (M + 2))
    (windows : trace.RebalancedGrowthWindows) (hL : 0 < L)
    (budget : 64 * (3 * firstPaymentCutoffBound210 L C (C - (2 * M - 2)) + 12166819) ≤ 61 * M) :
    (∑ i, (trace.event i).rebalancedNetCost) + (24 * (r - s) + 1091 : Nat) ≤ (M : Int) := by
  have path := residual_phase_balances210_path ledger
  have hstart : D (M + 2) = 2 * M - 2 := by
    cases p with
    | zero => exact path.2.2.2.1
    | succ _ => exact path.1.2.1
  have hend := (moving_horizon_path_endpoint path).2.1
  have hU (i : Fin p) : (trace.event i).horizon ≤ C := hend ▸ (trace.event_horizon_between i).2.le
  have hfirst := trace.rebalanced_first_payment_bound210 L C hL hU delta
  rw [hstart, hend] at hfirst
  apply rebalanced_crossing_budget_of_first_bound210 hM canonical ledger short gap trace windows
  exact (Nat.mul_le_mul_left 64 (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hfirst) _)).trans budget

/-- The original sublinear first-phase bound suffices for the capped
payments once the record is large enough. -/
theorem rebalanced_crossing_budget_of_windows_eventually210 :
    ∃ threshold : Nat, ∀ {M s C r p first : Nat} {balance : Int},
      threshold ≤ M → d (M + 2) = M →
      HasMovingHorizonResidualPhaseBalances210 residualHorizonPhase210
        (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M → r - s ≤ Nat.sqrt (4 * (3 * M + 4)) →
      ∀ trace : ResidualPhaseTrace210 (M + 2) s [] p first balance, trace.RebalancedGrowthWindows →
        (∑ i, (trace.event i).rebalancedNetCost) + (24 * (r - s) + 1091 : Nat) ≤ (M : Int) := by
  obtain ⟨B, hB⟩ := canonical_first_prime_phase_travel_sublinear 420 128 (by decide)
  refine ⟨max 50000000 B, ?_⟩
  intro M s C r p first balance hM hcanon hledger hshort hgap trace hwindows
  have h50 : 50000000 ≤ M := (le_max_left 50000000 B).trans hM
  obtain ⟨_, hphase⟩ := residual_phase_balances210_original hledger
  have hfirst : 128 * first ≤ M := hB ((le_max_right 50000000 B).trans hM) hcanon hphase hshort
  have hpayment : trace.totalCappedFirstPayment ≤ 24 * first :=
    trace.total_capped_first_payment_le.trans (Nat.mul_le_mul_left 24 trace.scaled_first_travel_le)
  have hcost : 64 * (3 * trace.totalCappedFirstPayment) ≤ 36 * M := by
    calc
      _ ≤ 64 * (3 * (24 * first)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpayment)
      _ = 36 * (128 * first) := by simp only [← Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ hfirst
  have hconstant : 64 * 12166819 ≤ 25 * M :=
    (by decide : 64 * 12166819 ≤ 25 * 50000000).trans (Nat.mul_le_mul_left 25 h50)
  apply rebalanced_crossing_budget_of_first_bound210 h50 hcanon hledger hshort hgap trace hwindows
  rw [Nat.mul_add, show 61 = 36 + 25 by decide, Nat.add_mul]
  exact Nat.add_le_add hcost hconstant

end A166944Research
