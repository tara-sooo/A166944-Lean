import A166944.TravelMod210

/-!
# Signed separating-event balances

Keep the negative as well as positive part of the residue-potential
balance. Only the supported sum is discarded in the crossing bound.
-/

namespace A166944Research

def signedStepBalance210 (seen : List Nat) (s C r C' : Nat) : Int :=
  (shortOrReusedTravelExcess seen (r - s) (d r) : Int) + (supportedPotential210 r C' : Int) -
    (supportedPotential210 s C : Int) - 2 * ((d r - 1 : Nat) : Int)

theorem signed_step_balance210_nonpos_of_supported {s C r C' : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C') (hdiv : d r ∣ 210) :
    signedStepBalance210 seen s C r C' ≤ 0 := by
  have h := (moving_horizon_supported210_step_budgets (seen := seen) hstep hdiv).2
  unfold signedStepBalance210
  omega

theorem signed_step_balance210_le_of_zero_excess {s C r C' : Nat} {seen : List Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hzero : shortOrReusedTravelExcess seen (r - s) (d r) = 0) :
    signedStepBalance210 seen s C r C' ≤ 1260 - 2 * ((d r - 1 : Nat) : Int) := by
  have hstate := hstep.2.2.2.2.2.2.2.2
  have hce : C' % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hV := (supported_excess_and_potential210_bounds r C' hce).2
  unfold signedStepBalance210
  omega

theorem separator_charge210_eq_signed_positive_part (seen : List Nat) (s C r C' : Nat) :
    separatorCharge210 seen s C r C' =
      (if d r ∣ 210 then (0 : Int) else signedStepBalance210 seen s C r C').toNat := by
  by_cases hdiv : d r ∣ 210
  · simp [separatorCharge210, hdiv]
  · simp only [separatorCharge210, signedStepBalance210, if_neg hdiv]
    omega

def HasMovingHorizonSignedBalances210 (s C sf Cf : Nat) (seen : List Nat) : Nat → Int → Int → Prop
  | 0, supported, separators => HasMovingHorizonPathTo s C sf Cf 0 ∧ supported = 0 ∧ separators = 0
  | q + 1, supported, separators =>
      ∃ r C' tailSupported tailSeparators, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonSignedBalances210 r C' sf Cf (d r :: seen) q tailSupported tailSeparators ∧
        supported = (if d r ∣ 210 then signedStepBalance210 seen s C r C' else 0) + tailSupported ∧
        separators = (if d r ∣ 210 then 0 else signedStepBalance210 seen s C r C') + tailSeparators

/-- The two signed sums account exactly for the excess, growth and
change in potential. Supported events have nonpositive total balance. -/
theorem moving_horizon_excess_signed_balances210 {s C sf Cf q remaining excess : Nat} {seen : List Nat}
    (hledger : HasMovingHorizonTravelExcess s C sf Cf seen q remaining excess) :
    ∃ supported separators : Int,
      HasMovingHorizonSignedBalances210 s C sf Cf seen q supported separators ∧ supported ≤ 0 ∧
      (excess : Int) + (supportedPotential210 sf Cf : Int) =
        2 * ((Cf : Int) - (C : Int)) + (supportedPotential210 s C : Int) + supported + separators := by
  induction q generalizing s C seen remaining excess with
  | zero =>
    obtain ⟨⟨rfl, rfl, hstate⟩, _, rfl⟩ := hledger
    exact ⟨0, 0, ⟨⟨rfl, rfl, hstate⟩, rfl, rfl⟩, by omega, by omega⟩
  | succ q ih =>
    obtain ⟨r, C', rest, tailExcess, hstep, htail, _, hexcess⟩ := hledger
    obtain ⟨supp, sep, hcost, hnonpos, hsum⟩ := ih htail
    have hup := moving_horizon_step_update hstep
    let bal := signedStepBalance210 seen s C r C'
    have hb : bal = (shortOrReusedTravelExcess seen (r - s) (d r) : Int) +
        (supportedPotential210 r C' : Int) - (supportedPotential210 s C : Int) -
        2 * ((d r - 1 : Nat) : Int) := rfl
    by_cases hdiv : d r ∣ 210
    · have hbneg : bal ≤ 0 := signed_step_balance210_nonpos_of_supported hstep hdiv
      refine ⟨bal + supp, sep, ⟨r, C', supp, sep, hstep, hcost, ?_, ?_⟩, ?_, ?_⟩
      · simp only [if_pos hdiv, bal]
      · simp only [if_pos hdiv, Int.zero_add]
      · omega
      · omega
    · refine ⟨supp, bal + sep, ⟨r, C', supp, sep, hstep, hcost, ?_, ?_⟩, hnonpos, ?_⟩
      · simp only [if_neg hdiv, Int.zero_add]
      · simp only [if_neg hdiv, bal]
      · omega

theorem canonical_first_crossing_requires_signed_separators210 {M sf Cf q : Nat}
    (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ (s C r C' p first : Nat) (supported separators : Int),
      HasMovingHorizonFirstUseTravel (M + 2) (2 * M - 2) s C [] p first ∧
      HasMovingHorizonSignedBalances210 (M + 2) (2 * M - 2) s C [] p supported separators ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      ((12 * M + supportedPotential210 s C : Nat) : Int) <
        ((24 * (first + (r - s)) + 11 * (C - (2 * M - 2)) +
          supportedPotential210 (M + 2) (2 * M - 2) : Nat) : Int) + separators ∧
      (M : Int) < ((24 * (first + (r - s)) + 1315 : Nat) : Int) + separators := by
  obtain ⟨s, C, r, C', p, _, first, _, hledger, _, hfirst, hstep, hr, hp,
    hshort, hcross, hG, hg, hdist⟩ := canonical_first_travel_crossing_excess hcanon hpath hlong
  obtain ⟨supp, sep, hbalances, hnonpos, hsum⟩ := moving_horizon_excess_signed_balances210 hledger
  have hGlo := (moving_horizon_travel_excess_bounds hledger).2.1
  have hV := (supported_excess_and_potential210_bounds (M + 2) (2 * M - 2) (by omega)).2
  exact ⟨s, C, r, C', p, first, supp, sep, hfirst, hbalances, hstep, hr, hp, hshort, hcross, hg,
    by omega, by omega⟩

end A166944Research
