import A166944.TravelCharged210

/-!
# Residual-travel ledgers and net crossing budgets

The step cost keeps the exact residual travel after first-phase gaps
have been separated. Its ledger is no larger than the four-growth
ledger, and its net crossing budget retains negative balances.
-/

namespace A166944Research

def HasMovingHorizonResidualPhaseBalances210 {slots : Nat} (phase : Nat → Nat → Fin slots)
    (s C sf Cf : Nat) (seen : List (Nat × Fin slots)) : Nat → Nat → Int → Prop
  | 0, first, balance => HasMovingHorizonPathTo s C sf Cf 0 ∧ first = 0 ∧ balance = 0
  | q + 1, first, balance =>
      ∃ r C' tailFirst tailBalance, IsMovingHorizonStep s C r C' ∧
        HasMovingHorizonResidualPhaseBalances210 phase r C' sf Cf (recordLongPrimePhase phase seen s C r)
          q tailFirst tailBalance ∧
        first = firstLongPrimePhaseGap phase seen s C r + tailFirst ∧
        balance = residualPhaseSeparatorBalance210 phase seen s C r C' + tailBalance

theorem residual_phase_balances210_comparison {slots s C sf Cf q first : Nat} {balance : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hledger : HasMovingHorizonResidualPhaseBalances210 phase s C sf Cf seen q first balance) :
    ∃ charged : Int, HasMovingHorizonChargedPhaseBalances210 phase s C sf Cf seen q first charged ∧
      balance ≤ charged := by
  induction q generalizing s C seen first balance with
  | zero =>
    obtain ⟨hpath, hf, rfl⟩ := hledger
    exact ⟨0, ⟨hpath, hf, rfl⟩, le_refl _⟩
  | succ q ih =>
    obtain ⟨r, C', tailFirst, tailBalance, hstep, htail, hfirst, hbalance⟩ := hledger
    obtain ⟨charged, hcharged, hle⟩ := ih htail
    refine ⟨_, ⟨r, C', tailFirst, charged, hstep, hcharged, hfirst, rfl⟩, ?_⟩
    have hlocal := residual_phase_balance210_le_charged (phase := phase) (seen := seen) hstep
    omega

theorem residual_phase_balances210_original {slots s C sf Cf q first : Nat} {balance : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hledger : HasMovingHorizonResidualPhaseBalances210 phase s C sf Cf seen q first balance) :
    ∃ original : Int, HasMovingHorizonPhaseBalances210 phase s C sf Cf seen q first original := by
  obtain ⟨charged, hcharged, _⟩ := residual_phase_balances210_comparison hledger
  exact charged_phase_balances210_original hcharged

theorem residual_phase_balances210_path {slots s C sf Cf q first : Nat} {balance : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hledger : HasMovingHorizonResidualPhaseBalances210 phase s C sf Cf seen q first balance) :
    HasMovingHorizonPathTo s C sf Cf q := by
  obtain ⟨original, horiginal⟩ := residual_phase_balances210_original hledger
  exact moving_horizon_phase_balances210_path horiginal

theorem residual_phase_balances210_budget {slots s C sf Cf q first : Nat} {balance : Int}
    {phase : Nat → Nat → Fin slots} {seen : List (Nat × Fin slots)}
    (hledger : HasMovingHorizonResidualPhaseBalances210 phase s C sf Cf seen q first balance) :
    ((24 * (sf - s) + supportedPotential210 sf Cf : Nat) : Int) ≤
      ((24 * first + 11 * (Cf - C) + supportedPotential210 s C : Nat) : Int) + balance := by
  induction q generalizing s C seen first balance with
  | zero =>
    obtain ⟨⟨rfl, rfl, _⟩, rfl, rfl⟩ := hledger
    simp
  | succ q ih =>
    obtain ⟨r, C', tailFirst, tailBalance, hstep, htail, hfirst, hbalance⟩ := hledger
    have hcost := ih htail
    have hlocal := residual_phase_step_budget210 (phase := phase) (seen := seen) hstep
    have hr := hstep.2.1
    have hrf := moving_horizon_path_index_le (residual_phase_balances210_path htail)
    have hCC' := moving_horizon_step_update hstep
    have hC'f := (moving_horizon_path_gap_le_three_growth (residual_phase_balances210_path htail)).2.1
    omega

theorem moving_horizon_residual_phase_balances210 {slots s C sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (seen : List (Nat × Fin slots))
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    ∃ first : Nat, ∃ balance : Int,
      HasMovingHorizonResidualPhaseBalances210 phase s C sf Cf seen q first balance := by
  induction q generalizing s C seen with
  | zero => exact ⟨0, 0, hpath, rfl, rfl⟩
  | succ q ih =>
    obtain ⟨_, r, C', hstep, htail⟩ := hpath
    obtain ⟨first, balance, hledger⟩ := ih (recordLongPrimePhase phase seen s C r) htail
    exact ⟨_, _, r, C', first, balance, hstep, hledger, rfl, rfl⟩

theorem canonical_first_crossing_requires_residual_phase_balances210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hlong : M < 2 * (sf - (M + 2))) :
    ∃ (s C r C' p first : Nat) (balance : Int),
      HasMovingHorizonResidualPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance ∧
      IsMovingHorizonStep s C r C' ∧ r ≤ sf ∧ p + 1 ≤ q ∧
      2 * (s - (M + 2)) ≤ M ∧ M < 2 * (r - (M + 2)) ∧
      r - s ≤ Nat.sqrt (4 * (3 * M + 4)) ∧
      (M : Int) < ((24 * (first + (r - s)) + 1315 : Nat) : Int) + balance := by
  obtain ⟨s, C, r, C', p, _, _, _, hledger, _, hfirst, hstep, hr, hp, hshort, hcross, hG, hg, _⟩ :=
    canonical_first_travel_crossing_excess hcanon hpath hlong
  obtain ⟨first, balance, hphase⟩ :=
    moving_horizon_residual_phase_balances210 phase [] (moving_horizon_first_use_travel_path hfirst)
  have hcost := residual_phase_balances210_budget hphase
  have hV := (supported_excess_and_potential210_bounds (M + 2) (2 * M - 2) (by omega)).2
  have hsf := (moving_horizon_travel_excess_bounds hledger).1
  have hsr := hstep.2.1
  exact ⟨s, C, r, C', p, first, balance, hphase, hstep, hr, hp, hshort, hcross, hg, by omega⟩

/-- Control the combined first-gap and signed-balance term, preserving
their cancellation rather than bounding each term separately. -/
theorem canonical_travel_of_residual_net_budget210 {slots M sf Cf q : Nat}
    (phase : Nat → Nat → Fin slots) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf q)
    (hbudget : ∀ {s C p first : Nat} {balance : Int},
      HasMovingHorizonResidualPhaseBalances210 phase (M + 2) (2 * M - 2) s C [] p first balance →
      2 * (s - (M + 2)) ≤ M →
      ((24 * (first + Nat.sqrt (4 * (3 * M + 4))) + 1315 : Nat) : Int) + balance ≤ M) :
    2 * (sf - (M + 2)) ≤ M := by
  by_cases hshort : 2 * (sf - (M + 2)) ≤ M
  · exact hshort
  · obtain ⟨s, C, r, C', p, first, balance, hphase, _, _, _, hs, _, hgap, hcross⟩ :=
      canonical_first_crossing_requires_residual_phase_balances210 phase hcanon hpath (by omega)
    have hle := hbudget hphase hs
    omega

end A166944Research
