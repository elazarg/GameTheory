/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicResponseCredibilityCriterion
import GameTheory.Concepts.Stochastic.QuittingGame

/-!
# The Flesch--Thuijsman--Vrieze cyclic credibility architecture

This file instantiates the finite public-response credibility criterion on the
three-player quitting game used by Flesch, Thuijsman and Vrieze.  The public
controller has three live clock phases and one absorbing child for each
nonempty quitter set.  In live phase `c`, player `c` quits with probability
one half and the other two players continue.

The intended main result is an actual-data theorem: the concrete controller
and target satisfy the four global conditions `(T0)`, `(Ti)`, `(N)`, and
`(P)`, and therefore produce the repository's operational public-response
enforcement ledger at every positive error.  No minimality or rigidity claim
is made here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace FTVCyclicCredibility

open Math.Probability Math.PMFProduct StochasticGame

/-- The three players, also used as the three live clock phases. -/
abbrev Player := Fin 3

/-- A terminal quitter set. -/
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The seven terminal rewards of the FTV quitting game. -/
def terminalReward (S : Terminal) : Payoff Player :=
  if S.1 = {0} then ![1, 3, 0]
  else if S.1 = {1} then ![0, 1, 3]
  else if S.1 = {2} then ![3, 0, 1]
  else if S.1 = {0, 1} then ![1, 0, 1]
  else if S.1 = {0, 2} then ![0, 1, 1]
  else if S.1 = {1, 2} then ![1, 1, 0]
  else ![0, 0, 0]

@[simp] theorem terminalReward_0 (h : ({0} : Finset Player).Nonempty) :
    terminalReward ⟨{0}, h⟩ = ![1, 3, 0] := by
  simp [terminalReward]

@[simp] theorem terminalReward_1 (h : ({1} : Finset Player).Nonempty) :
    terminalReward ⟨{1}, h⟩ = ![0, 1, 3] := by
  simp [terminalReward]

@[simp] theorem terminalReward_2 (h : ({2} : Finset Player).Nonempty) :
    terminalReward ⟨{2}, h⟩ = ![3, 0, 1] := by
  simp [terminalReward]

@[simp] theorem terminalReward_01 (h : ({0, 1} : Finset Player).Nonempty) :
    terminalReward ⟨{0, 1}, h⟩ = ![1, 0, 1] := by
  simp [terminalReward, show ({0, 1} : Finset Player) ≠ {0} by decide,
    show ({0, 1} : Finset Player) ≠ {1} by decide,
    show ({0, 1} : Finset Player) ≠ {2} by decide]

@[simp] theorem terminalReward_02 (h : ({0, 2} : Finset Player).Nonempty) :
    terminalReward ⟨{0, 2}, h⟩ = ![0, 1, 1] := by
  simp [terminalReward, show ({0, 2} : Finset Player) ≠ {0} by decide,
    show ({0, 2} : Finset Player) ≠ {1} by decide,
    show ({0, 2} : Finset Player) ≠ {2} by decide,
    show ({0, 2} : Finset Player) ≠ {0, 1} by decide]

@[simp] theorem terminalReward_12 (h : ({1, 2} : Finset Player).Nonempty) :
    terminalReward ⟨{1, 2}, h⟩ = ![1, 1, 0] := by
  simp [terminalReward, show ({1, 2} : Finset Player) ≠ {0} by decide,
    show ({1, 2} : Finset Player) ≠ {1} by decide,
    show ({1, 2} : Finset Player) ≠ {2} by decide,
    show ({1, 2} : Finset Player) ≠ {0, 1} by decide,
    show ({1, 2} : Finset Player) ≠ {0, 2} by decide]

@[simp] theorem terminalReward_012
    (h : ({0, 1, 2} : Finset Player).Nonempty) :
    terminalReward ⟨{0, 1, 2}, h⟩ = ![0, 0, 0] := by
  simp [terminalReward, show ({0, 1, 2} : Finset Player) ≠ {0} by decide,
    show ({0, 1, 2} : Finset Player) ≠ {1} by decide,
    show ({0, 1, 2} : Finset Player) ≠ {2} by decide,
    show ({0, 1, 2} : Finset Player) ≠ {0, 1} by decide,
    show ({0, 1, 2} : Finset Player) ≠ {0, 2} by decide,
    show ({0, 1, 2} : Finset Player) ≠ {1, 2} by decide]

/-- The concrete FTV quitting game. -/
abbrev game : StochasticGame Player := quittingGame terminalReward

instance : Fintype game.State :=
  inferInstanceAs (Fintype (Option Terminal))

instance : DecidableEq game.State :=
  inferInstanceAs (DecidableEq (Option Terminal))

instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Bool)

instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Bool)

/-- The unique live state of the quitting game.  Naming it avoids exposing
the reducible `Option` implementation in architecture-indexed declarations. -/
def initialState : game.State := none

/-- Three live phases, followed by the seven absorbing children. -/
abbrev Config := Player ⊕ Terminal

/-- Cyclic successor on the three live phases. -/
def nextPhase : Player → Player := ![1, 2, 0]

/-- The three continuation promises `(1,2,1)`, `(1,1,2)`, `(2,1,1)`. -/
def phaseTarget : Player → Payoff Player :=
  ![![1, 2, 1], ![1, 1, 2], ![2, 1, 1]]

/-- Complete target assignment, including the absorbing children. -/
def target : Config → Payoff Player
  | Sum.inl c => phaseTarget c
  | Sum.inr S => terminalReward S

/-- Public-state projection of the controller. -/
def publicState : Config → game.State
  | Sum.inl _ => none
  | Sum.inr S => some S

/-- In live phase `c`, only player `c` mixes, uniformly, between continue and
quit.  At an absorbing child the chosen row is immaterial. -/
def play : Config → ∀ _ : Player, PMF Bool
  | Sum.inl c => fun who =>
      if who = c then PMF.uniformOfFintype Bool else PMF.pure false
  | Sum.inr _ => fun _ => PMF.pure false

/-- Total public controller update.  On live survival the clock advances; a
terminal next state selects its matching child.  The otherwise unreachable
`child → none` branch is sent to live phase zero so that the update remains
total and respects the public-state projection. -/
def step : Config → game.JointAct → game.State → Config
  | Sum.inl c, _, none => Sum.inl (nextPhase c)
  | Sum.inr _, _, none => Sum.inl 0
  | _, _, some S => Sum.inr S

/-- The ten-node FTV public response architecture. -/
abbrev architecture : game.FiniteResponseArchitecture initialState where
  Config := Config
  start := Sum.inl 0
  publicState := publicState
  play := play
  step := step
  start_publicState := rfl
  step_publicState := by
    intro z act s'
    cases z <;> cases s' <;> rfl

@[simp] theorem architecture_start : architecture.start = Sum.inl 0 := rfl

@[simp] theorem architecture_publicState (z : Config) :
    architecture.publicState z = publicState z := rfl

@[simp] theorem architecture_play (z : Config) (who : Player) :
    architecture.play z who = play z who := rfl

@[simp] theorem architecture_step (z : Config) (act : game.JointAct)
    (s' : game.State) :
    architecture.step z act s' = step z act s' := rfl

/-- Fubini expansion of a product of three Boolean mixed actions. -/
theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦ f ![a, b, c] := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a))
      1 (sigma 1) = Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
      Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext c
  have hpure : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (PMF.pure c) = fun who ↦ PMF.pure (![a, b, c] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

@[simp] theorem quitters_000 :
    ({i | ![false, false, false] i = true} : Finset Player) = ∅ := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_100 :
    ({i | ![true, false, false] i = true} : Finset Player) = {0} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_010 :
    ({i | ![false, true, false] i = true} : Finset Player) = {1} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_001 :
    ({i | ![false, false, true] i = true} : Finset Player) = {2} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_110 :
    ({i | ![true, true, false] i = true} : Finset Player) = {0, 1} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_101 :
    ({i | ![true, false, true] i = true} : Finset Player) = {0, 2} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_011 :
    ({i | ![false, true, true] i = true} : Finset Player) = {1, 2} := by
  ext i
  fin_cases i <;> simp

@[simp] theorem quitters_111 :
    ({i | ![true, true, true] i = true} : Finset Player) = {0, 1, 2} := by
  ext i
  fin_cases i <;> simp

/-- Prescribed harmonicity on the three live phases, reduced to the eight
pure quitting profiles by the preceding Fubini lemma. -/
theorem prescribed_target_live (c who : Player) :
    expect (architecture.prescribedConfigDist (Sum.inl c))
        (fun z ↦ target z who) = target (Sum.inl c) who := by
  simp only [FiniteResponseArchitecture.prescribedConfigDist,
    FiniteResponseArchitecture.prescribedActionDist, expect_bind, expect_pure]
  change expect (pmfPi (play (Sum.inl c))) (fun act ↦
      expect ((quittingGame terminalReward).transition none act) (fun s' ↦
        target (step (Sum.inl c) act s') who)) = target (Sum.inl c) who
  rw [expect_pmfPi_fin3_bool]
  fin_cases c <;> fin_cases who <;>
    simp [play, game, quittingGame, step, target, phaseTarget, nextPhase,
      terminalReward] <;> norm_num

/-- At an absorbing child, prescribed play leaves both the state and target
unchanged. -/
theorem prescribed_target_child (S : Terminal) (who : Player) :
    expect (architecture.prescribedConfigDist (Sum.inr S))
        (fun z ↦ target z who) = target (Sum.inr S) who := by
  simp [FiniteResponseArchitecture.prescribedConfigDist,
    FiniteResponseArchitecture.prescribedActionDist, architecture, game,
    quittingGame, publicState, step, target]

/-- `(T0)` for the concrete FTV controller. -/
theorem isPrescribedTargetHarmonic :
    architecture.IsPrescribedTargetHarmonic target := by
  intro who z
  cases z with
  | inl c => exact prescribed_target_live c who
  | inr S => exact prescribed_target_child S who

/-- Every pure unilateral row at a live phase has continuation target no
larger than the current target. -/
theorem unilateral_target_live (c who : Player) (act : Bool) :
    expect (architecture.nextConfigDist who (Sum.inl c) (PMF.pure act))
        (fun z ↦ target z who) ≤ target (Sum.inl c) who := by
  simp only [FiniteResponseArchitecture.nextConfigDist,
    FiniteResponseArchitecture.actionDist, expect_bind, expect_pure]
  change expect
      (pmfPi (Function.update (play (Sum.inl c)) who (PMF.pure act)))
      (fun joint ↦
        expect ((quittingGame terminalReward).transition none joint) (fun s' ↦
          target (step (Sum.inl c) joint s') who)) ≤
    target (Sum.inl c) who
  rw [expect_pmfPi_fin3_bool]
  fin_cases c <;> fin_cases who <;> cases act <;>
    simp [play, game, quittingGame, step, target, phaseTarget, nextPhase,
      terminalReward_0, terminalReward_1, terminalReward_2,
      terminalReward_01, terminalReward_02, terminalReward_12] <;> norm_num

/-- Every pure unilateral row at an absorbing child keeps its target. -/
theorem unilateral_target_child (S : Terminal) (who : Player) (act : Bool) :
    expect (architecture.nextConfigDist who (Sum.inr S) (PMF.pure act))
        (fun z ↦ target z who) = target (Sum.inr S) who := by
  simp [FiniteResponseArchitecture.nextConfigDist,
    FiniteResponseArchitecture.actionDist, architecture, game, quittingGame,
    publicState, step, target]

/-- `(Ti)` for the concrete FTV controller. -/
theorem isUnilateralTargetSuperharmonic :
    architecture.IsUnilateralTargetSuperharmonic target := by
  intro who z act
  cases z with
  | inl c => exact unilateral_target_live c who act
  | inr S => exact (unilateral_target_child S who act).le

/-- In FTV the actual one-stage payoff surplus is pointwise nonpositive on
every configuration and every pure unilateral row.  Thus `(N)` needs no
analysis of the neutral support: nonnegative occupation weights can only
average nonpositive numbers. -/
theorem stagePayoffAt_sub_target_nonpos (who : Player) (z : Config)
    (act : Bool) :
    architecture.stagePayoffAt who z (PMF.pure act) - target z who ≤ 0 := by
  cases z with
  | inl c =>
      fin_cases c <;> fin_cases who <;>
        simp [FiniteResponseArchitecture.stagePayoffAt,
          FiniteResponseArchitecture.actionDist, game,
          quittingGame, publicState, target, phaseTarget]
  | inr S =>
      simp [FiniteResponseArchitecture.stagePayoffAt,
        FiniteResponseArchitecture.actionDist, game,
        quittingGame, publicState, target]

/-- `(N)` for the concrete FTV controller. -/
theorem isNeutralOccupationNonpositive :
    architecture.IsNeutralOccupationNonpositive target := by
  intro who μ
  unfold FiniteResponseArchitecture.NeutralOccupation.surplus
  exact Finset.sum_nonpos fun p _ ↦
    mul_nonpos_of_nonneg_of_nonpos (μ.mass_nonneg p)
      (stagePayoffAt_sub_target_nonpos who p.1 p.2)

/-- The prescribed live-to-live kernel is one half on the cyclic successor
and zero on the other two live phases. -/
theorem prescribedConfigDist_live_apply_live (source dest : Player) :
    (architecture.prescribedConfigDist (Sum.inl source) (Sum.inl dest)).toReal =
      if dest = nextPhase source then (1 / 2 : ℝ) else 0 := by
  rw [apply_toReal_eq_expect_indicator]
  simp only [FiniteResponseArchitecture.prescribedConfigDist,
    FiniteResponseArchitecture.prescribedActionDist, expect_bind, expect_pure]
  change expect (pmfPi (play (Sum.inl source))) (fun joint ↦
      expect ((quittingGame terminalReward).transition none joint) (fun s' ↦
        if step (Sum.inl source) joint s' = Sum.inl dest then 1 else 0)) = _
  rw [expect_pmfPi_fin3_bool]
  fin_cases source <;> fin_cases dest <;>
    simp [play, game, quittingGame, step, nextPhase]

/-- An absorbing child has no prescribed transition into a live phase. -/
theorem prescribedConfigDist_child_apply_live (S : Terminal) (dest : Player) :
    (architecture.prescribedConfigDist (Sum.inr S) (Sum.inl dest)).toReal = 0 := by
  rw [apply_toReal_eq_expect_indicator]
  simp [FiniteResponseArchitecture.prescribedConfigDist,
    FiniteResponseArchitecture.prescribedActionDist, architecture, game,
    quittingGame, publicState, step]

/-- A stationary distribution of the prescribed controller gives zero mass
to every live phase.  Balance yields
`m₀ = m₂/2`, `m₁ = m₀/2`, and `m₂ = m₁/2`; going once
around the clock therefore multiplies live mass by `1/8`. -/
theorem prescribedStationary_live_mass_zero
    (ν : architecture.PrescribedStationary) (c : Player) :
    ν.mass (Sum.inl c) = 0 := by
  have h0 := ν.balance (Sum.inl (0 : Player))
  have h1 := ν.balance (Sum.inl (1 : Player))
  have h2 := ν.balance (Sum.inl (2 : Player))
  simp only [Fintype.sum_sum_type] at h0 h1 h2
  rw [Fin.sum_univ_three] at h0 h1 h2
  rw [prescribedConfigDist_live_apply_live 0 0,
    prescribedConfigDist_live_apply_live 1 0,
    prescribedConfigDist_live_apply_live 2 0] at h0
  rw [prescribedConfigDist_live_apply_live 0 1,
    prescribedConfigDist_live_apply_live 1 1,
    prescribedConfigDist_live_apply_live 2 1] at h1
  rw [prescribedConfigDist_live_apply_live 0 2,
    prescribedConfigDist_live_apply_live 1 2,
    prescribedConfigDist_live_apply_live 2 2] at h2
  have hc0 : ∑ S : Terminal,
      ν.mass (Sum.inr S) *
        ((architecture.prescribedConfigDist (Sum.inr S) (Sum.inl 0)).toReal -
          if Sum.inl (0 : Player) = Sum.inr S then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    rw [prescribedConfigDist_child_apply_live S 0]
    simp
  have hc1 : ∑ S : Terminal,
      ν.mass (Sum.inr S) *
        ((architecture.prescribedConfigDist (Sum.inr S) (Sum.inl 1)).toReal -
          if Sum.inl (1 : Player) = Sum.inr S then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    rw [prescribedConfigDist_child_apply_live S 1]
    simp
  have hc2 : ∑ S : Terminal,
      ν.mass (Sum.inr S) *
        ((architecture.prescribedConfigDist (Sum.inr S) (Sum.inl 2)).toReal -
          if Sum.inl (2 : Player) = Sum.inr S then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    rw [prescribedConfigDist_child_apply_live S 2]
    simp
  rw [hc0] at h0
  rw [hc1] at h1
  rw [hc2] at h2
  have hb0 : -ν.mass (Sum.inl (0 : Player)) +
      ν.mass (Sum.inl (2 : Player)) * (1 / 2 : ℝ) = 0 := by
    simpa [nextPhase] using h0
  have hb1 : ν.mass (Sum.inl (0 : Player)) * (1 / 2 : ℝ) -
      ν.mass (Sum.inl (1 : Player)) = 0 := by
    simpa [nextPhase, sub_eq_add_neg] using h1
  have hb2 : ν.mass (Sum.inl (1 : Player)) * (1 / 2 : ℝ) -
      ν.mass (Sum.inl (2 : Player)) = 0 := by
    simpa [nextPhase, sub_eq_add_neg] using h2
  have hm0 : ν.mass (Sum.inl (0 : Player)) = 0 := by
    linarith [hb0, hb1, hb2]
  have hm1 : ν.mass (Sum.inl (1 : Player)) = 0 := by
    linarith [hb0, hb1, hb2]
  have hm2 : ν.mass (Sum.inl (2 : Player)) = 0 := by
    linarith [hb0, hb1, hb2]
  fin_cases c
  · exact hm0
  · exact hm1
  · exact hm2

/-- At an absorbing child, prescribed stage payoff is exactly the assigned
target. -/
theorem prescribedStagePayoff_child (S : Terminal) (who : Player) :
    architecture.prescribedStagePayoff (Sum.inr S) who =
      target (Sum.inr S) who := by
  simp [FiniteResponseArchitecture.prescribedStagePayoff,
    FiniteResponseArchitecture.prescribedActionDist, game, quittingGame,
    publicState, target]

/-- `(P)` for the concrete FTV controller.  Stationarity puts no mass on the
three transient live phases, while every absorbing child delivers its target
with equality. -/
theorem isPrescribedDelivery :
    architecture.IsPrescribedDelivery target := by
  intro who ν
  rw [Fintype.sum_sum_type]
  have hlive : ∑ c : Player,
      ν.mass (Sum.inl c) *
        (architecture.prescribedStagePayoff (Sum.inl c) who -
          target (Sum.inl c) who) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [prescribedStationary_live_mass_zero ν c]
    simp
  have hchild : ∑ S : Terminal,
      ν.mass (Sum.inr S) *
        (architecture.prescribedStagePayoff (Sum.inr S) who -
          target (Sum.inr S) who) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    rw [prescribedStagePayoff_child S who]
    ring
  rw [hlive, hchild]
  norm_num

/-- The concrete ten-node FTV architecture satisfies all four finite
credibility conditions. -/
theorem isGlobalCredibilityCriterion :
    architecture.IsGlobalCredibilityCriterion target where
  targetHarmonic := isPrescribedTargetHarmonic
  targetSuperharmonic := isUnilateralTargetSuperharmonic
  neutralOccupation := isNeutralOccupationNonpositive
  prescribedDelivery := isPrescribedDelivery

/-- The named payoff at the initial live phase. -/
def initialTarget : Payoff Player := ![1, 2, 1]

@[simp] theorem target_start (who : Player) :
    target architecture.start who = initialTarget who := by
  fin_cases who <;> rfl

/-- **Concrete credibility milestone.**  At every positive error, the actual
FTV three-cycle produces the operational public-response enforcement ledger
for payoff `(1,2,1)` at the active quitting-game state. -/
theorem nonempty_publicResponseEnforcementLedgerAt
    {err : ℝ} (herr : 0 < err) :
    Nonempty
      (game.PublicResponseEnforcementLedgerAt architecture.phaseProfile
        initialState initialTarget err) :=
  architecture.nonempty_publicResponseEnforcementLedgerAt
    isGlobalCredibilityCriterion initialTarget target_start herr

/-- Existential punishment-system packaging of the same concrete ledger. -/
theorem isPublicPhasePunishmentSystemAt
    {err : ℝ} (herr : 0 < err) :
    game.IsPublicPhasePunishmentSystemAt initialState initialTarget err :=
  architecture.isPublicPhasePunishmentSystemAt_of_isGlobalCredibilityCriterion
    isGlobalCredibilityCriterion initialTarget target_start herr

/-- Adaptive-certificate packaging of the same concrete ledger. -/
theorem isAdaptivePotentialCertificateAt
    {err : ℝ} (herr : 0 < err) :
    game.IsAdaptivePotentialCertificateAt initialState initialTarget err :=
  architecture.isAdaptivePotentialCertificateAt_of_isGlobalCredibilityCriterion
    isGlobalCredibilityCriterion initialTarget target_start herr

end FTVCyclicCredibility
end GameTheory
