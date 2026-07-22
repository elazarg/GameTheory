/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Asymptotic
import GameTheory.Concepts.Stochastic.QuittingGame
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Terminal and Finite-Average Payoffs in Quitting Games

In a finite quitting game, the probability of each absorbed state is monotone
over time and bounded by one.  Its limit therefore exists.  Expected stage
payoffs converge to the terminal rewards weighted by these limiting masses,
and Cesàro convergence shows that finite-horizon average payoffs have the same
limit.

Together with `StochasticGame.not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash`,
this gives the contrapositive interface needed by quitting-game refutation
arguments: failure of approximate Nash equilibrium for expected terminal
reward implies failure of a uniform equilibrium payoff.

## Main results

* `tendsto_finiteAveragePayoff_quittingGame` — finite averages converge to
  expected terminal reward for every behavior profile
* `quittingGame_not_exists_uniformEquilibriumPayoff_of_no_terminalNash` —
  a terminal-payoff nonexistence result refutes uniform-equilibrium existence
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Filter
open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Indicator of one absorbed state. -/
def quittingAbsorbedIndicator
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty})
    (s : (quittingGame r).State) : ℝ := by
  classical
  exact if s = some S then 1 else 0

/-- Probability that a quitting game has reached absorbed state `S` after
`t` completed stages, represented as the expectation of its indicator. -/
def quittingAbsorbedMass
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (t : ℕ)
    (S : {S : Finset ι // S.Nonempty}) : ℝ :=
  (quittingGame r).expectedStateValue σ none t
    (quittingAbsorbedIndicator r S)

theorem quittingAbsorbedMass_succ_ge
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (t : ℕ)
    (S : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass r σ t S ≤ quittingAbsorbedMass r σ (t + 1) S := by
  classical
  letI : Finite (quittingGame r).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ i : ι, Finite ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [quittingAbsorbedMass, quittingAbsorbedMass,
    (quittingGame r).expectedStateValue_succ]
  unfold StochasticGame.expectedStateValue
  apply expect_mono
  intro h
  cases hs : h.2 with
  | none =>
      rw [show quittingAbsorbedIndicator r S none = 0 by
        simp [quittingAbsorbedIndicator, quittingGame]]
      exact expect_nonneg _ _ fun a =>
        expect_nonneg _ _ fun s => by
          by_cases hs' : s = some S <;>
            simp [quittingAbsorbedIndicator, hs']
  | some T =>
      simp [quittingGame, quittingAbsorbedIndicator]

theorem quittingAbsorbedMass_monotone
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile)
    (S : {S : Finset ι // S.Nonempty}) :
    Monotone fun t => quittingAbsorbedMass r σ t S :=
  monotone_nat_of_le_succ fun t => quittingAbsorbedMass_succ_ge r σ t S

omit [DecidableEq ι] in
theorem quittingAbsorbedMass_le_one
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (t : ℕ)
    (S : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass r σ t S ≤ 1 := by
  classical
  letI : Finite (quittingGame r).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ i : ι, Finite ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  calc
    expect ((quittingGame r).histDist σ none t)
        (fun h => quittingAbsorbedIndicator r S h.2)
        ≤ expect ((quittingGame r).histDist σ none t) (fun _ => 1) := by
          apply expect_mono
          intro h
          by_cases hs : h.2 = some S <;>
            simp [quittingAbsorbedIndicator, hs]
    _ = 1 := expect_const _ _

/-- Limiting probability of absorption at `S`. -/
def quittingAbsorbedMassLimit
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile)
    (S : {S : Finset ι // S.Nonempty}) : ℝ :=
  ⨆ t, quittingAbsorbedMass r σ t S

theorem tendsto_quittingAbsorbedMass
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile)
    (S : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun t => quittingAbsorbedMass r σ t S) atTop
      (nhds (quittingAbsorbedMassLimit r σ S)) := by
  apply tendsto_atTop_ciSup (quittingAbsorbedMass_monotone r σ S)
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact quittingAbsorbedMass_le_one r σ t S

/-- Reward attached to the current state of a quitting game. -/
def quittingStateReward
    (r : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (quittingGame r).State → ℝ
  | none => 0
  | some S => r S who

omit [DecidableEq ι] in
theorem stageEUAt_quittingGame_eq_stateReward
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) {t : ℕ}
    (h : (quittingGame r).Hist t) (who : ι) :
    (quittingGame r).stageEUAt σ h who = quittingStateReward r who h.2 := by
  cases hs : h.2 with
  | none =>
      simp [StochasticGame.stageEUAt, quittingGame, quittingStateReward,
        expect_const, hs]
  | some S =>
      simp [StochasticGame.stageEUAt, quittingGame, quittingStateReward,
        expect_const, hs]

theorem quittingStateReward_eq_sum_indicator
    (r : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (s : (quittingGame r).State) :
    quittingStateReward r who s =
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingAbsorbedIndicator r S s * r S who := by
  classical
  cases s with
  | none => simp [quittingStateReward, quittingAbsorbedIndicator, quittingGame]
  | some T =>
      simp [quittingStateReward, quittingAbsorbedIndicator, quittingGame]

theorem expectedStagePayoff_quittingGame_eq_sum_mass
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (t : ℕ) (who : ι) :
    (quittingGame r).expectedStagePayoff σ none t who =
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingAbsorbedMass r σ t S * r S who := by
  classical
  letI : Finite (quittingGame r).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ i : ι, Finite ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold StochasticGame.expectedStagePayoff
  simp_rw [stageEUAt_quittingGame_eq_stateReward]
  conv_lhs =>
    enter [2, h]
    rw [quittingStateReward_eq_sum_indicator]
  rw [← expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [show (fun h : (quittingGame r).Hist t =>
      quittingAbsorbedIndicator r S h.2 * r S who) =
      (fun h => r S who * quittingAbsorbedIndicator r S h.2) by
        funext h
        ring]
  rw [expect_const_mul]
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  ring

/-- Expected terminal reward: absorbed-state rewards weighted by their
limiting absorption probabilities.  Nonabsorption contributes the active
state's payoff, which is zero. -/
def quittingTerminalPayoff
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (who : ι) : ℝ :=
  ∑ S : {S : Finset ι // S.Nonempty},
    quittingAbsorbedMassLimit r σ S * r S who

theorem tendsto_expectedStagePayoff_quittingGame
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (who : ι) :
    Tendsto (fun t =>
      (quittingGame r).expectedStagePayoff σ none t who) atTop
      (nhds (quittingTerminalPayoff r σ who)) := by
  simp_rw [expectedStagePayoff_quittingGame_eq_sum_mass]
  unfold quittingTerminalPayoff
  apply tendsto_finsetSum Finset.univ
  intro S _
  exact (tendsto_quittingAbsorbedMass r σ S).mul_const (r S who)

theorem tendsto_finiteAveragePayoff_quittingGame
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : (quittingGame r).BehaviorProfile) (who : ι) :
    Tendsto (fun T =>
      (quittingGame r).finiteAveragePayoff none T σ who) atTop
      (nhds (quittingTerminalPayoff r σ who)) := by
  letI : Finite (quittingGame r).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ i : ι, Finite ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  simp_rw [(quittingGame r).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  exact (tendsto_expectedStagePayoff_quittingGame r σ who).cesaro

/-- Refutation interface specialized to quitting games. -/
theorem quittingGame_not_exists_uniformEquilibriumPayoff_of_no_terminalNash
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε : ℝ} (hε : 0 < ε)
    (hno : ¬ ∃ σ : (quittingGame r).BehaviorProfile,
      (quittingGame r).IsεAsymptoticNash
        (quittingTerminalPayoff r) ε σ) :
    ¬ ∃ v : Payoff ι,
      (quittingGame r).IsUniformEquilibriumPayoff none v := by
  apply (quittingGame r).not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash
    none (quittingTerminalPayoff r) hε hno
  intro σ who
  exact tendsto_finiteAveragePayoff_quittingGame r σ who

end GameTheory
