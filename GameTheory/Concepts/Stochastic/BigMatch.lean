/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Absorbing
import Math.PMFProduct.Bool

/-!
# The Big Match

The classical two-player zero-sum Big Match has one live state and two
absorbing states. At the live state the maximizer chooses Continue/Stop and
the minimizer chooses Left/Right:

```text
             Left       Right
Continue       0           1
Stop           1*          0*
```

Here `*` means absorption at the displayed payoff. This file defines the
game and proves the one-step and finite-horizon identities used for
calendar-time state-Markov strategies.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

abbrev Player := Bool
abbrev Action (_ : Player) := Bool

inductive State
  | live
  | zero
  | one
  deriving DecidableEq, Fintype

/-- Maximizer reward. At live state it is one exactly off the diagonal. -/
def reward (s : State) (a : Player → Bool) : ℝ :=
  match s with
  | .live => if a false = a true then 0 else 1
  | .zero => 0
  | .one => 1

def payoff (s : State) (a : Player → Bool) (who : Player) : ℝ :=
  if who then -reward s a else reward s a

def nextState (s : State) (a : Player → Bool) : State :=
  match s with
  | .live => if a false then if a true then .zero else .one else .live
  | .zero => .zero
  | .one => .one

def transition (s : State) (a : Player → Bool) : PMF State :=
  PMF.pure (nextState s a)

abbrev game : StochasticGame Player where
  State := State
  Act := Action
  stagePayoff := payoff
  transition := transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance : Fintype game.State := inferInstanceAs (Fintype State)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq State)
instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Bool)

@[simp] lemma transition_eq_pure (s : State) (a : Player → Bool) :
    game.transition s a = PMF.pure (nextState s a) := rfl

@[simp] lemma expect_transition (s : State) (a : Player → Bool)
    (f : State → ℝ) :
    expect (game.transition s a) f = f (nextState s a) := by
  rw [transition_eq_pure, expect_pure]

@[simp] lemma payoff_minimizer (s : State) (a : Player → Bool) :
    game.stagePayoff s a true = -game.stagePayoff s a false := by
  simp [payoff]

@[simp] lemma payoff_maximizer (s : State) (a : Player → Bool) :
    game.stagePayoff s a false = reward s a := by
  simp [payoff]

lemma zero_isAbsorbingState : game.IsAbsorbingState .zero := by
  intro a
  simp [transition, nextState]

lemma one_isAbsorbingState : game.IsAbsorbingState .one := by
  intro a
  simp [transition, nextState]

theorem exists_uniformEquilibriumPayoff_zero :
    ∃ v : Payoff Player, game.IsUniformEquilibriumPayoff .zero v :=
  game.exists_uniformEquilibriumPayoff_of_isAbsorbingState zero_isAbsorbingState

theorem exists_uniformEquilibriumPayoff_one :
    ∃ v : Payoff Player, game.IsUniformEquilibriumPayoff .one v :=
  game.exists_uniformEquilibriumPayoff_of_isAbsorbingState one_isAbsorbingState

def liveIndicator : State → ℝ
  | .live => 1
  | .zero | .one => 0

def zeroIndicator : State → ℝ
  | .zero => 1
  | .live | .one => 0

def oneIndicator : State → ℝ
  | .one => 1
  | .live | .zero => 0

@[simp] lemma indicators_sum (s : State) :
    liveIndicator s + zeroIndicator s + oneIndicator s = 1 := by
  cases s <;> simp [liveIndicator, zeroIndicator, oneIndicator]

lemma pmfBool_false_toReal (μ : PMF Bool) :
    (μ false).toReal = 1 - (μ true).toReal :=
  Math.PMFProduct.pmfBool_false_toReal μ

/-- Fubini expansion of a product of two Boolean mixed actions. -/
lemma expect_pmfPi_bool (m : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun a =>
        expect (m true) (fun b => f (fun who => if who then b else a))) :=
  Math.PMFProduct.expect_pmfPi_bool m f

lemma expect_live_reward (m : Player → PMF Bool) :
    expect (pmfPi m) (fun a => reward .live a) =
      (m false true).toReal * (1 - (m true true).toReal) +
        (1 - (m false true).toReal) * (m true true).toReal := by
  rw [expect_pmfPi_bool]
  simp [reward, expect_eq_sum, pmfBool_false_toReal]

lemma expect_next_liveIndicator (s : State) (m : Player → PMF Bool) :
    expect (pmfPi m) (fun a =>
      expect (game.transition s a) liveIndicator) =
        (1 - (m false true).toReal) * liveIndicator s := by
  cases s <;> rw [expect_pmfPi_bool] <;>
    simp only [transition, expect_pure] <;>
    simp [nextState, liveIndicator, expect_eq_sum, pmfBool_false_toReal]

lemma expect_next_oneIndicator (s : State) (m : Player → PMF Bool) :
    expect (pmfPi m) (fun a =>
      expect (game.transition s a) oneIndicator) =
        oneIndicator s +
          ((m false true).toReal * (1 - (m true true).toReal)) *
            liveIndicator s := by
  cases s <;> rw [expect_pmfPi_bool] <;>
    simp only [transition, expect_pure] <;>
    simp [nextState, liveIndicator, oneIndicator, expect_eq_sum,
      pmfBool_false_toReal]

lemma expect_next_zeroIndicator (s : State) (m : Player → PMF Bool) :
    expect (pmfPi m) (fun a =>
      expect (game.transition s a) zeroIndicator) =
        zeroIndicator s +
          ((m false true).toReal * (m true true).toReal) *
            liveIndicator s := by
  cases s <;> rw [expect_pmfPi_bool] <;>
    simp only [transition, expect_pure] <;>
    simp [nextState, liveIndicator, zeroIndicator, expect_eq_sum,
      pmfBool_false_toReal]

lemma expect_stagePayoff_maximizer (s : State) (m : Player → PMF Bool) :
    expect (pmfPi m) (fun a => game.stagePayoff s a false) =
      oneIndicator s +
        (((m false true).toReal * (1 - (m true true).toReal) +
          (1 - (m false true).toReal) * (m true true).toReal)) *
            liveIndicator s := by
  cases s
  · simpa [payoff, oneIndicator, liveIndicator] using expect_live_reward m
  · simp [payoff, reward, oneIndicator, liveIndicator]
  · simp [payoff, reward, oneIndicator, liveIndicator]

/-! ## Calendar-time state-Markov play -/

abbrev TimeStateMixedProfile := ℕ → State → Player → PMF Bool

def timeStateBehaviorProfile
    (m : TimeStateMixedProfile) : game.BehaviorProfile :=
  fun who t h => m t h.2 who

@[simp] lemma stageActionDist_timeStateBehaviorProfile
    (m : TimeStateMixedProfile) {t : ℕ} (h : game.Hist t) :
    game.stageActionDist (timeStateBehaviorProfile m) h = pmfPi (m t h.2) :=
  rfl

def stopProbability (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  ((m t .live false) true).toReal

theorem stopProbability_nonneg (m : TimeStateMixedProfile) (t : ℕ) :
    0 ≤ stopProbability m t :=
  ENNReal.toReal_nonneg

theorem stopProbability_le_one (m : TimeStateMixedProfile) (t : ℕ) :
    stopProbability m t ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((m t .live false).coe_le_one true)

def rightProbability (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  ((m t .live true) true).toReal

def liveStageReward (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  stopProbability m t * (1 - rightProbability m t) +
    (1 - stopProbability m t) * rightProbability m t

def stateLiveProbability (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  game.expectedStateValue (timeStateBehaviorProfile m) .live t liveIndicator

def stateZeroProbability (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  game.expectedStateValue (timeStateBehaviorProfile m) .live t zeroIndicator

def stateOneProbability (m : TimeStateMixedProfile) (t : ℕ) : ℝ :=
  game.expectedStateValue (timeStateBehaviorProfile m) .live t oneIndicator

@[simp] lemma stateLiveProbability_zero
    (m : TimeStateMixedProfile) : stateLiveProbability m 0 = 1 := by
  simp [stateLiveProbability, liveIndicator]

@[simp] lemma stateZeroProbability_zero
    (m : TimeStateMixedProfile) : stateZeroProbability m 0 = 0 := by
  simp [stateZeroProbability, zeroIndicator]

@[simp] lemma stateOneProbability_zero
    (m : TimeStateMixedProfile) : stateOneProbability m 0 = 0 := by
  simp [stateOneProbability, oneIndicator]

theorem stateLiveProbability_succ
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateLiveProbability m (t + 1) =
      (1 - stopProbability m t) * stateLiveProbability m t := by
  rw [stateLiveProbability, game.expectedStateValue_succ]
  have hstep : ∀ h : game.Hist t,
      expect (game.stageActionDist (timeStateBehaviorProfile m) h) (fun a =>
        expect (game.transition h.2 a) liveIndicator) =
          (1 - stopProbability m t) * liveIndicator h.2 := by
    intro h
    rw [stageActionDist_timeStateBehaviorProfile]
    cases hs : h.2 <;>
      simpa [hs, stopProbability, liveIndicator] using
        expect_next_liveIndicator h.2 (m t h.2)
  simp_rw [hstep, expect_const_mul]
  rfl

theorem stateOneProbability_succ
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateOneProbability m (t + 1) = stateOneProbability m t +
      (stopProbability m t * (1 - rightProbability m t)) *
        stateLiveProbability m t := by
  rw [stateOneProbability, game.expectedStateValue_succ]
  let c := stopProbability m t * (1 - rightProbability m t)
  have hstep : ∀ h : game.Hist t,
      expect (game.stageActionDist (timeStateBehaviorProfile m) h) (fun a =>
        expect (game.transition h.2 a) oneIndicator) =
          oneIndicator h.2 + c * liveIndicator h.2 := by
    intro h
    rw [stageActionDist_timeStateBehaviorProfile]
    cases hs : h.2 <;>
      simpa [hs, c, stopProbability, rightProbability,
        liveIndicator, oneIndicator] using
          expect_next_oneIndicator h.2 (m t h.2)
  simp_rw [hstep, expect_add, expect_const_mul]
  rfl

theorem stateZeroProbability_succ
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateZeroProbability m (t + 1) = stateZeroProbability m t +
      (stopProbability m t * rightProbability m t) *
        stateLiveProbability m t := by
  rw [stateZeroProbability, game.expectedStateValue_succ]
  let c := stopProbability m t * rightProbability m t
  have hstep : ∀ h : game.Hist t,
      expect (game.stageActionDist (timeStateBehaviorProfile m) h) (fun a =>
        expect (game.transition h.2 a) zeroIndicator) =
          zeroIndicator h.2 + c * liveIndicator h.2 := by
    intro h
    rw [stageActionDist_timeStateBehaviorProfile]
    cases hs : h.2 <;>
      simpa [hs, c, stopProbability, rightProbability,
        liveIndicator, zeroIndicator] using
          expect_next_zeroIndicator h.2 (m t h.2)
  simp_rw [hstep, expect_add, expect_const_mul]
  rfl

theorem stateProbabilities_sum
    (m : TimeStateMixedProfile) (t : ℕ) :
    stateLiveProbability m t + stateZeroProbability m t +
      stateOneProbability m t = 1 := by
  unfold stateLiveProbability stateZeroProbability stateOneProbability
    expectedStateValue
  rw [← expect_add, ← expect_add]
  simp only [indicators_sum, expect_const]

theorem stateLiveProbability_eq_prod
    (m : TimeStateMixedProfile) (T : ℕ) :
    stateLiveProbability m T =
      ∏ t ∈ Finset.range T, (1 - stopProbability m t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [stateLiveProbability_succ, ih, Finset.prod_range_succ]
      ring

theorem expectedStagePayoff_maximizer
    (m : TimeStateMixedProfile) (t : ℕ) :
    game.expectedStagePayoff (timeStateBehaviorProfile m) .live t false =
      stateOneProbability m t +
        liveStageReward m t * stateLiveProbability m t := by
  unfold expectedStagePayoff stageEUAt
  have hstep : ∀ h : game.Hist t,
      expect (game.stageActionDist (timeStateBehaviorProfile m) h)
          (fun a => game.stagePayoff h.2 a false) =
        oneIndicator h.2 + liveStageReward m t * liveIndicator h.2 := by
    intro h
    rw [stageActionDist_timeStateBehaviorProfile]
    cases hs : h.2 <;>
      simpa [hs, liveStageReward, stopProbability, rightProbability,
        liveIndicator, oneIndicator] using
          expect_stagePayoff_maximizer h.2 (m t h.2)
  simp_rw [hstep, expect_add, expect_const_mul]
  rfl

theorem finiteAveragePayoff_maximizer
    (m : TimeStateMixedProfile) (T : ℕ) :
    game.finiteAveragePayoff .live T (timeStateBehaviorProfile m) false =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (stateOneProbability m t +
          liveStageReward m t * stateLiveProbability m t) := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  apply congrArg ((T : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro t ht
  exact expectedStagePayoff_maximizer m t

/-- The Big Match is zero-sum at every finite horizon. -/
theorem finiteAveragePayoff_minimizer
    (s₀ : State) (T : ℕ) (σ : game.BehaviorProfile) :
    game.finiteAveragePayoff s₀ T σ true =
      -game.finiteAveragePayoff s₀ T σ false := by
  have htotal : ∀ h : game.Hist T,
      game.totalPayoff true h = -game.totalPayoff false h := by
    intro h
    rw [totalPayoff, totalPayoff, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact payoff_minimizer (h.1 k).1 (h.1 k).2
  unfold finiteAveragePayoff
  simp_rw [htotal]
  have hneg :
      expect (game.histDist σ s₀ T) (fun h => -game.totalPayoff false h) =
        -expect (game.histDist σ s₀ T) (fun h => game.totalPayoff false h) := by
    calc
      expect (game.histDist σ s₀ T) (fun h => -game.totalPayoff false h) =
          expect (game.histDist σ s₀ T)
            (fun h => (-1 : ℝ) * game.totalPayoff false h) := by
        congr 1
        funext h
        ring
      _ = (-1 : ℝ) * expect (game.histDist σ s₀ T)
          (fun h => game.totalPayoff false h) :=
        expect_const_mul (game.histDist σ s₀ T) (-1)
          (fun h => game.totalPayoff false h)
      _ = -expect (game.histDist σ s₀ T)
          (fun h => game.totalPayoff false h) := by ring
  rw [hneg]
  ring

end BigMatch
end StochasticGame
end GameTheory
