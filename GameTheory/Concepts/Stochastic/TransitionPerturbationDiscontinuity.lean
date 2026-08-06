/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Discounted
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform payoffs are discontinuous under transition perturbations

Reward perturbations are harmless because they change every finite-horizon
average by the same horizon-independent amount.  Transition perturbations can
change which recurrent class is eventually reached, so no analogous theorem is
available in general.

This file gives the minimal counterexample.  There is one player, one action,
and two states.  State `true` is absorbing and pays `1`; state `false` pays `0`
and moves to `true` independently each round with probability `p`.

For every `p > 0`, absorption occurs asymptotically and the unique uniform
payoff from `false` is `1`.  At `p = 0`, the process remains at `false` and
payoff `1` is not uniform.  The transition probabilities themselves converge
coordinatewise whenever `p → 0`.  Thus transition kernels may converge to a
limit kernel while their uniform-equilibrium payoffs do not converge to a
uniform payoff of the limit game.
-/

noncomputable section

open Filter
open Math.Probability

namespace GameTheory
namespace StochasticGame
namespace TransitionPerturbationDiscontinuity

/-- The counterexample has one player. -/
abbrev Player : Type := Fin 1

/-- Two-state, one-action game with a rare transition to the good absorbing
state.  `PMF.bernoulli p hp` assigns probability `p` to `true`. -/
def rareTransitionGame (p : ℝ≥0) (hp : p ≤ 1) : StochasticGame Player where
  State := Bool
  Act := fun _ => PUnit
  stagePayoff := fun s _ _ => if s then 1 else 0
  transition := fun s _ => if s then PMF.pure true else PMF.bernoulli p hp
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- The unique joint pure action. -/
def canonicalAction : ∀ _ : Player, PUnit := fun _ => PUnit.unit

/-- Canonical behavior profile; every player always takes the unique action. -/
def canonicalProfile (p : ℝ≥0) (hp : p ≤ 1) :
    (rareTransitionGame p hp).BehaviorProfile :=
  fun _ _ _ => PMF.pure PUnit.unit

/-- With one available action, every behavior profile is the canonical one. -/
theorem behaviorProfile_eq_canonical
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) :
    σ = canonicalProfile p hp := by
  funext who t h
  exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ PUnit.unit

@[simp] theorem transition_false_true_toReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    (((rareTransitionGame p hp).transition false canonicalAction) true).toReal =
      (p : ℝ) := by
  simp [rareTransitionGame, canonicalAction, PMF.bernoulli_apply]

@[simp] theorem transition_false_false_toReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    (((rareTransitionGame p hp).transition false canonicalAction) false).toReal =
      1 - (p : ℝ) := by
  simp [rareTransitionGame, canonicalAction, PMF.bernoulli_apply, hp]

@[simp] theorem transition_true_true_toReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    (((rareTransitionGame p hp).transition true canonicalAction) true).toReal = 1 := by
  simp [rareTransitionGame, canonicalAction]

@[simp] theorem transition_true_false_toReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    (((rareTransitionGame p hp).transition true canonicalAction) false).toReal = 0 := by
  simp [rareTransitionGame, canonicalAction]

/-- Coordinatewise convergence of the transition kernels to the `p = 0`
kernel.  On this finite state-action skeleton this is also uniform convergence
of the kernel table. -/
theorem tendsto_transition_toReal_at_zero
    {p : ℕ → ℝ≥0} (hp : ∀ n, p n ≤ 1)
    (hp0 : Tendsto (fun n => (p n : ℝ)) atTop (nhds 0))
    (s s' : Bool) :
    Tendsto
      (fun n =>
        (((rareTransitionGame (p n) (hp n)).transition s canonicalAction) s').toReal)
      atTop
      (nhds ((((rareTransitionGame 0 (by norm_num)).transition s canonicalAction) s').toReal)) := by
  cases s <;> cases s'
  · simpa using (tendsto_const_nhds.sub hp0 :
      Tendsto (fun n => 1 - (p n : ℝ)) atTop (nhds (1 - 0)))
  · simpa using hp0
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

/-- Indicator of the bad state. -/
def badIndicator : Bool → ℝ
  | false => 1
  | true => 0

/-- Indicator of the good state. -/
def goodIndicator : Bool → ℝ
  | false => 0
  | true => 1

@[simp] theorem goodIndicator_eq_one_sub_badIndicator (s : Bool) :
    goodIndicator s = 1 - badIndicator s := by
  cases s <;> rfl

/-- Expected bad-state indicator after one transition. -/
theorem expect_transition_badIndicator
    (p : ℝ≥0) (hp : p ≤ 1)
    (s : Bool) (a : (rareTransitionGame p hp).JointAct) :
    expect ((rareTransitionGame p hp).transition s a) badIndicator =
      if s then 0 else 1 - (p : ℝ) := by
  cases s
  · rw [expect_eq_sum]
    simp [rareTransitionGame, badIndicator, PMF.bernoulli_apply, hp]
  · simp [rareTransitionGame, badIndicator]

/-- Probability mass of the bad state after `t` completed stages. -/
def badMass
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) (t : ℕ) : ℝ :=
  (rareTransitionGame p hp).expectedStateValue σ false t badIndicator

@[simp] theorem badMass_zero
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) :
    badMass p hp σ 0 = 1 := by
  simp [badMass, badIndicator]

/-- The remaining bad mass is multiplied by `1-p` at every step. -/
theorem badMass_succ
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) (t : ℕ) :
    badMass p hp σ (t + 1) = (1 - (p : ℝ)) * badMass p hp σ t := by
  unfold badMass
  rw [(rareTransitionGame p hp).expectedStateValue_succ]
  have hinner : ∀ h : (rareTransitionGame p hp).Hist t,
      expect ((rareTransitionGame p hp).stageActionDist σ h) (fun a =>
        expect ((rareTransitionGame p hp).transition h.2 a) badIndicator) =
      (1 - (p : ℝ)) * badIndicator h.2 := by
    intro h
    simp_rw [expect_transition_badIndicator]
    rw [expect_const]
    cases h.2 <;> simp [badIndicator]
  simp_rw [hinner]
  rw [expect_const_mul]
  rfl

/-- Exact geometric survival formula. -/
theorem badMass_eq_pow
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) (t : ℕ) :
    badMass p hp σ t = (1 - (p : ℝ)) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [badMass_succ, ih, pow_succ']
      ring

/-- Stage payoff after a history is exactly the current good-state indicator. -/
theorem stageEUAt_eq_goodIndicator
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile)
    {t : ℕ} (h : (rareTransitionGame p hp).Hist t) :
    (rareTransitionGame p hp).stageEUAt σ h 0 = goodIndicator h.2 := by
  unfold stageEUAt
  cases h.2 <;> simp [rareTransitionGame, goodIndicator]

/-- Expected stage payoff is one minus the bad-state mass. -/
theorem expectedStagePayoff_eq_one_sub_badMass
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) (t : ℕ) :
    (rareTransitionGame p hp).expectedStagePayoff σ false t 0 =
      1 - badMass p hp σ t := by
  unfold expectedStagePayoff badMass expectedStateValue
  simp_rw [stageEUAt_eq_goodIndicator,
    goodIndicator_eq_one_sub_badIndicator]
  rw [expect_sub, expect_const]

/-- Exact expected-stage-payoff formula. -/
theorem expectedStagePayoff_eq_one_sub_pow
    (p : ℝ≥0) (hp : p ≤ 1)
    (σ : (rareTransitionGame p hp).BehaviorProfile) (t : ℕ) :
    (rareTransitionGame p hp).expectedStagePayoff σ false t 0 =
      1 - (1 - (p : ℝ)) ^ t := by
  rw [expectedStagePayoff_eq_one_sub_badMass, badMass_eq_pow]

/-- At every positive transition probability, expected stage payoffs converge
to one. -/
theorem tendsto_expectedStagePayoff_one
    (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p)
    (σ : (rareTransitionGame p hp).BehaviorProfile) :
    Tendsto (fun t =>
      (rareTransitionGame p hp).expectedStagePayoff σ false t 0)
      atTop (nhds 1) := by
  have hp0r : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1r : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hbase0 : 0 ≤ 1 - (p : ℝ) := by linarith
  have hbase1 : 1 - (p : ℝ) < 1 := by linarith
  have hpow : Tendsto (fun t : ℕ => (1 - (p : ℝ)) ^ t) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  simpa [expectedStagePayoff_eq_one_sub_pow] using
    (tendsto_const_nhds.sub hpow :
      Tendsto (fun t : ℕ => 1 - (1 - (p : ℝ)) ^ t) atTop (nhds (1 - 0)))

/-- At every positive transition probability, finite averages converge to one. -/
theorem tendsto_finiteAveragePayoff_one
    (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p)
    (σ : (rareTransitionGame p hp).BehaviorProfile) :
    Tendsto (fun T =>
      (rareTransitionGame p hp).finiteAveragePayoff false T σ 0)
      atTop (nhds 1) := by
  simp_rw [(rareTransitionGame p hp).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  exact (tendsto_expectedStagePayoff_one p hp hp0 σ).cesaro

/-- For `p>0`, payoff one is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_one_of_pos
    (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) :
    (rareTransitionGame p hp).IsUniformEquilibriumPayoff false (fun _ => 1) := by
  intro ε hε
  let σ := canonicalProfile p hp
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_finiteAveragePayoff_one p hp hp0 σ) ε hε
  refine ⟨σ, T₀, fun T hT => ?_⟩
  constructor
  · intro who dev
    have hUpdate : Function.update σ who dev = σ := by
      calc
        Function.update σ who dev = canonicalProfile p hp :=
          behaviorProfile_eq_canonical p hp _
        _ = σ := (behaviorProfile_eq_canonical p hp σ).symm
    rw [hUpdate]
    linarith
  · intro who
    have hclose := (hT₀ T hT).le
    simpa [Real.dist_eq] using hclose

/-- At transition probability zero, every finite-horizon payoff from the bad
state is zero. -/
theorem finiteAveragePayoff_zero
    (σ : (rareTransitionGame 0 (by norm_num)).BehaviorProfile) (T : ℕ) :
    (rareTransitionGame 0 (by norm_num)).finiteAveragePayoff false T σ 0 = 0 := by
  rw [(rareTransitionGame 0 (by norm_num)).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp [expectedStagePayoff_eq_one_sub_pow]

/-- At the limit kernel `p=0`, payoff one is not a uniform-equilibrium payoff. -/
theorem not_isUniformEquilibriumPayoff_one_at_zero :
    ¬ (rareTransitionGame 0 (by norm_num)).IsUniformEquilibriumPayoff
        false (fun _ => 1) := by
  intro hUE
  obtain ⟨σ, T₀, hσ⟩ := hUE (1 / 2) (by norm_num)
  have hon := (hσ T₀ le_rfl).2 0
  rw [finiteAveragePayoff_zero] at hon
  norm_num at hon

end TransitionPerturbationDiscontinuity
end StochasticGame
end GameTheory
