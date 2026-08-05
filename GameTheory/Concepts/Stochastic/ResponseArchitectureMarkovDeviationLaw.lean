/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ResponseArchitecturePurePrefixLaw

/-!
# Configuration-Markov unilateral deviations

A unilateral policy on the finite controller configurations induces both a
configuration Markov kernel and a one-stage reward.  When that policy is used
as a behavior deviation against the architecture's prescribed opponents, the
full public-history semantics project exactly to those two finite objects.

This reusable law is the bridge needed to operationalize invariant neutral
occupations in the gain-bias criterion's necessity direction.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section MarkovDeviation

variable [Fintype ι] [DecidableEq ι]

/-- Behavior strategy obtained from a stationary mixed policy on controller
configurations. -/
noncomputable def configMarkovDeviation (who : ι)
    (policy : A.Config → PMF (G.Act who)) : G.BehaviorStrategy who :=
  fun _ h => policy (A.configAt _ h)

/-- Full profile with one configuration-Markov deviator and prescribed
opponents. -/
noncomputable def configMarkovProfile (who : ι)
    (policy : A.Config → PMF (G.Act who)) : G.BehaviorProfile :=
  Function.update A.phaseProfile.behaviorProfile who
    (A.configMarkovDeviation who policy)

/-- Induced configuration kernel of a configuration-Markov unilateral
policy. -/
noncomputable def configMarkovKernel (who : ι)
    (policy : A.Config → PMF (G.Act who)) (z : A.Config) : PMF A.Config :=
  A.nextConfigDist who z (policy z)

/-- Induced one-stage reward of a configuration-Markov unilateral policy. -/
noncomputable def configMarkovReward (who : ι)
    (policy : A.Config → PMF (G.Act who)) (z : A.Config) : ℝ :=
  A.stagePayoffAt who z (policy z)

/-- Configuration-kernel Cesaro payoff of a stationary unilateral policy. -/
noncomputable def configMarkovCesaroPayoff (who : ι)
    (policy : A.Config → PMF (G.Act who)) (z : A.Config) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
    expect (Math.PMFIter.iter (A.configMarkovKernel who policy) t z)
      (A.configMarkovReward who policy)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem configMarkovDeviation_apply (who : ι)
    (policy : A.Config → PMF (G.Act who)) (t : ℕ) (h : G.Hist t) :
    A.configMarkovDeviation who policy t h = policy (A.configAt t h) :=
  rfl

/-- Joint-action law under the configuration-Markov deviator. -/
theorem stageActionDist_configMarkovProfile (who : ι)
    (policy : A.Config → PMF (G.Act who)) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (A.configMarkovProfile who policy) h =
      A.actionDist who (A.configAt t h) (policy (A.configAt t h)) := by
  rw [configMarkovProfile, A.stageActionDist_update]
  rfl

/-- On every supported history, the conditional next-configuration law is
the induced configuration-Markov kernel. -/
theorem historyConfigStepDist_configMarkovProfile_of_mem_support
    (who : ι) (policy : A.Config → PMF (G.Act who)) {t : ℕ}
    (h : G.Hist t)
    (hh : h ∈ (G.histDist (A.configMarkovProfile who policy) initial t).support) :
    A.historyConfigStepDist (A.configMarkovProfile who policy) h =
      A.configMarkovKernel who policy (A.configAt t h) := by
  unfold historyConfigStepDist configMarkovKernel nextConfigDist
  rw [A.stageActionDist_configMarkovProfile who policy h,
    A.publicState_configAt_of_mem_support
      (A.configMarkovProfile who policy) h hh]

/-- The configuration marginal of the history law is exactly iteration of
the induced configuration-Markov kernel. -/
theorem map_configAt_histDist_configMarkovProfile
    (who : ι) (policy : A.Config → PMF (G.Act who)) : ∀ t : ℕ,
    (G.histDist (A.configMarkovProfile who policy) initial t).map
        (A.configAt t) =
      Math.PMFIter.iter (A.configMarkovKernel who policy) t A.start := by
  intro t
  induction t with
  | zero =>
      rw [G.histDist_zero, PMF.pure_map, Math.PMFIter.iter_zero]
      rfl
  | succ t ih =>
      rw [A.map_configAt_histDist_succ]
      rw [bind_congr_on_support
        (G.histDist (A.configMarkovProfile who policy) initial t)
        (A.historyConfigStepDist (A.configMarkovProfile who policy))
        (A.configMarkovKernel who policy ∘ A.configAt t) (by
          intro h hh
          simp only [Function.comp_apply]
          exact A.historyConfigStepDist_configMarkovProfile_of_mem_support
            who policy h hh)]
      rw [← PMF.bind_map, ih, Math.PMFIter.iter_succ']

/-- Expected calendar reward under a configuration-Markov deviation is the
reward expected under its iterated configuration kernel. -/
theorem expectedStagePayoff_configMarkovProfile_eq_configIter
    (who : ι) (policy : A.Config → PMF (G.Act who)) (t : ℕ) :
    G.expectedStagePayoff (A.configMarkovProfile who policy) initial t who =
      expect (Math.PMFIter.iter (A.configMarkovKernel who policy) t A.start)
        (A.configMarkovReward who policy) := by
  unfold StochasticGame.expectedStagePayoff
  calc
    expect (G.histDist (A.configMarkovProfile who policy) initial t)
        (fun h => G.stageEUAt (A.configMarkovProfile who policy) h who) =
        expect (G.histDist (A.configMarkovProfile who policy) initial t)
          (fun h => A.configMarkovReward who policy (A.configAt t h)) :=
      expect_congr_on_support _ _ _ fun h hh => by
        rw [configMarkovReward]
        exact A.stageEUAt_update who (A.configMarkovDeviation who policy) h
          (A.publicState_configAt_of_mem_support
            (A.configMarkovProfile who policy) h hh)
    _ = expect
          ((G.histDist (A.configMarkovProfile who policy) initial t).map
            (A.configAt t))
          (A.configMarkovReward who policy) := by
      rw [expect_map]
    _ = expect
          (Math.PMFIter.iter (A.configMarkovKernel who policy) t A.start)
          (A.configMarkovReward who policy) := by
      rw [A.map_configAt_histDist_configMarkovProfile who policy t]

/-- Arbitrary-start expected-stage form of the configuration-Markov law. -/
theorem expectedStagePayoff_configMarkovProfile_rebase_eq_configIter
    (z : A.Config) (who : ι) (policy : A.Config → PMF (G.Act who)) (t : ℕ) :
    G.expectedStagePayoff ((A.rebase z).configMarkovProfile who policy)
        (A.publicState z) t who =
      expect (Math.PMFIter.iter (A.configMarkovKernel who policy) t z)
        (A.configMarkovReward who policy) := by
  have hk : (A.rebase z).configMarkovKernel who policy =
      A.configMarkovKernel who policy := by rfl
  have hr : (A.rebase z).configMarkovReward who policy =
      A.configMarkovReward who policy := by rfl
  simpa only [hk, hr] using
    (A.rebase z).expectedStagePayoff_configMarkovProfile_eq_configIter
      who policy t

end MarkovDeviation

section MarkovDeviationFiniteAverage

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- History-semantic finite averages of a rebased configuration-Markov
deviation equal its finite configuration-kernel Cesaro payoff. -/
theorem finiteAveragePayoff_configMarkovProfile_rebase_eq_configCesaro
    (z : A.Config) (who : ι) (policy : A.Config → PMF (G.Act who)) (T : ℕ) :
    G.finiteAveragePayoff (A.publicState z) T
        ((A.rebase z).configMarkovProfile who policy) who =
      A.configMarkovCesaroPayoff who policy z T := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  unfold configMarkovCesaroPayoff
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact A.expectedStagePayoff_configMarkovProfile_rebase_eq_configIter
    z who policy t

end MarkovDeviationFiniteAverage

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
