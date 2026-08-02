/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAsymptotic

/-!
# Eventual delivery and deviation caps at finite horizons

This module isolates the negative finite-horizon bridge used for quitting
games.  If one profile eventually delivers a vector within error `d` and
caps every unilateral deviation above that vector within error `c`, then it
is a uniform finite-horizon `(d + c)`-equilibrium.  Pointwise convergence for
the prescribed profile and each fixed deviation therefore makes it a
terminal `(d + c)`-equilibrium.

In particular, failure of terminal `ε₀`-equilibrium rules out such a common
profile whenever `c + d < ε₀`.  No convergence uniform over deviations is
used.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

namespace StochasticGame

open Filter

variable {ι : Type}

/-- One profile eventually delivers `v` within `deliveryError` and caps every
unilateral finite-horizon payoff by `v + capError`, with a common horizon
threshold. -/
def HasEventuallyDeliveryAndDeviationCap
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (initial : G.State) (profile : G.BehaviorProfile) (v : Payoff ι)
    (deliveryError capError : ℝ) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
    (∀ who,
      |G.finiteAveragePayoff initial T profile who - v who| ≤ deliveryError) ∧
    (∀ who (deviation : G.BehaviorStrategy who),
      G.finiteAveragePayoff initial T
          (Function.update profile who deviation) who ≤
        v who + capError)

/-- Delivery error and deviation-cap error add to give a uniform
finite-horizon Nash error. -/
theorem HasEventuallyDeliveryAndDeviationCap.isUniformεEquilibrium
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {initial : G.State} {profile : G.BehaviorProfile} {v : Payoff ι}
    {deliveryError capError : ℝ}
    (h : G.HasEventuallyDeliveryAndDeviationCap initial profile v
      deliveryError capError) :
    G.IsUniformεEquilibrium initial (deliveryError + capError) profile := by
  obtain ⟨T₀, hT₀⟩ := h
  refine ⟨T₀, fun T hT who deviation => ?_⟩
  have hdelivery := (hT₀ T hT).1 who
  have hcap := (hT₀ T hT).2 who deviation
  have hleft := (abs_le.mp hdelivery).1
  linarith

/-- Approximate Nash for a limiting payoff is monotone in its error. -/
theorem IsεAsymptoticNash.mono
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {u : G.BehaviorProfile → ι → ℝ} {ε ε' : ℝ}
    {profile : G.BehaviorProfile}
    (h : G.IsεAsymptoticNash u ε profile) (hε : ε ≤ ε') :
    G.IsεAsymptoticNash u ε' profile := by
  intro who deviation
  have hdev := h who deviation
  linarith

/-- Generic negative bridge.  Pointwise finite-horizon convergence is enough:
after the violating player and deviation are fixed, both sides can be passed
to the limit. -/
theorem not_exists_eventual_deliveryAndDeviationCap_of_no_asymptoticNash
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (initial : G.State) (u : G.BehaviorProfile → ι → ℝ)
    {ε₀ deliveryError capError : ℝ}
    (hgap : capError + deliveryError < ε₀)
    (hno : ¬ ∃ profile : G.BehaviorProfile,
      G.IsεAsymptoticNash u ε₀ profile)
    (hlim : ∀ (profile : G.BehaviorProfile) who,
      Tendsto (fun T => G.finiteAveragePayoff initial T profile who)
        Filter.atTop (nhds (u profile who))) :
    ¬ ∃ (profile : G.BehaviorProfile) (v : Payoff ι),
      G.HasEventuallyDeliveryAndDeviationCap initial profile v
        deliveryError capError := by
  rintro ⟨profile, v, hfinite⟩
  apply hno
  refine ⟨profile, ?_⟩
  have hnash : G.IsεAsymptoticNash u (deliveryError + capError) profile :=
    G.isεAsymptoticNash_of_isUniformεEquilibrium initial u
      hfinite.isUniformεEquilibrium hlim
  exact hnash.mono (by linarith)

end StochasticGame

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Failure of terminal `ε₀`-Nash in a quitting game excludes a common
eventual delivery/cap profile whenever the two finite-horizon errors sum to
strictly less than `ε₀`. -/
theorem quittingGame_not_exists_eventual_deliveryAndDeviationCap_of_no_terminalNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε₀ deliveryError capError : ℝ}
    (hgap : capError + deliveryError < ε₀)
    (hno : ¬ ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε₀ profile) :
    ¬ ∃ (profile : (quittingGame reward).BehaviorProfile) (v : Payoff ι),
      (quittingGame reward).HasEventuallyDeliveryAndDeviationCap
        none profile v deliveryError capError := by
  exact StochasticGame.not_exists_eventual_deliveryAndDeviationCap_of_no_asymptoticNash
      (quittingGame reward) none (quittingTerminalPayoff reward) hgap hno
      (fun profile who =>
        tendsto_finiteAveragePayoff_quittingGame reward profile who)

end GameTheory
