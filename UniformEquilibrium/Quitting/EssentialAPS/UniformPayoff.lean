/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.InfiniteContraction
import UniformEquilibrium.Quitting.EssentialAPS.UniformHazard
import UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteSingletonMeshCertificate

/-!
# Uniform payoffs from terminal-free essential APS components

The compact terminal-free unique-live APS stratum now supplies every input of
the nonperiodic equilibrium compiler.

* Coherent APS recursion gives one bounded infinite singleton-flow path.
* Compact active-face separation gives uniform opponent block contraction.
* Compact separation from the viable singleton endpoint gives one coarse
  hazard ceiling `pStar < 1`.
* A fixed logarithmic mesh makes every immediate-Quit error arbitrarily small,
  while preserving exact policy evaluation, exact prescribed Continue, and
  the coarse opponent-survival contraction.
* The nonperiodic Snell supersolution compiler therefore gives the initial APS
  value as a uniform-equilibrium payoff.

This theorem is conditional on the displayed compact functional unique-live,
terminal-free APS component.  It does not assert that every quitting game has
such a component.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Uniform-equilibrium payoff on a compact terminal-free unique-live APS
component.**  Every initial point of the greatest APS family is a uniform-
equilibrium payoff once the component satisfies the finite-window active-face
separation hypotheses used to obtain opponent contraction. -/
theorem
    quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    {horizon : ℕ} (horizonPos : 0 < horizon)
    (hfaceAvoidance : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ¬ IsQuittingEssentialAPSActiveAlong reward
          (quittingEssentialAPSSuccessorOrbit successor player)
          current horizon)
    (hterminalFree : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        current ∉ quittingEssentialAPSTerminal reward player)
    {bound : ℝ} (hbound : 0 < bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hgreatestBound : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ∀ who, |current who| ≤ bound)
    (initialOwner : ι) {initial : Payoff ι}
    (hinitial : initial ∈
      quittingEssentialAPSGreatestFamily reward carrier initialOwner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none initial := by
  let owner := quittingEssentialAPSSuccessorOrbit successor initialOwner
  have hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound := by
    intro quitter who
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      hreward (quittingSingletonTerminal quitter) who
  obtain ⟨mass, value, hrun, K, eta, rho,
      hK, _heta, hrho0, hrho1, hmass0, hmass1,
      _hpolicy, hblock⟩ :=
    exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive horizonPos hfaceAvoidance hterminalFree hbound
        hrootBound hgreatestBound initialOwner hinitial
  have hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time) := by
    simpa only [owner] using hrun.2.1
  have harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)) := by
    intro time
    simpa only [owner] using (hrun.2.2 time).2
  have hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time) := by
    intro time
    simpa only [owner] using hrun.active_of_greatest time
  have hviable : ∀ time,
      QuittingEssentialAPSViable reward (value time) := by
    intro time
    exact quittingEssentialAPSGreatestFamily_viable
      reward carrier (hvalueMem time)
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact hgreatestBound (owner time) (value time) (hvalueMem time) who
  obtain ⟨pStar, _hpStar0, hpStar1, hmassCeiling⟩ :=
    exists_uniform_quittingEssentialAPSHazardCeiling_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive hterminalFree hbound owner mass value hvalueMem
        hmass0 hmass1 harc hrootBound hvalueBound
  have hD : 0 ≤ 2 * bound := by positivity
  have hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ 2 * bound := by
    intro active other _hne
    exact quittingSingletonCollisionSurplus_le_two_mul_bound
      reward hbound.le hreward active other
  have huniform :=
    isUniformEquilibriumPayoff_of_singletonFlow_uniformHazard
      reward owner mass value hK hmass0 hpStar1 hmassCeiling
        harc hactive hviable hD hcollision hvalueBound hreward
        hrho0 hrho1 hblock
  simpa only [owner, hrun.1] using huniform

end GameTheory
