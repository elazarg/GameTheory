/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSInfiniteContraction
import GameTheory.Concepts.Stochastic.QuittingVariableSingletonMesh

/-!
# Uniform payoff from the functional essential-APS stratum

This file closes the consumer side of the compact functional unique-live APS
construction.  The coherent coarse run already has exact Bellman transport
and uniform opponent contraction.  Accuracy-indexed variable subdivision
turns every coarse singleton arc into finitely many microstages whose immediate
Quit error is uniformly small, without changing any coarse survival product.
The nonperiodic supersolution compiler gives terminal Nash, and the finite
quitting-game transfer gives one profile valid at every sufficiently long
horizon.

The theorem remains a conditional stratum theorem: it assumes the compact
unique-live APS hypotheses.  It does not assert that every quitting game has
such a component.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Greatest-family points satisfy the APS individual-viability floor. -/
theorem quittingEssentialAPSGreatestFamily_viable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    {owner : ι} {value : Payoff ι}
    (hvalue : value ∈
      quittingEssentialAPSGreatestFamily reward carrier owner) :
    QuittingEssentialAPSViable reward value := by
  have hstep :=
    (quittingEssentialAPSGreatestFamily_subinvariant
      reward carrier owner hvalue).2
  change value ∈ quittingEssentialAPSOwnerStep reward
    (quittingEssentialAPSGreatestFamily reward carrier) owner at hstep
  rcases hstep with hterminal | hprefix
  · exact hterminal.2
  · exact hprefix.1

/-- **Functional essential APS produces a uniform-equilibrium payoff.**

Under the hypotheses of the coherent-run/opponent-contraction capstone, the
distinguished initial payoff is a genuine uniform-equilibrium payoff.  The
additional all-terminal reward bound only prices collision surplus; it is
automatic for a finite quitting table after increasing `bound`. -/
theorem
    quittingEssentialAPS_isUniformEquilibriumPayoff_unique_live
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
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (hgreatestBound : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ∀ who, |current who| ≤ bound)
    (initialOwner : ι) {initial : Payoff ι}
    (hinitial : initial ∈
      quittingEssentialAPSGreatestFamily reward carrier initialOwner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none initial := by
  obtain ⟨mass, coarse, hrunRaw, K, _eta, rho,
      hK, _heta, hrho0, hrho1, hmass0, hmass1,
      _hpolicy, hblockRaw⟩ :=
    exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive horizonPos hfaceAvoidance hterminalFree hbound
        hrootBound hgreatestBound initialOwner hinitial
  let owner := quittingEssentialAPSSuccessorOrbit successor initialOwner
  have hrun : IsQuittingEssentialAPSInfiniteRun reward
      (quittingEssentialAPSGreatestFamily reward carrier)
      owner initial mass coarse := by
    simpa only [owner] using hrunRaw
  have hblock : IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      K rho := by
    simpa only [owner] using hblockRaw
  have hmassLt : ∀ block, mass block < 1 := by
    intro block
    exact (hrun.2.2 block).1.2
  have harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (coarse (block + 1)) := by
    intro block
    exact (hrun.2.2 block).2
  have hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block) := by
    intro block
    exact hrun.active_of_greatest block
  have hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who := by
    intro block who
    have hviable := quittingEssentialAPSGreatestFamily_viable
      reward carrier (hrun.2.1 block)
    exact hviable who
  have hcoarseBound : ∀ block who, |coarse block who| ≤ bound := by
    intro block who
    exact hgreatestBound (owner block) (coarse block)
      (hrun.2.1 block) who
  have hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ 2 * bound := by
    intro block other _hne
    have hcollisionBound :
        |quittingSingletonCollisionReward reward (owner block) other| ≤
          bound := by
      simpa [quittingSingletonCollisionReward] using
        hreward ⟨{owner block, other}, by simp⟩ other
    have hsoloBound := hrootBound other other
    rw [abs_le] at hcollisionBound hsoloBound
    apply max_le
    · linarith
    · linarith
  have hcoarseBlock : IsQuittingOpponentBlockContraction
      (quittingVariableSingletonCoarseRoot owner mass hmass0 hmassLt)
      K rho := by
    simpa [quittingVariableSingletonCoarseRoot,
      quittingEssentialAPSSingletonRoots] using hblock
  have hcoarseSurvival : ∀ who,
      Tendsto (quittingOpponentSurvivalWeight
        (quittingVariableSingletonCoarseRoot owner mass hmass0 hmassLt)
        who 0) atTop (nhds 0) := by
    intro who
    exact tendsto_zero_quittingOpponentSurvivalWeight_of_blockContraction
      (quittingVariableSingletonCoarseRoot owner mass hmass0 hmassLt)
      hK hcoarseBlock hrho0 hrho1 who 0
  intro epsilon hepsilon
  let D : ℝ := 2 * bound
  let delta : ℝ := epsilon / (8 * bound)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos hepsilon (mul_pos (by norm_num) hbound)
  have hterminalError : D * delta < epsilon / 2 := by
    have hboundNe : bound ≠ 0 := ne_of_gt hbound
    have hidentity : D * delta = epsilon / 4 := by
      dsimp only [D, delta]
      field_simp [hboundNe]
      ring
    rw [hidentity]
    linarith
  let length : ℕ → ℕ := fun block =>
    quittingAdaptiveMeshLength (mass block) delta
  let roots := quittingVariableSingletonMeshRoot
    owner mass length hmass0 hmassLt
  let profile := quittingInfinitePathProfile reward roots
  obtain ⟨hterminalNash, hterminalValueCoarse⟩ :=
    adaptiveVariableSingletonMesh_isTerminalNash_and_delivers
      reward owner mass coarse hdelta hD hbound.le hmass0 hmassLt
        hreward hcoarseBound harc hactive hcoarseSolo hcollision
        hcoarseSurvival
  have hterminalValue : quittingTerminalPayoff reward profile = initial := by
    change quittingTerminalPayoff reward
        (quittingInfinitePathProfile reward roots) = initial
    rw [hterminalValueCoarse, hrun.1]
  have hterminalNashProfile :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (D * delta) profile := by
    simpa only [profile, roots, length] using hterminalNash
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none (epsilon / 2) profile := by
    exact quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hterminalError hterminalNashProfile
  obtain ⟨nashThreshold, hnash⟩ := huniform
  have heventuallyDelivery : ∀ᶠ averagingHorizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none averagingHorizon
          profile who - initial who| < epsilon := by
    apply Filter.eventually_all.mpr
    intro who
    have htendsto : Tendsto
        (fun averagingHorizon ↦
          (quittingGame reward).finiteAveragePayoff none averagingHorizon
            profile who)
        atTop (nhds (initial who)) := by
      rw [← congrFun hterminalValue who]
      exact tendsto_finiteAveragePayoff_quittingGame reward profile who
    have hball := htendsto.eventually
      (Metric.ball_mem_nhds (initial who) hepsilon)
    filter_upwards [hball] with averagingHorizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
  obtain ⟨deliveryThreshold, hdelivery⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun averagingHorizon hlarge ↦ ?_⟩
  constructor
  · exact (hnash averagingHorizon
      (le_trans (Nat.le_max_left _ _) hlarge)).mono (by linarith)
  · intro who
    exact (hdelivery averagingHorizon
      (le_trans (Nat.le_max_right _ _) hlarge) who).le

end GameTheory
