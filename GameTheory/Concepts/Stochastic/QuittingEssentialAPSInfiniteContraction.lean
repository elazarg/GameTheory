/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSInfiniteRun

/-!
# Infinite essential-APS runs with opponent contraction

This file packages the two independent constructions:

1. terminal-free unique-live APS recursion produces one coherent infinite run;
2. compact active-face separation and bounded Flesch drift give that run a
   uniform opponent block-contraction certificate.

The singleton roots implementing the run also satisfy the exact prescribed
Bellman equations.  Thus the remaining input for the existing infinite-path
equilibrium compiler is local deviation control, not path existence or tail
contraction.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The singleton roots implementing an infinite APS run satisfy its exact
prescribed Bellman equations. -/
theorem IsQuittingEssentialAPSInfiniteRun.policy_singletonRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {owner : ℕ → ι} {initial : Payoff ι}
    {mass : ℕ → ℝ} {value : ℕ → Payoff ι}
    (hrun : IsQuittingEssentialAPSInfiniteRun reward family
      owner initial mass value)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1))
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1 time) := by
  intro time
  change value time = quittingRootSuccessorPayoff reward
    (value (time + 1))
    (quittingSoloStationaryRoot (owner time)
      (quittingHazardCoin (mass time) (hmass0 time) (hmass1 time)))
  rw [quittingRootSuccessorPayoff_solo]
  funext who
  have harcWho := congrFun (hrun.2.2 time).2 who
  simpa [quittingSingletonArcPayoff] using harcWho

/-- **Infinite APS path with exact Bellman transport and uniform opponent
contraction.**  Under terminal-freeness, compact unique-live successor fibers,
and finite-window active-face avoidance, every initial greatest-family point
admits one coherent infinite executable run whose singleton-root implementation
has a block-contraction factor strictly below one. -/
theorem
    exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live
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
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (hgreatestBound : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ∀ who, |current who| ≤ bound)
    (initialOwner : ι) {initial : Payoff ι}
    (hinitial : initial ∈
      quittingEssentialAPSGreatestFamily reward carrier initialOwner) :
    ∃ mass value,
      ∃ hrun : IsQuittingEssentialAPSInfiniteRun reward
        (quittingEssentialAPSGreatestFamily reward carrier)
        (quittingEssentialAPSSuccessorOrbit successor initialOwner)
        initial mass value,
      ∃ K : ℕ, ∃ eta rho : ℝ,
        0 < K ∧ 0 < eta ∧ 0 ≤ rho ∧ rho < 1 ∧
          ∃ (hmass0 : ∀ time, 0 ≤ mass time)
            (hmass1 : ∀ time, mass time ≤ 1),
            (∀ time,
              value time = quittingRootSuccessorPayoff reward
                (value (time + 1))
                (quittingEssentialAPSSingletonRoots
                  (quittingEssentialAPSSuccessorOrbit successor initialOwner)
                  mass hmass0 hmass1 time)) ∧
            IsQuittingOpponentBlockContraction
              (quittingEssentialAPSSingletonRoots
                (quittingEssentialAPSSuccessorOrbit successor initialOwner)
                mass hmass0 hmass1)
              K rho := by
  let owner := quittingEssentialAPSSuccessorOrbit successor initialOwner
  have hownerNext : ∀ time,
      owner (time + 1) = successor (owner time) := by
    intro time
    rfl
  have hedgePath : ∀ time,
      QuittingFleschSuccessor reward (owner time) (owner (time + 1)) := by
    intro time
    rw [hownerNext]
    exact hedge (owner time)
  have huniquePath : ∀ time candidate,
      QuittingFleschSuccessor reward (owner time) candidate →
        candidate ≠ owner (time + 1) →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅ := by
    intro time candidate hcandidate hne
    apply huniqueLive (owner time) candidate hcandidate
    rwa [hownerNext] at hne
  have hterminalPath : ∀ time current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier
        (owner time) →
      current ∉ quittingEssentialAPSTerminal reward (owner time) := by
    intro time current hcurrent
    exact hterminalFree (owner time) current hcurrent
  have hinitialPath : initial ∈
      quittingEssentialAPSGreatestFamily reward carrier (owner 0) := by
    simpa only [owner, quittingEssentialAPSSuccessorOrbit_zero] using hinitial
  obtain ⟨mass, value, hrun⟩ :=
    exists_quittingEssentialAPSInfiniteRun_of_unique_live_of_terminalFree
      reward carrier hcarrierConvex owner hedgePath huniquePath
        hterminalPath hinitialPath
  have hmass0 : ∀ time, 0 ≤ mass time := by
    intro time
    exact (hrun.2.2 time).1.1
  have hmass1 : ∀ time, mass time ≤ 1 := by
    intro time
    exact (hrun.2.2 time).1.2.le
  have hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time) :=
    hrun.2.1
  have harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)) := by
    intro time
    exact (hrun.2.2 time).2
  have hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time) := by
    intro time
    exact hrun.active_of_greatest time
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact hgreatestBound (owner time) (value time) (hvalueMem time) who
  obtain ⟨K, eta, rho, hK, heta, hrho0, hrho1, hcontraction⟩ :=
    exists_quittingEssentialAPSPath_opponentBlockContraction_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive horizonPos hfaceAvoidance hbound hrootBound
        owner mass value hownerNext hvalueMem hmass0 hmass1 harc hactive
        hvalueBound
  have hpolicy := hrun.policy_singletonRoots hmass0 hmass1
  refine ⟨mass, value, ?_, K, eta, rho,
    hK, heta, hrho0, hrho1, hmass0, hmass1, ?_, ?_⟩
  · simpa only [owner] using hrun
  · simpa only [owner] using hpolicy
  · simpa only [owner] using hcontraction

end GameTheory
