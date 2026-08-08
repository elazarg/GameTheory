/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun
import UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteVariableSingletonMeshCertificate

/-!
# Adaptive-mesh uniform payoffs from terminal-free essential APS components

This capstone removes two quantitative hypotheses from the final compiler
layer.

* A bounded active Flesch path needs no geometric opponent-block contraction:
  divergence of its total absorption mass already forces every deleted-player
  survival tail to vanish by bounded successor-coordinate drift.
* A proper path needs no uniform hazard ceiling: every coarse hazard chooses
  its own finite logarithmic subdivision width.

Compact finite-window face avoidance is still used to produce one positive
mass floor along every shifted coarse window. After that point the proof uses
only divergence, exact survival transport at variable boundaries, and the
nonperiodic Snell supersolution compiler. In particular, neither the
superblock length nor the contraction factor from the earlier capstone enters
this theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Adaptive-mesh uniform payoff on a compact terminal-free unique-live APS
component.** Compactness produces a divergent executable mass path; bounded
Flesch drift and pointwise subdivision compile that path without a uniform
hazard ceiling or a geometric survival rate. -/
theorem
    quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh
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
    {horizon : ℕ}
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
  have hmassLt : ∀ time, mass time < 1 := by
    intro time
    exact (hrun.2.2 time).1.2
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
  have hviable : ∀ time,
      QuittingEssentialAPSViable reward (value time) := by
    intro time
    have hfixedOwner := congrFun
      (quittingEssentialAPSGreatestFamily_fixed reward carrier) (owner time)
    have hrestricted : value time ∈
        quittingEssentialAPSRestrictedOperator reward carrier
          (quittingEssentialAPSGreatestFamily reward carrier) (owner time) := by
      rw [hfixedOwner]
      exact hvalueMem time
    rcases hrestricted.2 with hterminal | hprefix
    · exact hterminal.2
    · exact hprefix.1
  have hsolo : ∀ time who,
      quittingSoloReward reward who who ≤ value time who := by
    intro time who
    exact hviable time who
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact hgreatestBound (owner time) (value time) (hvalueMem time) who
  have hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound := by
    intro quitter who
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      hreward (quittingSingletonTerminal quitter) who
  obtain ⟨nu, hnuPos, hwindow⟩ :=
    exists_uniform_quittingEssentialAPSWindowMass_along_successor_path_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive horizon hfaceAvoidance hbound hrootBound owner mass value
        hownerNext hvalueMem hmass0 harc hactive hvalueBound
  have htotal : Tendsto
      (quittingEssentialAPSWindowMass mass 0) atTop atTop :=
    tendsto_quittingEssentialAPSWindowMass_atTop_of_uniformWindow
      mass hmass0 hnuPos hwindow
  obtain ⟨gap, hgapPos, hgap⟩ :=
    exists_uniform_quittingFleschSuccessor_forwardGap
      reward successor initialOwner hedge
  have hpath :=
    isUniformEquilibriumPayoff_of_proper_flesch_infiniteSingletonPath_of_windowMass_atTop
      reward successor owner mass value hgapPos hbound.le hreward hmass0
        hmassLt harc hactive hownerNext hgap hsolo hvalueBound htotal
  simpa only [hrun.1] using hpath

end GameTheory
