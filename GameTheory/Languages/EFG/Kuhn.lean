/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct
import GameTheory.Languages.EFG.CompileObsFacts
import GameTheory.Theorems.Kuhn

/-!
# Kuhn's Theorem for EFG — via ObsModelCore

Kuhn's theorem (behavioral ↔ mixed strategy equivalence) for extensive-form
games, derived as a corollary of the generic Kuhn development on
`ObsModelCore`.

The EFG-specific compiled-model structure, adequacy, and recall obligations live
in `GameTheory.Languages.EFG.CompileObsFacts`. This file is the theorem-facing
assembly layer.
-/

namespace EFG

open GameTheory Math.PMFProduct

variable {S : InfoStructure} {Outcome : Type}

-- ============================================================================
-- B→M via the central ObsModelCore theorem
-- ============================================================================

/-- **Kuhn B→M for EFG via the central theorem.**
The `runDist` of the lifted behavioral profile equals the product mixed strategy
bound to `runDistPure`, provided the tree has no info-set repeats. -/
theorem kuhn_behavioral_to_mixed_runDist
    (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) (k : Nat) :
    let O := compiledCoreObs t
    O.runDist k (GameTheory.EFG.liftBehavioralProfileCore t σ) =
      (O.behavioralToMixedJoint (GameTheory.EFG.liftBehavioralProfileCore t σ)).bind
        (fun π => O.runDistPure k π) :=
  ObsModelCore.kuhn_behavioral_to_mixed
    (noNontrivialInfoStateRepeat_compiledCore t hnr)
    (GameTheory.EFG.liftBehavioralProfileCore t σ) k

/-- **Kuhn B→M for EFG at the `evalDist` level, via the central theorem.**
For any behavioral profile on a tree with no info-set repeats,
the `evalDist` equals the expected `evalDist` under the product mixed strategy. -/
theorem kuhn_behavioral_to_mixed_evalDist
    (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) :
    let O := compiledCoreObs t
    t.evalDist σ =
      (O.behavioralToMixedJoint
        (GameTheory.EFG.liftBehavioralProfileCore t σ)).bind
        (fun π => t.evalDist
          (pureToBehavioral
            (GameTheory.EFG.descendPureProfileCore t π))) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let β' := GameTheory.EFG.liftBehavioralProfileCore t σ
  have hrun := kuhn_behavioral_to_mixed_runDist σ t hnr k
  -- Apply adequacy to both sides
  have hleft :
      (O.runDist k β').bind (fun ss => (O.lastState ss).evalDist σ) =
        t.evalDist σ :=
    runDist_bind_evalDist_core t σ k
  have hper_pure :
      ∀ π, (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ) =
        t.evalDist (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π)) := by
    intro π
    have hadq := runDistPure_bind_evalDist_core t π k
    -- Both sides agree on terminal states, and all reachable states are terminal
    calc
      (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ)
        = (O.runDistPure k π).bind (fun ss =>
            (O.lastState ss).evalDist
              (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π))) := by
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (O.runDistPure k π) _ _ ?_
          intro ss hss
          have hss' :=
            lastState_terminal_of_pureRun_height t
              (by simpa [O, k, ObsModelCore.runDistPure_eq_pureRun] using hss)
          obtain ⟨z, hz⟩ := hss'
          simp [O, hz]
      _ = t.evalDist
            (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π)) := hadq
  have hright :
      ((O.behavioralToMixedJoint β').bind (O.runDistPure k)).bind
          (fun ss => (O.lastState ss).evalDist σ) =
        (O.behavioralToMixedJoint β').bind
          (fun π => t.evalDist
            (pureToBehavioral
              (GameTheory.EFG.descendPureProfileCore t π))) := by
    rw [PMF.bind_bind]
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (O.behavioralToMixedJoint β') _ _ ?_
    intro π _hπ
    exact hper_pure π
  calc
    t.evalDist σ =
      (O.runDist k β').bind (fun ss => (O.lastState ss).evalDist σ) :=
        hleft.symm
    _ = ((O.behavioralToMixedJoint β').bind (O.runDistPure k)).bind
        (fun ss => (O.lastState ss).evalDist σ) := by
      rw [hrun]
    _ = (O.behavioralToMixedJoint β').bind
        (fun π => t.evalDist
          (pureToBehavioral
            (GameTheory.EFG.descendPureProfileCore t π))) :=
      hright

-- ============================================================================
-- Tree-level Kuhn theorems (bridge from ObsModel to evalDist)
-- ============================================================================

/-- Kuhn's theorem (behavioral → mixed direction):
    For any behavioral profile σ and tree with no info-set repeats,
    there exists a distribution over flat profiles
    that induces the same outcome distribution.

Delegates to `kuhn_behavioral_to_mixed_evalDist` (the central ObsModel proof)
and transports the witness through `flatProfileEquivPureProfile`. -/
theorem kuhn_behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ := by
  let O := compiledCoreObs t
  let β' := GameTheory.EFG.liftBehavioralProfileCore t σ
  have heval := kuhn_behavioral_to_mixed_evalDist σ t hnr
  let μ : PMF (FlatProfile S) :=
    (O.behavioralToMixedJoint β').map
      (fun π => flatProfileEquivPureProfile.symm
        (GameTheory.EFG.descendPureProfileCore t π))
  refine ⟨μ, ?_⟩
  simp only [μ, PMF.bind_map]
  have : (fun s => t.evalDist (flatToBehavioral s)) ∘
      (fun π => flatProfileEquivPureProfile.symm
        (GameTheory.EFG.descendPureProfileCore t π)) =
      fun π => t.evalDist (pureToBehavioral
        (GameTheory.EFG.descendPureProfileCore t π)) := by
    ext π; congr 1
  rw [this]
  exact heval.symm

/-- `kuhn_behavioral_to_mixed` under the original `PerfectRecall` assumption. -/
theorem kuhn_behavioral_to_mixed_pr (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hpr : PerfectRecall t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ :=
  kuhn_behavioral_to_mixed σ t (PerfectRecall_implies_NoInfoSetRepeat t hpr)

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (behavioral → mixed). -/
theorem kuhn_behavioral_to_mixed_udist (G : EFGGame)
    (σ : BehavioralProfile G.inf) (hpr : PerfectRecall G.tree) :
    ∃ μ : PMF (FlatProfile G.inf),
      μ.bind (fun s => G.toKernelGame.udist (flatToBehavioral s)) =
      G.toKernelGame.udist σ := by
  obtain ⟨μ, hμ⟩ := kuhn_behavioral_to_mixed_pr σ G.tree hpr
  exact ⟨μ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [← hμ, PMF.bind_bind]⟩

private theorem kuhn_mixed_to_behavioral_core
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ β : (compiledCoreObs t).BehavioralProfile,
      let O := compiledCoreObs t
      let k := treeHeight t
      let μ := GameTheory.EFG.liftMixedProfileCore t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let μ := GameTheory.EFG.liftMixedProfileCore t muP
  have hMass :
      ObsModelCore.StepMassInvariant O := by
    intro ss u π₁ π₂ h₁ h₂
    exact stepMassInvariant_compiledCore t π₁ π₂ h₁ h₂
  have hFactor :
      ObsModelCore.StepSupportFactorization O := by
    intro ss u π₀ π h₀
    exact stepSupportFactorization_compiledCore t π₀ π h₀
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := O)
      hMass hFactor
      (fun i =>
        ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility (O := O)
          hMass i
          (by
            simpa [O] using
              obsLocalFeasibility_compiledCore t hpr i))
      μ k
  exact ⟨β, hβ⟩

private theorem compiledCore_runEq_to_evalDistEq
    (t : GameTree S Outcome)
    (muP : MixedProfile S)
    {β : (compiledCoreObs t).BehavioralProfile}
    (hβ :
      let O := compiledCoreObs t
      let k := treeHeight t
      let μ := GameTheory.EFG.liftMixedProfileCore t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k)) :
    let σ := GameTheory.EFG.descendBehavioralProfileCore t β
    t.evalDist σ =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist (pureToBehavioral pi)) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let μ := GameTheory.EFG.liftMixedProfileCore t muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore t β
  have hleft :
      (O.runDist k β).bind (fun ss => (O.lastState ss).evalDist σ) = t.evalDist σ := by
    simpa [O, k, σ, GameTheory.EFG.liftBehavioralProfileCore_descendBehavioralProfileCore] using
      runDist_bind_evalDist_core t σ k
  have hright :
      ((pmfPi μ).bind (O.runDistPure k)).bind
          (fun ss => (O.lastState ss).evalDist σ) =
        (mixedProfileJoint muP).bind
          (fun pi => t.evalDist (pureToBehavioral pi)) := by
    rw [PMF.bind_bind]
    calc
      (pmfPi μ).bind
          (fun π => (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ))
        =
      (pmfPi μ).bind
          (fun π =>
            (O.runDistPure k π).bind
              (fun ss =>
                (O.lastState ss).evalDist
                  (pureToBehavioral
                    (GameTheory.EFG.descendPureProfileCore
                      t π)))) := by
            refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
            intro π _hπ
            refine Math.ProbabilityMassFunction.bind_congr_on_support (O.runDistPure k π) _ _ ?_
            intro ss hss
            have hss' :
                Math.ParameterizedChain.pureRun (O.pureStep) O.init k π ss ≠ 0 := by
              simpa [O, k, ObsModelCore.runDistPure_eq_pureRun] using hss
            obtain ⟨z, hz⟩ :=
              lastState_terminal_of_pureRun_height
                t
                (by simpa [O, k] using hss')
            simp [O, hz]
      _ =
        (pmfPi μ).bind
          (fun π =>
            t.evalDist
              (pureToBehavioral
                (GameTheory.EFG.descendPureProfileCore
                  t π))) := by
          refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
          intro π _hπ
          simpa [O, k] using
            runDistPure_bind_evalDist_core t π k
      _ =
        (Math.ProbabilityMassFunction.pushforward
          (mixedProfileJoint muP)
          (GameTheory.EFG.liftPureProfileCore t)).bind
            (fun π =>
              t.evalDist
                (pureToBehavioral
                  (GameTheory.EFG.descendPureProfileCore
                    t π))) := by
          rw [liftMixedProfileCore_joint t muP]
      _ =
        (mixedProfileJoint muP).bind
          (fun pi => t.evalDist (pureToBehavioral pi)) := by
          rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (mixedProfileJoint muP) _ _ ?_
          intro pi _hpi
          simp
  calc
    t.evalDist σ =
      (O.runDist k β).bind (fun ss => (O.lastState ss).evalDist σ) := by
        symm
        exact hleft
    _ =
      ((pmfPi μ).bind (O.runDistPure k)).bind
        (fun ss => (O.lastState ss).evalDist σ) := by
          simpa [O, k, μ] using congrArg
            (fun d => d.bind (fun ss => (O.lastState ss).evalDist σ)) hβ
    _ =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist (pureToBehavioral pi)) := hright

/-- **Kuhn's theorem (mixed → behavioral direction).**
    For any game tree with perfect recall and any mixed strategy profile,
    there exists a behavioral strategy profile that induces the same
    outcome distribution. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral pi)) := by
  obtain ⟨β, hβ⟩ :=
    kuhn_mixed_to_behavioral_core t hpr muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore t β
  refine ⟨σ, ?_⟩
  simpa [σ] using
    compiledCore_runEq_to_evalDistEq t muP hβ

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (mixed → behavioral). -/
theorem kuhn_mixed_to_behavioral_udist (G : EFGGame)
    (hpr : PerfectRecall G.tree) (muP : MixedProfile G.inf) :
    ∃ σ : BehavioralProfile G.inf,
      G.toKernelGame.udist σ =
      (mixedProfileJoint (S := G.inf) muP).bind
        (fun pi => G.toKernelGame.udist (pureToBehavioral pi)) := by
  obtain ⟨σ, hσ⟩ := kuhn_mixed_to_behavioral G.tree hpr muP
  exact ⟨σ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [hσ, PMF.bind_bind]⟩

end EFG
