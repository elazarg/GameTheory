/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Expressiveness.Relations
import GameTheory.Languages.Bridges.FOSG.AugmentedEFG

/-!
# EFG / FOSG Expressiveness Packaging

This file packages the existing bounded-horizon FOSG-to-EFG bridge in the
language-expressiveness vocabulary.

The important structural fact already proved by
`GameTheory.Languages.Bridges.FOSG.AugmentedEFG` is:

* a bounded-horizon FOSG can be presented as a finite EFG tree;
* each simultaneous FOSG step is serialized as one EFG decision opportunity per
  player followed by one chance node for the stochastic world transition;
* legal FOSG behavioral profiles translate to EFG behavioral profiles with the
  same native history outcome law.

The bridge EFG uses the canonical finite player type `Fin (Fintype.card ι)`, so
the compiled EFG kernel is reindexed back to the source player type `ι`.
-/

namespace GameTheory
namespace Languages
namespace Expressiveness

open FOSG.AugmentedEFGBridge

/-- A bounded-horizon FOSG presentation with the finiteness assumptions needed
for compilation and for the existing EFG bridge.

The bounded horizon is the exact hypothesis that makes the native terminal-law
kernel and the finite EFG tree agree. -/
structure BoundedFOSGPresentation (ι : Type) [DecidableEq ι] [Fintype ι] where
  W : Type
  Act : ι → Type
  PrivObs : ι → Type
  PubObs : Type
  [instFintypeW : Fintype W]
  [instFintypeAct : ∀ i, Fintype (Act i)]
  [instDecidableEqAct : ∀ i, DecidableEq (Act i)]
  [instFintypePrivObs : ∀ i, Fintype (PrivObs i)]
  [instDecidableEqPrivObs : ∀ i, DecidableEq (PrivObs i)]
  [instFintypePubObs : Fintype PubObs]
  [instDecidableEqPubObs : DecidableEq PubObs]
  game : FOSG ι W Act PrivObs PubObs
  [instDecidablePredTerminal : DecidablePred game.terminal]
  horizon : Nat
  bounded : game.BoundedHorizon horizon

attribute [instance]
  BoundedFOSGPresentation.instFintypeW
  BoundedFOSGPresentation.instFintypeAct
  BoundedFOSGPresentation.instDecidableEqAct
  BoundedFOSGPresentation.instFintypePrivObs
  BoundedFOSGPresentation.instDecidableEqPrivObs
  BoundedFOSGPresentation.instFintypePubObs
  BoundedFOSGPresentation.instDecidableEqPubObs
  BoundedFOSGPresentation.instDecidablePredTerminal

namespace BoundedFOSGPresentation

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Bounded horizon and finite step data give a finite realized-history type. -/
@[reducible]
noncomputable def historyFintype (X : BoundedFOSGPresentation ι) :
    Fintype X.game.History := by
  classical
  exact X.game.historyFintypeOfBoundedHorizon X.bounded

/-- Native bounded-horizon FOSG kernel semantics. -/
noncomputable def toKernelGame (X : BoundedFOSGPresentation ι) :
    KernelGame ι := by
  classical
  letI : Fintype X.game.History := X.historyFintype
  exact X.game.toKernelGameOfBoundedHorizon X.bounded

/-- Plain finite EFG obtained by serializing each FOSG step. -/
noncomputable def toPlainEFG (X : BoundedFOSGPresentation ι) : EFG.EFGGame := by
  classical
  exact FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon
    (G := X.game) X.bounded

/-- The generated EFG kernel, reindexed from the bridge's canonical player type
`Fin (Fintype.card ι)` back to the native FOSG player type `ι`. -/
noncomputable def toPlainEFGKernelGame (X : BoundedFOSGPresentation ι) :
    KernelGame ι :=
  KernelGame.reindex (FOSG.AugmentedEFGBridge.playerEquiv (ι := ι))
    X.toPlainEFG.toKernelGame

/-- The generated augmented EFG for the bounded-horizon FOSG. -/
noncomputable def toAugmentedEFG (X : BoundedFOSGPresentation ι) :
    EFG.AugmentedGame := by
  classical
  exact FOSG.AugmentedEFGBridge.toAugmentedOfBoundedHorizon
    (G := X.game) X.bounded

/-- Translate one native FOSG legal behavioral strategy to the corresponding
player's strategy in the serialized EFG presentation. -/
noncomputable def translateStrategy (X : BoundedFOSGPresentation ι) (i : ι) :
    X.game.LegalBehavioralStrategy i → X.toPlainEFGKernelGame.Strategy i := by
  classical
  intro σi
  change EFG.BehavioralStrategy
    (FOSG.AugmentedEFGBridge.infoStructure (G := X.game) X.horizon)
    (FOSG.AugmentedEFGBridge.playerEquiv (ι := ι) i)
  intro I
  exact PMF.map
    (fun a =>
      FOSG.AugmentedEFGBridge.indexOfAction (G := X.game) I
        (cast (by rw [FOSG.AugmentedEFGBridge.origPlayer_playerEquiv (ι := ι) i]) a))
    (σi.1
      (cast (by rw [FOSG.AugmentedEFGBridge.origPlayer_playerEquiv (ι := ι) i])
        (FOSG.AugmentedEFGBridge.Word.toList I)))

/-- Profile-level forward translation into the reindexed serialized EFG
kernel. -/
noncomputable def translateProfile (X : BoundedFOSGPresentation ι) :
    KernelGame.Profile X.toKernelGame → KernelGame.Profile X.toPlainEFGKernelGame :=
  fun σ i => by
    classical
    change EFG.BehavioralStrategy
      (FOSG.AugmentedEFGBridge.infoStructure (G := X.game) X.horizon)
      (FOSG.AugmentedEFGBridge.playerEquiv (ι := ι) i)
    exact FOSG.AugmentedEFGBridge.translateBehavioralProfile
      (G := X.game) σ (FOSG.AugmentedEFGBridge.playerEquiv (ι := ι) i)

/-- The reindexed generated EFG has the same outcome law as the native
bounded-horizon FOSG under the forward profile translation. -/
theorem toPlainEFGKernelGame_outcomeKernel_eq_native
    (X : BoundedFOSGPresentation ι) (σ : KernelGame.Profile X.toKernelGame) :
    X.toPlainEFGKernelGame.outcomeKernel (X.translateProfile σ) =
      X.toKernelGame.outcomeKernel σ := by
  classical
  letI : Fintype X.game.History := X.historyFintype
  change X.toPlainEFG.toKernelGame.outcomeKernel
      (fun p =>
        cast (congrArg X.toPlainEFG.toKernelGame.Strategy
          (FOSG.AugmentedEFGBridge.playerEquiv_origPlayer (ι := ι) p))
          (X.translateProfile σ
            (FOSG.AugmentedEFGBridge.origPlayer (ι := ι) p))) =
    (X.game.toKernelGameOfBoundedHorizon X.bounded).outcomeKernel σ
  have hprofile :
      (fun p =>
        cast (congrArg X.toPlainEFG.toKernelGame.Strategy
          (FOSG.AugmentedEFGBridge.playerEquiv_origPlayer (ι := ι) p))
          (X.translateProfile σ
            (FOSG.AugmentedEFGBridge.origPlayer (ι := ι) p))) =
      FOSG.AugmentedEFGBridge.translateBehavioralProfile
        (G := X.game) σ := by
    funext p
    let q : FOSG.AugmentedEFGBridge.PlayerIx (ι := ι) :=
      FOSG.AugmentedEFGBridge.playerEquiv (ι := ι)
        (FOSG.AugmentedEFGBridge.origPlayer (ι := ι) p)
    have hq : q = p :=
      FOSG.AugmentedEFGBridge.playerEquiv_origPlayer (ι := ι) p
    change cast (congrArg X.toPlainEFG.toKernelGame.Strategy hq)
        (FOSG.AugmentedEFGBridge.translateBehavioralProfile (G := X.game) σ q) =
      FOSG.AugmentedEFGBridge.translateBehavioralProfile (G := X.game) σ p
    induction hq
    rfl
  have hout :=
    FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon_outcomeKernel_eq_nativeBounded
    (G := X.game) X.bounded σ
  exact (congrArg X.toPlainEFG.toKernelGame.outcomeKernel hprofile).trans hout

/-- Utility-distribution equality for the native bounded FOSG and its
serialized EFG, under the forward profile translation. -/
theorem toPlainEFGKernelGame_udist_eq_native
    (X : BoundedFOSGPresentation ι) (σ : KernelGame.Profile X.toKernelGame) :
    X.toPlainEFGKernelGame.udist (X.translateProfile σ) =
      X.toKernelGame.udist σ := by
  classical
  unfold KernelGame.udist
  rw [X.toPlainEFGKernelGame_outcomeKernel_eq_native σ]
  congr 1
  funext h
  congr 1
  funext i
  simp [toPlainEFGKernelGame, KernelGame.reindex, toPlainEFG, toKernelGame,
    FOSG.AugmentedEFGBridge.toPlainEFGOfBoundedHorizon,
    FOSG.AugmentedEFGBridge.toPlainEFGAtHorizon,
    EFG.EFGGame.toKernelGame, FOSG.toKernelGameOfBoundedHorizon]
  rfl

end BoundedFOSGPresentation

/-- Native bounded-horizon FOSGs as a language over player type `ι`. -/
noncomputable def BoundedFOSGLanguage (ι : Type)
    [DecidableEq ι] [Fintype ι] : Language ι where
  Syntax := BoundedFOSGPresentation ι
  compile := BoundedFOSGPresentation.toKernelGame

/-- The EFG sublanguage generated by serializing bounded-horizon FOSGs. -/
noncomputable def FOSGPlainEFGLanguage (ι : Type)
    [DecidableEq ι] [Fintype ι] : Language ι where
  Syntax := BoundedFOSGPresentation ι
  compile := BoundedFOSGPresentation.toPlainEFGKernelGame

/-- Every bounded FOSG has a serialized EFG presentation with the same utility
distribution under the bridge profile translation. -/
noncomputable def boundedFOSGToPlainEFGProfileMapReduction (ι : Type)
    [DecidableEq ι] [Fintype ι] :
    Reduction (BoundedFOSGLanguage ι) (FOSGPlainEFGLanguage ι)
      ProfileMapUtilityDistributionSimulation where
  translate := _root_.id
  sound := fun X =>
    ⟨X.translateProfile, X.toPlainEFGKernelGame_udist_eq_native⟩

/-- Bounded-horizon FOSGs are no more expressive than the EFGs generated by
serializing them, under the directed profile-map utility-distribution lens. -/
theorem boundedFOSG_expressiveLe_plainEFG_profileMap (ι : Type)
    [DecidableEq ι] [Fintype ι] :
    (profileMapUtilityDistributionSimulationLens ι).ExpressiveLe
      (BoundedFOSGLanguage ι) (FOSGPlainEFGLanguage ι) :=
  (profileMapUtilityDistributionSimulationLens ι).expressiveLe_of_reduction
    (boundedFOSGToPlainEFGProfileMapReduction ι)

end Expressiveness
end Languages
end GameTheory
