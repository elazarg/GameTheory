/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.InfoModel.Lemmas.Profiles
import Math.ProbabilityMassFunction

/-!
# GameTheory.Languages.InfoModel.Lemmas.Disintegration
-/

namespace GameTheory
namespace InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

/-- Mixed evaluation disintegration at one queried coordinate. -/
theorem mixedEval_disintegrate_coordinate
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    [Finite (PureProfile I)]
    (μ : MixedProfile (I := I))
    (k : Nat)
    (i : ι) (v : I.LocalTrace i) :
    evalMixedCanonical (I := I) D k μ =
      (Math.ProbabilityMassFunction.pushforward
        (mixedJoint (I := I) μ)
        (pureActionAt (I := I) i v)).bind
        (fun a =>
          (Math.ProbabilityMassFunction.condOn
            (mixedJoint (I := I) μ)
            (pureActionAt (I := I) i v) a).bind
            (D.evalPure k)) := by
  letI : Fintype (PureProfile I) := Fintype.ofFinite (PureProfile I)
  simpa [evalMixedCanonical, pureActionAt] using
    (Math.ProbabilityMassFunction.bind_pushforward_condOn
      (μ := mixedJoint (I := I) μ) (proj := pureActionAt (I := I) i v) (g := D.evalPure k))

/-- Evaluation identity for the canonical realization. -/
theorem evalBehavioral_realize_eq_evalMixed
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (k : Nat)
    (μ : MixedProfile (I := I))
    (hRun :
      D.runDist k (realizeBehavioralCanonical (I := I) μ) =
        (mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π)) :
    D.evalBehavioral k (realizeBehavioralCanonical (I := I) μ) =
      evalMixedCanonical (I := I) D k μ := by
  unfold Execution.Dynamics.evalBehavioral evalMixedCanonical
  rw [hRun]
  rw [Math.ProbabilityMassFunction.pushforward_bind]
  rfl

end InfoModel
end GameTheory
