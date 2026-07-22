/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Kuhn.KuhnModel
import GameTheory.Languages.Kuhn.ObsModel
import GameTheory.Languages.Kuhn.BehavioralToMixedCore
import GameTheory.Languages.Kuhn.MixedToBehavioralCore

/-!
# GameTheory.Languages.Kuhn

Reusable observation-model infrastructure and core Kuhn equivalence facts used
by the language compilers.

## Recall vocabulary across language layers

`PerfectRecall` is intentionally namespaced because each language exposes a
different history representation. The currently formalized notions are:

- `EFG.PerfectRecall`: the classical extensive-form condition that equal
  infosets carry equal own-action histories. `EFG.AugmentedGame.PerfectRecall`
  is exactly this predicate on the augmented game's underlying tree.
- `ObsModel.PerfectRecall`: observation recall plus action recall for the
  snapshot-refined generic Kuhn model. No generic implication from this
  predicate to the semantic M→B hypotheses is currently exported.
- `GameTheory.InfoModel.PerfectRecall`: observation plus action recall for the
  semantics-first relational information model. It is not an alias for the
  snapshot-refined `ObsModel` predicate.
- `GameTheory.FOSG.PerfectRecall`: observation plus action recall for native
  FOSG action-observation histories; `FOSG.perfectRecall` proves it by
  construction.
- `MAID.Struct.PerfectRecall`: the graphical ancestry/observation condition.
  `MAID_EFG.maidToEFG_perfectRecall` transports it to `EFG.PerfectRecall`.
- `MultiRoundGame.PerfectRecall`: view-history recall only. The standard
  observation-and-own-action condition is `MultiRoundGame.FullRecall`, with
  the proved implication `FullRecall.toPerfectRecall`; the Kuhn M→B result uses
  `FullRecall`.
- `Intrinsic.PerfectRecall`: the player-local choice-field condition for
  W-games and a configuration ordering; it directly drives the intrinsic
  `kuhn_equivalence` theorem.

No equivalence between differently represented notions should be inferred
unless a compiler or bridge theorem states it explicitly.
-/

namespace GameTheory
namespace Theorems

/-- Generic behavioral -> mixed outcome-equality schema. -/
def KuhnBehavioralToMixedOutcome
    (Behavioral Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ

/-- Generic mixed -> behavioral realization schema. -/
def KuhnMixedToBehavioralViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure

/-- Complete Kuhn statement (both directions) at outcome-distribution level. -/
def KuhnCompleteViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  (∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ) ∧
  (∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure)

end Theorems
end GameTheory
