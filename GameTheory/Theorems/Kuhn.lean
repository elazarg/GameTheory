import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.BehavioralToMixed
import GameTheory.Theorems.Kuhn.CorrelatedRealization

/-!
# GameTheory.Theorems.Kuhn

Kuhn's theorem: behavioral and mixed strategy equivalence.

The canonical proofs live on `ObsModel` (observation-indexed actions over a
deterministic stochastic machine):
- **B→M** (`kuhn_behavioral_to_mixed` in `BehavioralToMixed.lean`): no recall needed
- **M→B** (`kuhn_mixed_to_behavioral_pspr` in `CorrelatedRealization.lean`): requires
  `PerStepPlayerRecall`

This file re-exports the ObsModel results and provides generic outcome-equality
schema types used by language-specific Kuhn reductions.
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
