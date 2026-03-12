import GameTheory.Theorems.Kuhn.KuhnModel
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.BehavioralToMixed
import GameTheory.Theorems.Kuhn.CorrelatedRealization

/-!
# GameTheory.Theorems.Kuhn

Kuhn's theorem: behavioral and mixed strategy equivalence.

The semantic core now lives on `KuhnModel`/`ObsModelCore`:
- **B→M** (`ObsModelCore.kuhn_behavioral_to_mixed` in
  `BehavioralToMixedCore.lean`): no recall needed, but requires the semantic
  horizon-separation condition used to fold sequential randomization into an
  ex-ante product distribution.
- **M→B** (`ObsModelCore.kuhn_mixed_to_behavioral_semantic` in
  `CorrelatedRealization.lean`): stated over semantic step/locality
  assumptions.

`ObsModel` is now the stronger snapshot-refined compatibility layer. It is
useful when a client naturally has faithful observation-history snapshots and
wants syntactic recall corollaries such as
`kuhn_mixed_to_behavioral_pspr` or automatic `HorizonSeparation`.

This file re-exports the Kuhn model, the core theorems, the migration wrappers,
and the generic outcome-equality schema types used by language-specific Kuhn
reductions.
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
