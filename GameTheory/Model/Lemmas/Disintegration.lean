import GameTheory.Model.Lemmas.Profiles
import Math.ProbabilityMassFunction

namespace GameTheory
namespace InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)

/-- Mixed evaluation disintegration at one queried coordinate. -/
theorem mixedEval_disintegrate_coordinate
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    [Fintype (PureProfile I)]
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
  simpa [evalMixedCanonical, pureActionAt] using
    (Math.ProbabilityMassFunction.bind_pushforward_condOn
      (μ := mixedJoint (I := I) μ) (proj := pureActionAt (I := I) i v) (g := D.evalPure k))

/-- Evaluation identity for the canonical realization. -/
theorem evalBehavioral_realize_eq_evalMixed
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (k : Nat)
    (μ : MixedProfile (I := I))
    (hRun :
      D.runDist k (realizeBehavioralCanonical (I := I) μ) =
        (mixedJoint (I := I) μ).bind (fun π => D.runDistPure k π)) :
    D.evalBehavioral k (realizeBehavioralCanonical (I := I) μ) =
      evalMixedCanonical (I := I) D k μ := by
  unfold Execution.Dynamics.evalBehavioral evalMixedCanonical
  rw [hRun]
  simpa [Execution.Dynamics.evalPure] using
    (Math.ProbabilityMassFunction.pushforward_bind
      (μ := mixedJoint (I := I) μ)
      (k := fun π => D.runDistPure k π)
      (f := I.outcomeOfStates))

end InfoModel
end GameTheory
