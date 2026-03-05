import GameTheory.Theorems.KuhnCore
import GameTheory.Theorems.KuhnMixedToBehavioral

namespace GameTheory
namespace Theorems

section InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

/-- **Kuhn (complete, both directions)** at the `InfoModel` level.

Do not modify this by strengthening assumptions in either direction.
If proof infrastructure is missing, keep the exact statement and refine lemmas.
-/
theorem kuhn_complete
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  exact ⟨
    kuhn_behavioral_to_mixed (I := I) (D := D) (k := k),
    kuhn_mixed_to_behavioral (I := I) (D := D) (k := k) hPR
  ⟩

end InfoModel

end Theorems
end GameTheory

