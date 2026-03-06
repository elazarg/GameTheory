import GameTheory.Theorems.KuhnCore
import GameTheory.Theorems.KuhnMixedToBehavioral

namespace GameTheory
namespace Theorems

section InfoModel

open Execution

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

/-- Kuhn completeness at the outcome-distribution level for an `InfoModel`.

Conceptually, the mixed-to-behavioral direction is driven by a reachable-prefix
distributive law: conditioning the mixed profile on the realized local history
distributes over sequencing/continuation. -/
theorem kuhn_complete
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

