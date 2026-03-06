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

/-- Restricted finite-cover Kuhn completeness. This is the general bounded
interface that avoids assuming the full ambient local-trace type is finite. -/
theorem kuhn_complete_restricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (I.RestrictedLocalPure H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, I.RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      (I.RestrictedBehavioralProfile H)
      (I.RestrictedMixedProfile H)
      (I.RestrictedPureProfile H)
      I.Outcome
      (mixedOfBehavioralCanonicalRestricted (I := I) H)
      (I.restrictedMixedJointRaw H)
      (evalRestrictedBehavioral (I := I) D k H)
      (evalRestrictedPure (I := I) D k H) := by
  exact kuhn_complete_of_infoModel_restricted (I := I) (D := D) (k := k) H hStepIndep

/-- Restricted finite-cover mixed-to-behavioral direction. -/
theorem kuhn_mixed_to_behavioral_restricted
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (I.RestrictedLocalPure H i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hStepIndep : ∀ μ n, I.RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      (I.RestrictedBehavioralProfile H)
      (I.RestrictedMixedProfile H)
      (I.RestrictedPureProfile H)
      I.Outcome
      (I.restrictedMixedJointRaw H)
      (evalRestrictedBehavioral (I := I) D k H)
      (evalRestrictedPure (I := I) D k H) := by
  exact kuhn_mixed_to_behavioral_core_restricted (I := I) (D := D) (k := k) H hStepIndep

end InfoModel

end Theorems
end GameTheory

