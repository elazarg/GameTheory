import GameTheory.Theorems.Kuhn.Core
import GameTheory.Theorems.Kuhn.MixedToBehavioral
import GameTheory.Model.Lemmas.HistoryCover

namespace GameTheory
namespace Theorems

section InfoModel

open Execution

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)
variable (D : Execution.Dynamics I)
variable (k : Nat)

/-- Kuhn completeness at the outcome-distribution level for an `InfoModel`.

Conceptually, the mixed-to-behavioral direction is driven by a reachable-prefix
distributive law: conditioning the mixed profile on the realized local history
distributes over sequencing/continuation. -/
theorem kuhn_complete
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
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
    [∀ i, Fintype (Option (Act i))]
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
    [∀ i, Fintype (Option (Act i))]
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

/-- Cover-based mixed-to-behavioral Kuhn theorem on full profiles. -/
theorem kuhn_mixed_to_behavioral_via_cover
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (I.RestrictedLocalPure H i)]
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (hCover : I.CoversHistoriesUpTo H k)
    (hStepIndep : ∀ μ n, I.RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I)
      (InfoModel.MixedProfile (I := I))
      (PureProfile I)
      I.Outcome
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  intro μ
  let μr : I.RestrictedMixedProfile H := I.restrictMixedProfile H μ
  obtain ⟨σr, hσr⟩ :=
    kuhn_mixed_to_behavioral_restricted (I := I) (D := D) (k := k) H hStepIndep μr
  refine ⟨I.extendRestrictedBehavioralProfile H σr, ?_⟩
  have hbridge :
      (I.restrictedMixedJointRaw H μr).bind
          (evalRestrictedPure (I := I) D k H) =
        (I.restrictedMixedJoint H μr).bind (D.evalPure k) := by
    simpa [evalRestrictedPure] using
      InfoModel.restrictedMixedJointRaw_bind_eq_restrictedMixedJoint_bind
        (I := I) (H := H) μr (fun π => D.evalPure k π)
  have hpush :
      I.restrictedMixedJoint H μr =
        Math.ProbabilityMassFunction.pushforward
          (InfoModel.mixedJoint (I := I) μ)
          (fun π => I.extendRestrictedPureProfile H
            (I.restrictPureProfile H π)) := by
    calc
      I.restrictedMixedJoint H μr
          = InfoModel.mixedJoint (I := I)
              (I.extendRestrictedMixedProfile H μr) := by
                symm
                exact InfoModel.mixedJoint_extendRestrictedMixedProfile_eq_restrictedMixedJoint
                  (I := I) (H := H) μr
      _ =
        Math.ProbabilityMassFunction.pushforward
          (InfoModel.mixedJoint (I := I) μ)
          (fun π => I.extendRestrictedPureProfile H
            (I.restrictPureProfile H π)) := by
              simpa [μr] using
                InfoModel.mixedJoint_extendRestrict_eq_pushforward (I := I) (H := H) μ
  have hpure :
      (Math.ProbabilityMassFunction.pushforward
        (InfoModel.mixedJoint (I := I) μ)
        (fun π => I.extendRestrictedPureProfile H (I.restrictPureProfile H π))).bind
          (D.evalPure k) =
        (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
    rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind]
    have hpure_bind :
        ((InfoModel.mixedJoint (I := I) μ).bind
          (fun π =>
            (PMF.pure (I.extendRestrictedPureProfile H (I.restrictPureProfile H π))).bind
              (D.evalPure k))) =
          (InfoModel.mixedJoint (I := I) μ).bind
            (fun π =>
              D.evalPure k
                (I.extendRestrictedPureProfile H (I.restrictPureProfile H π))) := by
      apply Math.ProbabilityMassFunction.bind_congr_on_support
        (μ := InfoModel.mixedJoint (I := I) μ)
        (f := fun π =>
          (PMF.pure (I.extendRestrictedPureProfile H (I.restrictPureProfile H π))).bind
            (D.evalPure k))
        (g := fun π => D.evalPure k (I.extendRestrictedPureProfile H (I.restrictPureProfile H π)))
      intro π _
      rw [PMF.pure_bind]
    rw [hpure_bind]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
      (μ := InfoModel.mixedJoint (I := I) μ)
      (f := fun π => D.evalPure k (I.extendRestrictedPureProfile H (I.restrictPureProfile H π)))
      (g := fun π => D.evalPure k π)
    intro π _
    exact I.evalPure_eq_extend_restrict_pure_of_cover (D := D) hCover π
  calc
    D.evalBehavioral k (I.extendRestrictedBehavioralProfile H σr)
        = evalRestrictedBehavioral (I := I) D k H σr := rfl
    _ = (I.restrictedMixedJointRaw H μr).bind
          (evalRestrictedPure (I := I) D k H) := hσr
    _ = (I.restrictedMixedJoint H μr).bind (D.evalPure k) := hbridge
    _ =
      (Math.ProbabilityMassFunction.pushforward
        (InfoModel.mixedJoint (I := I) μ)
        (fun π => I.extendRestrictedPureProfile H
          (I.restrictPureProfile H π))).bind
        (D.evalPure k) := by rw [hpush]
    _ = (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := hpure

/-- Cover-based full Kuhn completeness theorem. -/
theorem kuhn_complete_via_cover
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, DecidableEq (I.LocalTrace i)]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (I.RestrictedLocalPure H i)]
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (hCover : I.CoversHistoriesUpTo H k)
    (hStepIndep : ∀ μ n, I.RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I)
      (InfoModel.MixedProfile (I := I))
      (PureProfile I)
      I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (InfoModel.mixedJoint (I := I))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  refine ⟨kuhn_behavioral_to_mixed (I := I) (D := D) (k := k), ?_⟩
  exact kuhn_mixed_to_behavioral_via_cover (I := I) (D := D) (k := k) H hCover hStepIndep

end InfoModel

end Theorems
end GameTheory

