/-
# Bayesian strategic-form transfer

The solution-concept-free Bayesian compiler identifies information-local
policies with type-contingent plans and proves equality of their outcome laws.
This leaf adds expected utility and packages those compiler facts as an
ordinary Nash equivalence.  It defines no Bayesian-specific equilibrium
predicate.
-/

import GameTheory.Languages.Bayesian
import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory.Languages.Bayesian

open GameTheory GameTheory.Probability

universe uι

variable {ι : Type uι}

/-- Evaluate a completed protocol outcome with the Bayesian game's utility.
The `none` branch is unreachable after the compiler's two-step horizon but
keeps the utility total on the protocol form's outcome carrier. -/
def protocolUtility (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    Utility (toProtocolForm B).sig :=
  fun outcome who =>
    match outcome with
    | some realized => B.utility realized who
    | none => 0

/-- Mapping a direct Bayesian outcome into the completed protocol carrier
preserves every player's expected utility. -/
@[simp]
theorem expectedUtility_protocolUtility_map (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (who : ι)
    (law : FinDist B.signature.Outcome) :
    expectedUtility (protocolUtility B) who (law.map some) =
      expectedUtility B.utility who law := by
  rw [expectedUtility_map]
  rfl

/-- The protocol-backed form evaluates exactly like the direct form after
recovering the policy profile's contingent plans. -/
@[simp]
theorem expectedUtility_toProtocolForm (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (who : ι)
    (policies : Profile (informationModel B).strategicSignature) :
    expectedUtility (protocolUtility B) who
        ((toProtocolForm B).play policies) =
      expectedUtility B.utility who
        (B.toForm.play (planOfPolicyProfile B policies)) := by
  rw [toProtocolForm_play, expectedUtility_protocolUtility_map]

variable [DecidableEq ι]

/-- Nash equilibrium of an arbitrary information-local policy profile is
exactly Nash equilibrium of its equivalent type-contingent plan profile in the
direct Bayesian form. -/
theorem isNash_toProtocolForm_iff_planOfPolicyProfile
    (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B)) policies ↔
      IsNash B.toForm (euPreference B.utility)
        (planOfPolicyProfile B policies) := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro hnash who replacement
    have hdeviation := hnash who (Policy.ofPlan replacement)
    have hdeviation' :
        expectedUtility (protocolUtility B) who
            ((toProtocolForm B).play
              (Profile.update policies who (Policy.ofPlan replacement))) ≤
          expectedUtility (protocolUtility B) who
            ((toProtocolForm B).play policies) :=
      hdeviation
    have hupdate :
        planOfPolicyProfile B
            (Profile.update policies who (Policy.ofPlan replacement)) =
          Profile.update (planOfPolicyProfile B policies) who replacement := by
      rw [planOfPolicyProfile_update, Policy.toPlan_ofPlan]
    have hupdateValue := congrArg
      (fun plan => expectedUtility B.utility who (B.toForm.play plan)) hupdate
    show
      expectedUtility B.utility who
          (B.toForm.play
            (Profile.update (planOfPolicyProfile B policies) who replacement)) ≤
        expectedUtility B.utility who
          (B.toForm.play (planOfPolicyProfile B policies))
    calc
      _ = expectedUtility B.utility who
          (B.toForm.play
            (planOfPolicyProfile B
              (Profile.update policies who (Policy.ofPlan replacement)))) :=
        hupdateValue.symm
      _ = expectedUtility (protocolUtility B) who
          ((toProtocolForm B).play
            (Profile.update policies who (Policy.ofPlan replacement))) :=
        (expectedUtility_toProtocolForm B who _).symm
      _ ≤ expectedUtility (protocolUtility B) who
          ((toProtocolForm B).play policies) := hdeviation'
      _ = expectedUtility B.utility who
          (B.toForm.play (planOfPolicyProfile B policies)) :=
        expectedUtility_toProtocolForm B who policies
  · intro hnash who replacement
    have hdeviation := hnash who (Policy.toPlan replacement)
    have hdeviation' :
        expectedUtility B.utility who
            (B.toForm.play
              (Profile.update (planOfPolicyProfile B policies) who
                (Policy.toPlan replacement))) ≤
          expectedUtility B.utility who
            (B.toForm.play (planOfPolicyProfile B policies)) :=
      hdeviation
    have hupdate := planOfPolicyProfile_update B policies who replacement
    have hupdateValue := congrArg
      (fun plan => expectedUtility B.utility who (B.toForm.play plan)) hupdate
    show
      expectedUtility (protocolUtility B) who
          ((toProtocolForm B).play
            (Profile.update policies who replacement)) ≤
        expectedUtility (protocolUtility B) who
          ((toProtocolForm B).play policies)
    calc
      _ = expectedUtility B.utility who
          (B.toForm.play
            (planOfPolicyProfile B
              (Profile.update policies who replacement))) :=
        expectedUtility_toProtocolForm B who _
      _ = expectedUtility B.utility who
          (B.toForm.play
            (Profile.update (planOfPolicyProfile B policies) who
              (Policy.toPlan replacement))) := hupdateValue
      _ ≤ expectedUtility B.utility who
          (B.toForm.play (planOfPolicyProfile B policies)) := hdeviation'
      _ = expectedUtility (protocolUtility B) who
          ((toProtocolForm B).play policies) :=
        (expectedUtility_toProtocolForm B who policies).symm

/-- The language-facing Nash transfer for a type-contingent plan.  The same
source player is the deviator on both sides, and its whole own-type plan is
transported through the policy/plan equivalence. -/
theorem isNash_toProtocolForm_iff (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B))
        (policyProfileOfPlan B plan) ↔
      IsNash B.toForm (euPreference B.utility) plan := by
  rw [isNash_toProtocolForm_iff_planOfPolicyProfile,
    planOfPolicyProfile_policyProfileOfPlan]

end GameTheory.Languages.Bayesian
