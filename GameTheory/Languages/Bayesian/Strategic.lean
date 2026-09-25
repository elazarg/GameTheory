/-
# Bayesian strategic-form transfer

The solution-concept-free compiler identifies local policies with contingent
plans. This leaf transports guarded expected utility and Nash equilibrium.
-/

import GameTheory.Languages.Bayesian
import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory.Languages.Bayesian

open GameTheory GameTheory.Math.Probability

universe uι

variable {ι : Type uι}

/-- Realized Bayesian payoff, extended by zero to an unfinished protocol outcome. -/
def protocolUtility (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    Utility (toProtocolForm B).sig :=
  fun outcome who =>
    match outcome with
    | some realized => B.utility realized who
    | none => 0

theorem expectedUtility_protocolUtility_map (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (who : ι)
    (law : PMF B.signature.Outcome)
    (h : UtilityIntegrable B.utility who law) :
    expectedUtility (protocolUtility B) who (law.map some)
        ((payoffIntegrable_map_iff some law
          (fun outcome => protocolUtility B outcome who)).mpr
          (by simpa only [Function.comp_def, protocolUtility] using h)) =
      expectedUtility B.utility who law h := by
  simpa only [protocolUtility, BayesianGame.utility, expectedUtility] using
    expectedUtility_map (protocolUtility B) who some law
      ((payoffIntegrable_map_iff some law
        (fun outcome => protocolUtility B outcome who)).mpr
        (by simpa only [Function.comp_def, protocolUtility] using h))

theorem expectedUtility_toProtocolForm (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (who : ι)
    (policies : Profile (informationModel B).strategicSignature)
    (h : UtilityIntegrable B.utility who
      (B.toForm.play (planOfPolicyProfile B policies))) :
    expectedUtility (protocolUtility B) who
        ((toProtocolForm B).play policies)
        (payoffIntegrable_congr_law
          (toProtocolForm_play B policies).symm
          ((payoffIntegrable_map_iff some
            (B.toForm.play (planOfPolicyProfile B policies))
            (fun outcome => protocolUtility B outcome who)).mpr
            (by simpa only [Function.comp_def, protocolUtility] using h))) =
      expectedUtility B.utility who
        (B.toForm.play (planOfPolicyProfile B policies)) h := by
  calc
    _ = expectedUtility (protocolUtility B) who
          ((B.toForm.play (planOfPolicyProfile B policies)).map some)
          ((payoffIntegrable_map_iff some
            (B.toForm.play (planOfPolicyProfile B policies))
            (fun outcome => protocolUtility B outcome who)).mpr
            (by simpa only [Function.comp_def, protocolUtility] using h)) :=
      expectedUtility_congr_law (protocolUtility B) who
        (toProtocolForm_play B policies) _ _
    _ = _ := expectedUtility_protocolUtility_map B who _ h

variable [DecidableEq ι]

/-- The protocol and direct game compare the same two actual laws. -/
theorem isNash_toProtocolForm_iff_planOfPolicyProfile
    (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B)) policies ↔
      IsNash B.toForm (euPreference B.utility)
        (planOfPolicyProfile B policies) := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro hnash who replacement
    have h := hnash who (Policy.ofPlan replacement)
    have hmap :
        euPreference (protocolUtility B) who
          ((B.toForm.play (planOfPolicyProfile B policies)).map some)
          ((B.toForm.play
            (planOfPolicyProfile B
              (Profile.update policies who (Policy.ofPlan replacement)))).map some) := by
      rw [← toProtocolForm_play B policies,
        ← toProtocolForm_play B
          (Profile.update policies who (Policy.ofPlan replacement))]
      exact h
    have hdirect := (euPreference_map (protocolUtility B) who some _ _).mp hmap
    have hutil :
        (fun outcome => protocolUtility B (some outcome)) = B.utility := by
      funext outcome who
      rfl
    rw [hutil] at hdirect
    simpa only [planOfPolicyProfile_update, Policy.toPlan_ofPlan] using hdirect
  · intro hnash who replacement
    have h := hnash who (Policy.toPlan replacement)
    have hdirect :
        euPreference B.utility who
          (B.toForm.play (planOfPolicyProfile B policies))
          (B.toForm.play
            (planOfPolicyProfile B (Profile.update policies who replacement))) := by
      simpa only [planOfPolicyProfile_update] using h
    have hmap :
        euPreference (protocolUtility B) who
          ((B.toForm.play (planOfPolicyProfile B policies)).map some)
          ((B.toForm.play
            (planOfPolicyProfile B
              (Profile.update policies who replacement))).map some) :=
      (euPreference_map (protocolUtility B) who some _ _).mpr (by
        have hutil :
            (fun outcome => protocolUtility B (some outcome)) = B.utility := by
          funext outcome who
          rfl
        rw [hutil]
        exact hdirect)
    have hcong := congrArg₂ (euPreference (protocolUtility B) who)
      (toProtocolForm_play B policies)
      (toProtocolForm_play B (Profile.update policies who replacement))
    exact hcong.mpr hmap

theorem isNash_toProtocolForm_iff (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B))
        (policyProfileOfPlan B plan) ↔
      IsNash B.toForm (euPreference B.utility) plan := by
  rw [isNash_toProtocolForm_iff_planOfPolicyProfile,
    planOfPolicyProfile_policyProfileOfPlan]

end GameTheory.Languages.Bayesian
