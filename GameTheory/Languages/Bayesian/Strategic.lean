module

/-
# Bayesian strategic-form transfer

The solution-concept-free compiler identifies local policies with contingent
plans. This leaf transports Nash equilibrium for arbitrary preferences on
outcome laws; expected utility is a specialization preserving definedness.
-/

public import GameTheory.Languages.Bayesian
public import GameTheory.Core.BayesianEquilibrium

@[expose] public section

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
    (law : PMF B.signature.Outcome) :
    expectedUtility (protocolUtility B) who (law.map some) =
      expectedUtility B.utility who law := by
  simpa only [protocolUtility, BayesianGame.utility, expectedUtility] using
    expectedUtility_map (protocolUtility B) who some law

theorem expectedUtility_toProtocolForm (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (who : ι)
    (policies : Profile (informationModel B).strategicSignature) :
    expectedUtility (protocolUtility B) who
        ((toProtocolForm B).play policies) =
      expectedUtility B.utility who
        (B.toForm.play (planOfPolicyProfile B policies)) := by
  calc
    _ = expectedUtility (protocolUtility B) who
          ((B.toForm.play (planOfPolicyProfile B policies)).map some) :=
      expectedUtility_congr_law (protocolUtility B) who
        (toProtocolForm_play B policies)
    _ = _ := expectedUtility_protocolUtility_map B who _

variable [DecidableEq ι]

/-- The compiler transports every preference on protocol outcome laws. The
source preference is its pullback along the completed-outcome embedding. -/
theorem isNash_toProtocolForm_iff_of_preference
    (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (prefers : WeakPreference ι (toProtocolForm B).sig.Outcome)
    (policies : Profile (informationModel B).strategicSignature) :
    IsNash (toProtocolForm B) prefers policies ↔
      IsNash B.toForm (Preference.comapOutcome some prefers)
        (planOfPolicyProfile B policies) := by
  constructor
  · intro hnash
    rw [isNash_iff] at hnash ⊢
    intro who replacement
    have hcomparison := hnash who (Policy.ofPlan replacement)
    have hdev := toProtocolForm_play B
      (Profile.update policies who (Policy.ofPlan replacement))
    rw [planOfPolicyProfile_update, Policy.toPlan_ofPlan] at hdev
    exact (congrArg₂ (prefers who) (toProtocolForm_play B policies) hdev).mp hcomparison
  · intro hnash
    rw [isNash_iff] at hnash ⊢
    intro who replacement
    have hcomparison := hnash who (Policy.toPlan replacement)
    have hdev := toProtocolForm_play B (Profile.update policies who replacement)
    rw [planOfPolicyProfile_update] at hdev
    exact (congrArg₂ (prefers who) (toProtocolForm_play B policies) hdev).mpr hcomparison

/-- Expected utility specializes preference-generic compiler transport,
including existence of both compared expectations. -/
theorem isNash_toProtocolForm_iff_planOfPolicyProfile
    (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B)) policies ↔
      IsNash B.toForm (euPreference B.utility)
        (planOfPolicyProfile B policies) := by
  have hpref : Preference.comapOutcome some (euPreference (protocolUtility B)) =
      euPreference B.utility := by
    funext who preferred alternative
    exact propext (euPreference_map (protocolUtility B) who some preferred alternative)
  rw [← hpref]
  exact isNash_toProtocolForm_iff_of_preference B (euPreference (protocolUtility B)) policies

theorem isNash_toProtocolForm_iff (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    IsNash (toProtocolForm B) (euPreference (protocolUtility B))
        (policyProfileOfPlan B plan) ↔
      IsNash B.toForm (euPreference B.utility) plan := by
  rw [isNash_toProtocolForm_iff_planOfPolicyProfile,
    planOfPolicyProfile_policyProfileOfPlan]

end GameTheory.Languages.Bayesian
