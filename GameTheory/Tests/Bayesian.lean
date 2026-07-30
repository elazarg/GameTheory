/-
# Bayesian compiler stress test

One player privately observes a fair bit and must report it. Matching the type
pays one and mismatching pays zero. Truthful reporting is interim-optimal at
both types, hence Nash in the direct form; the exact compiler law then transfers
the same profile to the information-local protocol form.
-/

import GameTheory.Core.BayesianEquilibrium
import GameTheory.Languages.Bayesian

noncomputable section

namespace GameTheory.Tests.Bayesian

open GameTheory GameTheory.Probability
open GameTheory.Languages.Bayesian

/-- A fair private bit. -/
def fairBit : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

/-- The fair bit as the sole player's type profile. -/
def bitPrior : FinDist (∀ _ : Unit, Bool) :=
  fairBit.map fun bit _ => bit

/-- Guess one's private bit. -/
def bitGame : BayesianGame Unit where
  Ty _ := Bool
  Act _ := Bool
  prior := bitPrior
  payoff types actions _ := if actions () = types () then 1 else 0

instance instNonemptyBitAction (i : Unit) : Nonempty (bitGame.Act i) :=
  ⟨false⟩

instance instFintypeBitType (i : Unit) : Fintype (bitGame.Ty i) :=
  inferInstanceAs (Fintype Bool)

instance instDecidableEqBitType (i : Unit) : DecidableEq (bitGame.Ty i) :=
  inferInstanceAs (DecidableEq Bool)

/-- Report the observed bit. -/
def truthful : Profile bitGame.signature :=
  fun _ ownType => ownType

/-- The acting policy receives a `Bool`, not the hidden type profile. -/
theorem truthful_policy_at (ownType : Bool) :
    (policyProfileOfPlan bitGame truthful ()).act (View.acting ownType) =
      some ownType := rfl

/-- The direct and protocol-backed forms agree on the truthful profile. -/
theorem truthful_protocol_law :
    (toProtocolForm bitGame).play (policyProfileOfPlan bitGame truthful) =
      (bitGame.toForm.play truthful).map some :=
  toProtocolForm_play_policyProfileOfPlan bitGame truthful

/-- Truthful reporting maximizes the prior-weighted interim value at every own
type. Both types have positive mass, so neither branch is vacuous. -/
theorem truthful_interim_optimal :
    ∀ (who : Unit) (ownType : bitGame.Ty who) (respond : bitGame.Act who),
      bitGame.interimValue who ownType truthful respond ≤
        bitGame.interimValue who ownType truthful (truthful who ownType) := by
  intro who ownType respond
  cases who
  unfold BayesianGame.interimValue
  apply FinDist.expect_mono
  intro types _
  by_cases htype : types () = ownType
  · simp [htype, bitGame, truthful]
    split <;> norm_num
  · simp [htype]

/-- The stable EXP-008 theorem supplies ordinary Nash directly; there is no
Bayes-specific equilibrium predicate. -/
theorem truthful_isNash :
    IsNash bitGame.toForm (euPreference bitGame.utility) truthful :=
  (bitGame.isNash_iff_interim truthful).2 truthful_interim_optimal

/-- Utility on the protocol form. The `none` branch is unreachable after two
steps but remains total for arbitrary histories. -/
def protocolUtility : Utility (toProtocolForm bitGame).sig :=
  fun outcome who =>
    match outcome with
    | some realized => bitGame.payoff realized.1 realized.2 who
    | none => 0

@[simp]
theorem protocolUtility_some (outcome : bitGame.signature.Outcome) (who : Unit) :
    protocolUtility (some outcome) who = bitGame.utility outcome who := rfl

@[simp]
theorem protocolUtility_realized (types : ∀ i, bitGame.Ty i)
    (actions : ∀ i, bitGame.Act i) (who : Unit) :
    protocolUtility (some (types, actions)) who =
      bitGame.payoff types actions who := rfl

theorem expectedUtility_protocol_map (who : Unit)
    (law : FinDist bitGame.signature.Outcome) :
    expectedUtility protocolUtility who (law.map some) =
      expectedUtility bitGame.utility who law := by
  rw [expectedUtility_map]
  unfold expectedUtility
  refine FinDist.expect_congr fun outcome _ => ?_
  cases outcome
  rfl

/-- The information-local policy profile is Nash in the protocol-backed form.
The proof uses only the exact compiler law, policy/plan equivalence, and the
ordinary direct-form Nash theorem. -/
theorem truthful_protocol_isNash :
    IsNash (toProtocolForm bitGame) (euPreference protocolUtility)
      (policyProfileOfPlan bitGame truthful) := by
  rw [isNash_iff]
  refine fun who (replacement : (informationModel bitGame).Policy who) => ?_
  have hnash := truthful_isNash
  rw [isNash_iff] at hnash
  have hdirect := hnash who (Policy.toPlan replacement)
  have hupdate :
      planOfPolicyProfile bitGame
          (Profile.update (policyProfileOfPlan bitGame truthful) who replacement) =
        Profile.update truthful who (Policy.toPlan replacement) := by
    rw [planOfPolicyProfile_update,
      planOfPolicyProfile_policyProfileOfPlan]
  have hstatus :
      planOfPolicyProfile bitGame (policyProfileOfPlan bitGame truthful) =
        truthful :=
    planOfPolicyProfile_policyProfileOfPlan bitGame truthful
  have hupdateLaw := congrArg
    (fun plan => (bitGame.toForm.play plan).map some) hupdate
  have hstatusLaw := congrArg
    (fun plan => (bitGame.toForm.play plan).map some) hstatus
  rw [euPreference_apply] at hdirect ⊢
  rw [toProtocolForm_play, toProtocolForm_play]
  calc
    expectedUtility protocolUtility who
        ((bitGame.toForm.play
          (planOfPolicyProfile bitGame
            (Profile.update (policyProfileOfPlan bitGame truthful)
              who replacement))).map some) =
      expectedUtility protocolUtility who
        ((bitGame.toForm.play
          (Profile.update truthful who (Policy.toPlan replacement))).map some) :=
            congrArg (expectedUtility protocolUtility who) hupdateLaw
    _ ≤ expectedUtility protocolUtility who
        ((bitGame.toForm.play truthful).map some) := by
          rw [expectedUtility_protocol_map, expectedUtility_protocol_map]
          exact hdirect
    _ = expectedUtility protocolUtility who
        ((bitGame.toForm.play
          (planOfPolicyProfile bitGame
            (policyProfileOfPlan bitGame truthful))).map some) :=
          (congrArg (expectedUtility protocolUtility who) hstatusLaw).symm

end GameTheory.Tests.Bayesian
