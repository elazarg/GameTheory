/-
# Bayesian compiler stress test

A private fair bit is reported truthfully. A two-player common-bit game
exercises both source-player deviation coordinates of the protocol transfer.
-/

import GameTheory.Languages.Bayesian.Strategic
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Tests.Bayesian

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bayesian

def fairBit : PMF Bool := PMF.uniformOfFintype Bool

def bitPrior : PMF (∀ _ : Unit, Bool) :=
  fairBit.map fun bit _ => bit

@[reducible]
def bitGame : BayesianGame Unit where
  Ty _ := Bool
  Act _ := Bool
  prior := bitPrior
  payoff types actions _ := if actions () = types () then 1 else 0

instance instNonemptyBitAction (i : Unit) : Nonempty (bitGame.Act i) := ⟨false⟩

instance instDecidableEqBitType (i : Unit) : DecidableEq (bitGame.Ty i) :=
  inferInstanceAs (DecidableEq Bool)

def truthful : Profile bitGame.signature :=
  fun _ ownType => ownType

theorem truthful_policy_at (ownType : Bool) :
    (policyProfileOfPlan bitGame truthful ()).act (View.acting ownType) =
      some ownType := rfl

theorem truthful_protocol_law :
    (toProtocolForm bitGame).play (policyProfileOfPlan bitGame truthful) =
      (bitGame.toForm.play truthful).map some :=
  toProtocolForm_play_policyProfileOfPlan bitGame truthful

private theorem bit_utility_bounded (who : Unit)
    (outcome : bitGame.signature.Outcome) :
    |bitGame.utility outcome who| ≤ (1 : ℝ) := by
  cases who
  simp [BayesianGame.utility, bitGame]
  split <;> norm_num

/-- Bounded bit-game payoffs integrate under each actual deviation law. -/
theorem bit_deviation_integrable (who : Unit)
    (deviation : bitGame.Ty who → bitGame.Act who) :
    UtilityIntegrable bitGame.utility who
      (bitGame.toForm.play (Profile.update truthful who deviation)) :=
  payoffIntegrable_of_bounded _ _ (bit_utility_bounded who)

theorem truthful_isNash :
    IsNash bitGame.toForm (euPreference bitGame.utility) truthful := by
  rw [isNash_iff]
  intro who replacement
  let dev := Profile.update truthful who replacement
  have htruth : UtilityIntegrable bitGame.utility who
      (bitGame.toForm.play truthful) :=
    payoffIntegrable_of_bounded _ _ (bit_utility_bounded who)
  have hdev : UtilityIntegrable bitGame.utility who
      (bitGame.toForm.play dev) :=
    payoffIntegrable_of_bounded _ _ (bit_utility_bounded who)
  apply (euPreference_iff bitGame.utility who
    (bitGame.toForm.play truthful) (bitGame.toForm.play dev)
    htruth hdev).2
  rw [bitGame.expectedUtility_eq_prior who truthful htruth,
    bitGame.expectedUtility_eq_prior who dev hdev]
  apply expect_mono
  intro types _
  cases who
  simp [BayesianGame.planPayoff, dev, bitGame, truthful,
    BayesianGame.actionsOf]
  split <;> norm_num

/-- The general infinite-type interim theorem specializes to this fair bit. -/
theorem truthful_interim_optimal :
    ∀ (who : Unit) (ownType : bitGame.Ty who) (respond : bitGame.Act who),
      bitGame.interimValueOfDeviation who ownType truthful respond
        (bitGame.singleTypeDeviation truthful who ownType respond) (by
          simp [BayesianGame.singleTypeDeviation])
        (bit_deviation_integrable who
          (bitGame.singleTypeDeviation truthful who ownType respond)) ≤
      bitGame.interimValueOfDeviation who ownType truthful
        (truthful who ownType) (fun t => truthful who t) rfl
        (by simpa only [Profile.update_eq_self] using
          bit_deviation_integrable who (truthful who)) :=
  (bitGame.isNash_iff_interim truthful bit_deviation_integrable).1
    truthful_isNash

theorem truthful_protocol_isNash :
    IsNash (toProtocolForm bitGame) (euPreference (protocolUtility bitGame))
      (policyProfileOfPlan bitGame truthful) :=
  (isNash_toProtocolForm_iff bitGame truthful).2 truthful_isNash

namespace TwoPlayer

def commonBitPrior : PMF (∀ _ : Bool, Bool) :=
  fairBit.map fun bit _ => bit

@[reducible]
def coordinationGame : BayesianGame Bool where
  Ty _ := Bool
  Act _ := Bool
  prior := commonBitPrior
  payoff types actions _ :=
    if actions false = types false ∧ actions true = types true then 1 else 0

instance instNonemptyAction (i : Bool) : Nonempty (coordinationGame.Act i) :=
  ⟨false⟩

instance instDecidableEqType (i : Bool) :
    DecidableEq (coordinationGame.Ty i) :=
  inferInstanceAs (DecidableEq Bool)

def truthful : Profile coordinationGame.signature :=
  fun _ ownType => ownType

private theorem utility_bounded (who : Bool)
    (outcome : coordinationGame.signature.Outcome) :
    |coordinationGame.utility outcome who| ≤ (1 : ℝ) := by
  simp [BayesianGame.utility, coordinationGame]
  split <;> norm_num

/-- Bounded coordination payoffs integrate under each actual deviation law. -/
theorem deviation_integrable (who : Bool)
    (deviation : coordinationGame.Ty who → coordinationGame.Act who) :
    UtilityIntegrable coordinationGame.utility who
      (coordinationGame.toForm.play
        (Profile.update truthful who deviation)) :=
  payoffIntegrable_of_bounded _ _ (utility_bounded who)

theorem truthful_isNash :
    IsNash coordinationGame.toForm
      (euPreference coordinationGame.utility) truthful := by
  rw [isNash_iff]
  intro who replacement
  let dev := Profile.update truthful who replacement
  have htruth : UtilityIntegrable coordinationGame.utility who
      (coordinationGame.toForm.play truthful) :=
    payoffIntegrable_of_bounded _ _ (utility_bounded who)
  have hdev : UtilityIntegrable coordinationGame.utility who
      (coordinationGame.toForm.play dev) :=
    payoffIntegrable_of_bounded _ _ (utility_bounded who)
  apply (euPreference_iff coordinationGame.utility who
    (coordinationGame.toForm.play truthful) (coordinationGame.toForm.play dev)
    htruth hdev).2
  rw [coordinationGame.expectedUtility_eq_prior who truthful htruth,
    coordinationGame.expectedUtility_eq_prior who dev hdev]
  apply expect_mono
  intro types _
  cases who <;>
    simp [BayesianGame.planPayoff, dev, coordinationGame, truthful,
      BayesianGame.actionsOf]
  all_goals split <;> norm_num

theorem truthful_interim_optimal :
    ∀ (who : Bool) (ownType : coordinationGame.Ty who)
      (respond : coordinationGame.Act who),
      coordinationGame.interimValueOfDeviation who ownType truthful respond
        (coordinationGame.singleTypeDeviation truthful who ownType respond) (by
          simp [BayesianGame.singleTypeDeviation])
        (deviation_integrable who
          (coordinationGame.singleTypeDeviation truthful who ownType respond)) ≤
      coordinationGame.interimValueOfDeviation who ownType truthful
        (truthful who ownType) (fun t => truthful who t) rfl
        (by simpa only [Profile.update_eq_self] using
          deviation_integrable who (truthful who)) :=
  (coordinationGame.isNash_iff_interim truthful deviation_integrable).1
    truthful_isNash

theorem truthful_protocol_isNash :
    IsNash (toProtocolForm coordinationGame)
      (euPreference (protocolUtility coordinationGame))
      (policyProfileOfPlan coordinationGame truthful) :=
  (isNash_toProtocolForm_iff coordinationGame truthful).2 truthful_isNash

end TwoPlayer

end GameTheory.Tests.Bayesian
