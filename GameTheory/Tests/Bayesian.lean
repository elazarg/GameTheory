/-
# Bayesian compiler stress test

One player privately observes a fair bit and must report it. Matching the type
pays one and mismatching pays zero. Truthful reporting is interim-optimal at
both types, hence Nash in the direct form; the exact compiler law then transfers
the same profile to the information-local protocol form. A two-player
common-bit coordination fixture separately exercises both deviation
coordinates of the generic transfer theorem.
-/

import GameTheory.Languages.Bayesian.Strategic

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

/-- Interim optimality supplies ordinary Nash directly; there is no
Bayes-specific equilibrium predicate. -/
theorem truthful_isNash :
    IsNash bitGame.toForm (euPreference bitGame.utility) truthful :=
  (bitGame.isNash_iff_interim truthful).2 truthful_interim_optimal

/-- The information-local policy profile is Nash in the protocol-backed form.
This is now an instance of the generic language-facing transfer theorem. -/
theorem truthful_protocol_isNash :
    IsNash (toProtocolForm bitGame) (euPreference (protocolUtility bitGame))
      (policyProfileOfPlan bitGame truthful) := by
  exact (isNash_toProtocolForm_iff bitGame truthful).2 truthful_isNash

namespace TwoPlayer

/-- A common private bit observed by both players. -/
def commonBitPrior : FinDist (∀ _ : Bool, Bool) :=
  fairBit.map fun bit _ => bit

/-- Both players are rewarded exactly when both reports match their respective
types.  This makes a unilateral deviation by either source player observable. -/
def coordinationGame : BayesianGame Bool where
  Ty _ := Bool
  Act _ := Bool
  prior := commonBitPrior
  payoff types actions _ :=
    if actions false = types false ∧ actions true = types true then 1 else 0

instance instNonemptyAction (i : Bool) : Nonempty (coordinationGame.Act i) :=
  ⟨false⟩

instance instFintypeType (i : Bool) : Fintype (coordinationGame.Ty i) :=
  inferInstanceAs (Fintype Bool)

instance instDecidableEqType (i : Bool) : DecidableEq (coordinationGame.Ty i) :=
  inferInstanceAs (DecidableEq Bool)

/-- Each of the two source players reports its own observed type. -/
def truthful : Profile coordinationGame.signature :=
  fun _ ownType => ownType

/-- Truthful reporting is interim-optimal for both players and both types. -/
theorem truthful_interim_optimal :
    ∀ (who : Bool) (ownType : coordinationGame.Ty who)
      (respond : coordinationGame.Act who),
      coordinationGame.interimValue who ownType truthful respond ≤
        coordinationGame.interimValue who ownType truthful
          (truthful who ownType) := by
  intro who ownType respond
  unfold BayesianGame.interimValue
  apply FinDist.expect_mono
  intro types _
  by_cases htype : types who = ownType
  · simp only [htype, if_true]
    cases who <;>
      simp [coordinationGame, truthful, BayesianGame.actionsOf, htype]
    <;> split <;> norm_num
  · simp [htype]

/-- Truthful reporting is Nash in the direct two-player Bayesian form. -/
theorem truthful_isNash :
    IsNash coordinationGame.toForm
      (euPreference coordinationGame.utility) truthful :=
  (coordinationGame.isNash_iff_interim truthful).2
    truthful_interim_optimal

/-- A two-player endpoint for the generic direct/protocol Nash equivalence.
Unlike the one-player smoke test, both update coordinates are exercised by the
quantified equilibrium theorem. -/
theorem truthful_protocol_isNash :
    IsNash (toProtocolForm coordinationGame)
      (euPreference (protocolUtility coordinationGame))
      (policyProfileOfPlan coordinationGame truthful) := by
  exact (isNash_toProtocolForm_iff coordinationGame truthful).2
    truthful_isNash

end TwoPlayer

end GameTheory.Tests.Bayesian
