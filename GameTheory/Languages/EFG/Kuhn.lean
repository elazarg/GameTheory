/-
# Kuhn correspondence for extensive-form games

The substantive behavioral/mixed equivalence lives on the accepted
`InformationModel`. This module gives an EFG-facing surface without introducing
another evaluator, strategy representation, or equilibrium notion.

The two directions deliberately retain their sharp hypotheses. Predrawing a
behavioral plan needs no repeated nontrivial information state; reading a mixed
plan behaviorally needs recall, used through the weaker constraint-locality
fact it implies.
-/

import GameTheory.Languages.EFG.Strategic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol Probability

universe uι us ua up uq uk uo

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- A behavioral EFG plan randomizes locally at each information state. -/
abbrev BehavioralPlan (who : ι) :=
  G.information.BehavioralPolicy who

/-- A mixed EFG plan draws one information-local contingent plan once. -/
abbrev MixedPlan (who : ι) :=
  G.information.MixedPolicy who

/-- The EFG behavioral signature is the accepted information-model signature. -/
abbrev behavioralSignature : GameSignature ι :=
  G.information.behavioralSignature

variable [Fintype ι]

/-- Present behavioral EFG plans through the canonical behavioral runner. -/
@[reducible]
def toBehavioralGameForm (horizon : ℕ) : GameForm ι :=
  G.information.toBehavioralGameForm horizon

/-- The behavioral EFG compiler has no language-specific evaluator. -/
@[simp]
theorem toBehavioralGameForm_play (horizon : ℕ)
    (behavioral : Profile G.behavioralSignature) :
    (G.toBehavioralGameForm horizon).play behavioral =
      G.information.runBehavioral behavioral horizon :=
  InformationModel.toBehavioralGameForm_play G.information horizon behavioral

/-- **Behavioral-to-mixed Kuhn direction.** Predrawing every local choice gives
an explicit mixed contingent-plan profile with exactly the same history law. -/
theorem kuhn_behavioral_to_mixed
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      G.information.runMixed mixed horizon =
        G.information.runBehavioral behavioral horizon :=
  ⟨fun who => (behavioral who).toMixed,
    G.information.runMixed_toMixed hactsOnce behavioral horizon⟩

/-- **Mixed-to-behavioral Kuhn direction.** Under perfect recall, the canonical
behavioral reading of a mixed contingent plan has exactly the same history
law. -/
theorem kuhn_mixed_to_behavioral
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ) :
    ∃ behavioral : Profile G.behavioralSignature,
      G.information.runBehavioral behavioral horizon =
        G.information.runMixed mixed horizon :=
  ⟨fun who =>
      InformationModel.MixedPolicy.toBehavioral
        (M := G.information) (mixed who),
    (G.information.runMixed_toBehavioral
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      horizon mixed).symm⟩

/-- Behavioral and mixed EFG profiles realize exactly the same history laws
when both sharp conditions hold. -/
theorem kuhn_historyLaws
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (hrecall : G.information.PerfectRecall) (horizon : ℕ) :
    { law | ∃ behavioral : Profile G.behavioralSignature,
        G.information.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : Profile G.strategicSignature.mixed,
        G.information.runMixed mixed horizon = law } :=
  G.information.runBehavioral_image_eq_runMixed_image hactsOnce
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon

/-- Pushing a behavioral history law through any outcome map preserves the
behavioral-to-mixed correspondence. This is the utility-distribution theorem
from v1 with utility generalized to arbitrary retained outcome data. -/
theorem kuhn_behavioral_to_mixed_outcomeLaw
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      FinDist.map outcome (G.information.runMixed mixed horizon) =
        FinDist.map outcome (G.information.runBehavioral behavioral horizon) := by
  obtain ⟨mixed, hmixed⟩ :=
    G.kuhn_behavioral_to_mixed hactsOnce behavioral horizon
  exact ⟨mixed, congrArg (FinDist.map outcome) hmixed⟩

/-- Pushing a mixed history law through any outcome map preserves the
mixed-to-behavioral correspondence. -/
theorem kuhn_mixed_to_behavioral_outcomeLaw
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ behavioral : Profile G.behavioralSignature,
      FinDist.map outcome (G.information.runBehavioral behavioral horizon) =
        FinDist.map outcome (G.information.runMixed mixed horizon) := by
  obtain ⟨behavioral, hbehavioral⟩ :=
    G.kuhn_mixed_to_behavioral hrecall mixed horizon
  exact ⟨behavioral, congrArg (FinDist.map outcome) hbehavioral⟩

/-- The behavioral-to-mixed witness preserves every player's expected utility. -/
theorem kuhn_behavioral_to_mixed_expectedUtility
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    (utility : G.History → ι → ℝ) :
    ∃ mixed : Profile G.strategicSignature.mixed,
      ∀ who,
        expectedUtility utility who
            (G.information.runMixed mixed horizon) =
          expectedUtility utility who
            (G.information.runBehavioral behavioral horizon) := by
  obtain ⟨mixed, hmixed⟩ :=
    G.kuhn_behavioral_to_mixed hactsOnce behavioral horizon
  exact ⟨mixed, fun who => congrArg (expectedUtility utility who) hmixed⟩

/-- The mixed-to-behavioral witness preserves every player's expected utility. -/
theorem kuhn_mixed_to_behavioral_expectedUtility
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ)
    (utility : G.History → ι → ℝ) :
    ∃ behavioral : Profile G.behavioralSignature,
      ∀ who,
        expectedUtility utility who
            (G.information.runBehavioral behavioral horizon) =
          expectedUtility utility who
            (G.information.runMixed mixed horizon) := by
  obtain ⟨behavioral, hbehavioral⟩ :=
    G.kuhn_mixed_to_behavioral hrecall mixed horizon
  exact
    ⟨behavioral,
      fun who => congrArg (expectedUtility utility who) hbehavioral⟩

end Game

end GameTheory.Languages.EFG
