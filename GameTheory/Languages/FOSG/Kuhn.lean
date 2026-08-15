/-
# Kuhn correspondence for factored-observation stochastic games

FOSG owns no native Kuhn machine.  A FOSG already carries the canonical
`InformationModel`, whose behavioral and mixed runners return laws over the
same Protocol histories.  This leaf gives that existing theorem a named
FOSG-facing surface without defining another history, strategy, product law,
or evaluator.

As in the EFG-facing surface, the correspondence is currently stated for whole
profiles. It does not yet provide the per-player realization theorem needed to
transfer Nash equilibria between behavioral and mixed strategy spaces.
-/

import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Languages.FOSG

open GameTheory.Protocol GameTheory.Math.Probability

universe uι us ua up uq uk uo

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- A behavioral FOSG plan randomizes at each information-local menu. -/
abbrev BehavioralPlan (who : ι) := G.information.BehavioralPolicy who

/-- A mixed FOSG plan draws one information-local contingent policy once. -/
abbrev MixedPlan (who : ι) := G.information.MixedPolicy who

/-- The behavioral signature is exactly the canonical information-model
signature. -/
abbrev behavioralSignature : GameSignature ι :=
  G.information.behavioralSignature

variable [Fintype ι]

/-- Present behavioral FOSG plans through the canonical behavioral runner. -/
@[reducible]
def toBehavioralGameForm (horizon : ℕ) : GameForm ι :=
  G.information.toBehavioralGameForm horizon

/-- The behavioral FOSG compiler has no language-specific evaluator. -/
@[simp]
theorem toBehavioralGameForm_play (horizon : ℕ)
    (behavioral : Profile G.behavioralSignature) :
    (G.toBehavioralGameForm horizon).play behavioral =
      G.information.runBehavioral behavioral horizon :=
  InformationModel.toBehavioralGameForm_play G.information horizon behavioral

/-- Predrawing every local choice preserves the complete FOSG history law. -/
theorem kuhn_behavioral_to_mixed
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ) :
    ∃ mixed : Profile G.information.strategicSignature.mixed,
      G.information.runMixed mixed horizon =
        G.information.runBehavioral behavioral horizon :=
  ⟨fun who => (behavioral who).toMixed,
    G.information.runMixed_toMixed hactsOnce behavioral horizon⟩

/-- Under perfect recall, the behavioral reading of a mixed FOSG plan
preserves the complete history law. -/
theorem kuhn_mixed_to_behavioral
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.information.strategicSignature.mixed) (horizon : ℕ) :
    ∃ behavioral : Profile G.behavioralSignature,
      G.information.runBehavioral behavioral horizon =
        G.information.runMixed mixed horizon :=
  ⟨fun who =>
      InformationModel.MixedPolicy.toBehavioral
        (M := G.information) (mixed who),
    (G.information.runMixed_toBehavioral
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      horizon mixed).symm⟩

/-- Under perfect recall, behavioral and mixed FOSG profiles realize the same
complete-history laws. Perfect recall supplies the no-revisit consequence used
in the behavioral-to-mixed direction. -/
theorem kuhn_historyLaws
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hrecall : G.information.PerfectRecall) (horizon : ℕ) :
    { law | ∃ behavioral : Profile G.behavioralSignature,
        G.information.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : Profile G.information.strategicSignature.mixed,
        G.information.runMixed mixed horizon = law } :=
  G.information.runBehavioral_image_eq_runMixed_image
    (G.information.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon

/-- Every outcome projection of the behavioral history law is preserved by
the predrawn mixed witness. -/
theorem kuhn_behavioral_to_mixed_outcomeLaw
    [∀ who, Fintype (G.information.InfoState who)]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (behavioral : Profile G.behavioralSignature) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ mixed : Profile G.information.strategicSignature.mixed,
      FinDist.map outcome (G.information.runMixed mixed horizon) =
        FinDist.map outcome (G.information.runBehavioral behavioral horizon) := by
  obtain ⟨mixed, hmixed⟩ :=
    G.kuhn_behavioral_to_mixed hactsOnce behavioral horizon
  exact ⟨mixed, congrArg (FinDist.map outcome) hmixed⟩

/-- Every outcome projection of a mixed FOSG history law is preserved by its
behavioral reading under perfect recall. -/
theorem kuhn_mixed_to_behavioral_outcomeLaw
    (hrecall : G.information.PerfectRecall)
    (mixed : Profile G.information.strategicSignature.mixed) (horizon : ℕ)
    {Outcome : Type uo} (outcome : G.History → Outcome) :
    ∃ behavioral : Profile G.behavioralSignature,
      FinDist.map outcome (G.information.runBehavioral behavioral horizon) =
        FinDist.map outcome (G.information.runMixed mixed horizon) := by
  obtain ⟨behavioral, hbehavioral⟩ :=
    G.kuhn_mixed_to_behavioral hrecall mixed horizon
  exact ⟨behavioral, congrArg (FinDist.map outcome) hbehavioral⟩

end Game

end GameTheory.Languages.FOSG
