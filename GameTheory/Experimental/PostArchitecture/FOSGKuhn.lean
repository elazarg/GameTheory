/-
# EXP-057 witness: FOSG observation ownership and Kuhn laws

The execution below is literally the same two-vote Protocol in both games.
Only its information model changes: the forgetful signals fail perfect recall,
while the recalling signals satisfy both standard named Kuhn hypotheses.  The
named FOSG theorems then preserve the canonical complete-history law and every
outcome projection without constructing a native FOSG runner.
-/

import GameTheory.Languages.FOSG.Kuhn
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Experimental.FOSGKuhn

open GameTheory.Languages GameTheory.Protocol GameTheory.Tests

private def forgetfulGame : FOSG.Game Unit where
  execution := Randomized.twice
  information := Randomized.model

private def recallingGame : FOSG.Game Unit where
  execution := Randomized.twice
  information := Randomized.recallModel

private def singleGame : FOSG.Game Unit where
  execution := Randomized.once
  information := Randomized.singleModel

private noncomputable instance recallingInfoStateFintype (who : Unit) :
    Fintype (recallingGame.information.InfoState who) := by
  cases who
  simpa [recallingGame, Randomized.recallModel, Randomized.recallSignals] using
    (inferInstance : Fintype Randomized.Memory)

private instance recallingInfoStateDecidableEq (who : Unit) :
    DecidableEq (recallingGame.information.InfoState who) := by
  cases who
  simpa [recallingGame, Randomized.recallModel, Randomized.recallSignals] using
    (inferInstance : DecidableEq Randomized.Memory)

private noncomputable instance singleInfoStateFintype (who : Unit) :
    Fintype (singleGame.information.InfoState who) := by
  cases who
  simpa [singleGame, Randomized.singleModel, Randomized.singleSignals] using
    (inferInstance : Fintype Bool)

private instance singleInfoStateDecidableEq (who : Unit) :
    DecidableEq (singleGame.information.InfoState who) := by
  cases who
  simpa [singleGame, Randomized.singleModel, Randomized.singleSignals] using
    (inferInstance : DecidableEq Bool)

/-- Observation design changes while execution remains definitionally equal. -/
example : forgetfulGame.execution = recallingGame.execution := rfl

/-- The forgetful observation design cannot use the recall-facing direction. -/
example : ¬forgetfulGame.information.PerfectRecall :=
  Randomized.not_perfectRecall

/-- Repeating one nontrivial information state also violates the acts-once
hypothesis, and the two randomization modes then induce different laws. -/
example : ¬forgetfulGame.information.ActsOnceWhereItMatters :=
  Randomized.not_actsOnceWhereItMatters

example :
    Probability.FinDist.map (fun history => history.state)
        (forgetfulGame.information.runBehavioral
          (fun _ => Randomized.coinPolicy) 2) ≠
      Probability.FinDist.map (fun history => history.state)
        (forgetfulGame.information.runMixed
          (fun _ => Randomized.coinPolicy.toMixed) 2) := by
  simpa [forgetfulGame] using Randomized.runBehavioral_ne_runMixed

/-- One move satisfies acts-once while still forgetting its own action, so
acts-once does not imply perfect recall. -/
private theorem singleActsOnce : singleGame.information.ActsOnceWhereItMatters :=
  singleGame.information.actsOnceWhereItMatters_of_actsOnce
    Randomized.single_actsOnceAtEachInfoState

example : ¬singleGame.information.PerfectRecall :=
  Randomized.single_not_perfectRecall

example (behavioral : Profile singleGame.behavioralSignature) (horizon : ℕ) :
    ∃ mixed : Profile singleGame.information.strategicSignature.mixed,
      singleGame.information.runMixed mixed horizon =
        singleGame.information.runBehavioral behavioral horizon :=
  singleGame.kuhn_behavioral_to_mixed singleActsOnce behavioral horizon

private theorem recallingActsOnce :
    recallingGame.information.ActsOnceWhereItMatters :=
  recallingGame.information.actsOnceWhereItMatters_of_actsOnce
    Randomized.recall_actsOnceAtEachInfoState

private theorem recallingPerfectRecall :
    recallingGame.information.PerfectRecall :=
  Randomized.recall_perfectRecall

/-- The FOSG-facing behavioral-to-mixed theorem is the canonical Protocol law. -/
theorem recalling_behavioral_to_mixed
    (behavioral : Profile recallingGame.behavioralSignature) (horizon : ℕ) :
    ∃ mixed : Profile recallingGame.information.strategicSignature.mixed,
      recallingGame.information.runMixed mixed horizon =
        recallingGame.information.runBehavioral behavioral horizon :=
  recallingGame.kuhn_behavioral_to_mixed recallingActsOnce behavioral horizon

/-- The recall-facing direction uses the same histories and runner. -/
theorem recalling_mixed_to_behavioral
    (mixed : Profile recallingGame.information.strategicSignature.mixed)
    (horizon : ℕ) :
    ∃ behavioral : Profile recallingGame.behavioralSignature,
      recallingGame.information.runBehavioral behavioral horizon =
        recallingGame.information.runMixed mixed horizon :=
  recallingGame.kuhn_mixed_to_behavioral recallingPerfectRecall mixed horizon

/-- Both presentations realize exactly the same complete-history laws. -/
theorem recalling_historyLaws (horizon : ℕ) :
    { law | ∃ behavioral : Profile recallingGame.behavioralSignature,
        recallingGame.information.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : Profile recallingGame.information.strategicSignature.mixed,
        recallingGame.information.runMixed mixed horizon = law } :=
  recallingGame.kuhn_historyLaws recallingPerfectRecall horizon

/-- Arbitrary retained outcome data commutes with the predrawn mixed witness. -/
theorem recalling_outcomeLaw
    (behavioral : Profile recallingGame.behavioralSignature) (horizon : ℕ)
    {Outcome : Type} (outcome : recallingGame.History → Outcome) :
    ∃ mixed : Profile recallingGame.information.strategicSignature.mixed,
      Probability.FinDist.map outcome
          (recallingGame.information.runMixed mixed horizon) =
        Probability.FinDist.map outcome
          (recallingGame.information.runBehavioral behavioral horizon) :=
  recallingGame.kuhn_behavioral_to_mixed_outcomeLaw
    recallingActsOnce behavioral horizon outcome


end GameTheory.Experimental.FOSGKuhn
