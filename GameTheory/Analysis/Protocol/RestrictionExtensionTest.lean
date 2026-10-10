/-
# Extending a sequential equilibrium through the identity restriction

The identity restriction of the entry-deterrence arena keeps every choice, so
exiting and rewarding off path extends to a sequential equilibrium with the
same terminal play, beliefs and behavior at every decision.
-/

import GameTheory.Analysis.Protocol.RestrictionExtension
import GameTheory.Analysis.Protocol.SequentialOneShotTest
import GameTheory.Analysis.Protocol.SequentialExistenceTest

noncomputable section

namespace GameTheory.Tests.RestrictionExtension

open GameTheory GameTheory.Protocol
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.SubgameLocalization
open GameTheory.Tests.InformationLocalization GameTheory.Tests.SequentialOneShot
open InformationModel

/-- **Rewarding off path extends.** -/
theorem rewarding_extends :
    ∃ target : model.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        arena_wellFoundedHistories sePayoff ∧
      (model.runBehavioralTerminalFrom arena_wellFoundedHistories rewardingAssessment.strategy
          arena.initHistory).map (ActionRestriction.refl model).history =
        model.runBehavioralTerminalFrom arena_wellFoundedHistories target.strategy
          arena.initHistory := by
  obtain ⟨target, equilibrium, -, -, law, -⟩ :=
    (ActionRestriction.refl model).sequentialEquilibrium_extends_of_indifference
      decisionRecall.decisionInformationAntichain arena_wellFoundedHistories
      arena_wellFoundedHistories (trembleAssessment 0) (trembleAssessment_fullyMixed 0)
      decisionRecall sePayoff sePayoff (fun _ _ => rfl)
      (fun _ => Or.inl fun _ choice => ⟨choice, rfl⟩) rewardingAssessment
      rewardingAssessment_isSequentialEquilibrium
  exact ⟨target, equilibrium, law⟩


namespace Asynchronous

open GameTheory.Tests.SequentialExistence

/-- Restriction extension applies to a hidden decision whose two histories
have different depths; the common-depth premise is concretely impossible. -/
theorem identity_extends_without_common_depth :
    (¬ ∃ depth, InformationSite.CommonDepth information actingSite depth) ∧
      ∃ source target : information.BehavioralAssessment,
        source.IsSequentialEquilibrium antichain game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff ∧
        target.IsSequentialEquilibrium antichain game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff ∧
        information.runBehavioralTerminalFrom game.wellFoundedHistories source.strategy
            execution.initHistory =
          information.runBehavioralTerminalFrom game.wellFoundedHistories target.strategy
            execution.initHistory := by
  classical
  let _ : Fintype execution.History := execution.historyFintype treeShaped
  obtain ⟨source, equilibrium⟩ := exists_sequential_equilibrium
  change source.IsSequentialEquilibrium antichain game.wellFoundedHistories GameTheory.Tests.SequentialExistence.payoff at equilibrium
  obtain ⟨sequence, approximates, _⟩ := equilibrium.2
  let decisionRecallCertificate := information.decisionRecall_of_perfectRecall perfectRecall
  obtain ⟨target, targetEquilibrium, _, _, law, _⟩ :=
    (ActionRestriction.refl information).sequentialEquilibrium_extends_of_indifference
      antichain game.wellFoundedHistories game.wellFoundedHistories
      (sequence 0) (approximates 0).1 decisionRecallCertificate GameTheory.Tests.SequentialExistence.payoff GameTheory.Tests.SequentialExistence.payoff (fun _ _ => rfl)
      (fun _ => Or.inl fun _ choice => ⟨choice, rfl⟩) source equilibrium
  refine ⟨no_commonDepth, source, target, equilibrium, targetEquilibrium, ?_⟩
  change (information.runBehavioralTerminalFrom game.wellFoundedHistories source.strategy
    execution.initHistory).map id = _ at law
  rw [PMF.map_id] at law
  exact law

end Asynchronous

end GameTheory.Tests.RestrictionExtension
