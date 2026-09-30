/-
# Extending a sequential equilibrium through the identity restriction

The identity restriction of the entry-deterrence arena keeps every choice, so
exiting and rewarding off path extends to a sequential equilibrium with the
same terminal play, beliefs and behavior at every decision.
-/

import GameTheory.Analysis.Protocol.RestrictionExtension
import GameTheory.Analysis.Protocol.SequentialOneShotTest

noncomputable section

namespace GameTheory.Tests.RestrictionExtension

open GameTheory GameTheory.Protocol
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.SubgameLocalization
open GameTheory.Tests.InformationLocalization GameTheory.Tests.SequentialOneShot
open InformationModel

/-- The root is decided at depth zero and the decision at depth one. -/
def siteDepth (_ : Unit) (site : model.InformationSite ()) : ℕ :=
  if site.1 = .root then 0 else 1

theorem site_commonDepth (who : Unit) (site : model.InformationSite who) :
    InformationSite.CommonDepth model site (siteDepth who site) := by
  cases who
  intro history
  rcases site_cases site with hroot | hdecision
  · have same := eq_initHistory_of_root history.1.trace
      ((signals_infoOf_state history.1.trace).symm.trans (history.2.trans hroot))
    simp only [siteDepth, hroot, ↓reduceIte]
    rw [show history.1 = arena.initHistory from same]
    rfl
  · have same := eq_decisionHistory history.1
      ((signals_infoOf_state history.1.trace).symm.trans (history.2.trans hdecision))
    simp only [siteDepth, hdecision, reduceCtorEq, ↓reduceIte]
    rw [same]
    rfl

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
      decisionRecall siteDepth site_commonDepth sePayoff sePayoff (fun _ _ => rfl)
      (fun _ => Or.inl fun _ choice => ⟨choice, rfl⟩) rewardingAssessment
      rewardingAssessment_isSequentialEquilibrium
  exact ⟨target, equilibrium, law⟩

end GameTheory.Tests.RestrictionExtension
