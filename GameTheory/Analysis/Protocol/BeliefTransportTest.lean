/-
# Beliefs at an unreached decision

Exiting at the root and rewarding at the unreached decision is a consistent
assessment, so it obeys Bayes' rule wherever its limit reaches. Along its
trembles the incumbent's own strategy cancels from the decision belief: every
tremble level gives the same belief there, although the decision's mass
changes with the level.
-/

import GameTheory.Analysis.Protocol.BeliefTransport
import GameTheory.Analysis.Protocol.SequentialOneShotTest

noncomputable section

namespace GameTheory.Tests.BeliefTransport

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.InformationLocalization
open GameTheory.Tests.SequentialOneShot
open InformationModel

/-- The consistent assessment obeys Bayes' rule at every reached site. -/
theorem rewardingAssessment_isBayesConsistent :
    BehavioralAssessment.IsBayesConsistent model rewardingAssessment
      decisionRecall.decisionInformationAntichain :=
  rewardingAssessment_consistent.isBayesConsistent _

/-- Different tremble levels give the incumbent the same belief at the
decision: its own strategy cancels. -/
theorem tremble_decision_belief_eq (n m : ℕ) :
    model.bayesBelief (trembleAssessment n).strategy () decisionSite
        (decisionRecall.decisionInformationAntichain () decisionSite)
        (model.informationMass_pos_of_fullSupport _ (trembleAssessment_fullyMixed n) ()
          decisionSite) =
      model.bayesBelief (trembleAssessment m).strategy () decisionSite
        (decisionRecall.decisionInformationAntichain () decisionSite)
        (model.informationMass_pos_of_fullSupport _ (trembleAssessment_fullyMixed m) ()
          decisionSite) :=
  model.bayesBelief_eq_of_eq_off _ _ () decisionSite _
    (fun other hother => absurd (Subsingleton.elim other ()) hother)
    (commonPlayerReachAt_of_decisionRecall model decisionRecall _ () decisionSite)
    (commonPlayerReachAt_of_decisionRecall model decisionRecall _ () decisionSite) _ _

end GameTheory.Tests.BeliefTransport
