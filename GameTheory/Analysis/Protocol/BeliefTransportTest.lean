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
open scoped ENNReal

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


/-- Reach-mass ratios cancel even when the two profiles enter with different
probabilities. This exercises a genuinely proportional reach certificate. -/
theorem tremble_decision_belief_eq_via_proportional (n m : ℕ) :
    model.bayesBelief (trembleAssessment n).strategy () decisionSite
        (decisionRecall.decisionInformationAntichain () decisionSite)
        (model.informationMass_pos_of_fullSupport _ (trembleAssessment_fullyMixed n) ()
          decisionSite) =
      model.bayesBelief (trembleAssessment m).strategy () decisionSite
        (decisionRecall.decisionInformationAntichain () decisionSite)
        (model.informationMass_pos_of_fullSupport _ (trembleAssessment_fullyMixed m) ()
          decisionSite) := by
  classical
  let raw := (trembleAssessment n).strategy
  let source := (trembleAssessment m).strategy
  let mass := model.informationMass source () decisionSite
  have positive : 0 < mass := model.informationMass_pos_of_fullSupport _
    (trembleAssessment_fullyMixed m) () decisionSite
  have finite : mass ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (model.informationMass_le_one source () decisionSite
      (decisionRecall.decisionInformationAntichain () decisionSite))
  have rawPositive := model.informationMass_pos_of_fullSupport _
    (trembleAssessment_fullyMixed n) () decisionSite
  have rawFinite := ne_top_of_le_ne_top ENNReal.one_ne_top
    (model.informationMass_le_one raw () decisionSite
      (decisionRecall.decisionInformationAntichain () decisionSite))
  have unique (first second : model.InformationHistory () decisionSite.1) : first = second :=
    Subtype.ext (site_history_unique decisionSite first second)
  have weight (profile : (who : Unit) → model.BehavioralPolicy who)
      (history : model.InformationHistory () decisionSite.1) :
      model.informationMass profile () decisionSite = model.historyReachWeight profile history.1 :=
    tsum_eq_single history fun other different => absurd (unique other history) different
  have fiber (history : model.InformationHistory () decisionSite.1) :
      (model.informationMass raw () decisionSite / mass) *
          model.historyReachWeight source history.1 =
        ∑' original : model.InformationHistory () decisionSite.1,
          if id original.1 = history.1 then model.historyReachWeight raw original.1 else 0 := by
    rw [← weight source history, ENNReal.div_mul_cancel positive.ne' finite]
    simp only [show ∀ original : model.InformationHistory () decisionSite.1,
      id original.1 = history.1 from fun original => congrArg Subtype.val (unique original history),
      ite_true]
    rfl
  have projected := model.bayesBelief_projection_of_proportional_reach model raw source id ()
    decisionSite decisionSite (fun _ same => same)
    (model.informationMass raw () decisionSite / mass) fiber
    (ENNReal.div_ne_zero.mpr ⟨rawPositive.ne', finite⟩)
    (ENNReal.div_ne_top rawFinite positive.ne')
    (decisionRecall.decisionInformationAntichain () decisionSite)
    (decisionRecall.decisionInformationAntichain () decisionSite) positive
  change (model.bayesBelief raw () decisionSite _ _).map id = _ at projected
  rw [PMF.map_id] at projected
  exact projected

end GameTheory.Tests.BeliefTransport
