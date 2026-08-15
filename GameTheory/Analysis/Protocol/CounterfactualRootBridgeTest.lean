/-
# Root consumers for bounded counterfactual decomposition

This small leaf keeps the composed generic theorem responsive without making
the larger hostile fixture re-elaborate on every root-bridge change.
-/

import GameTheory.Analysis.Protocol.CounterfactualDecompositionTest

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest

open GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest
open GameTheory.Analysis.Protocol.CounterfactualDecompositionTest
open GameTheory.Tests.SubgameOneShot

local instance : Fintype
    (information.InformationHistory () firstSite.1) :=
  Fintype.ofEquiv Bool firstHistoryEquivBool.symm

local instance : Fintype
    (information.InformationHistory () (secondSite true).1) :=
  Fintype.ofEquiv Bool (secondHistoryEquivBool true).symm

theorem incumbentOwnReach_first (hidden : Bool) :
    information.playerReachProbability incumbentBehavioralStrategy ()
      (firstHistory hidden).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_firstHistory]
  rfl

theorem incumbentCommonOwnReach_first
    (history : information.InformationHistory () firstSite.1) :
    information.playerReachProbability incumbentBehavioralStrategy ()
      history.1.trace = 1 := by
  rw [← firstHistoryEquivBool.symm_apply_apply history]
  exact incumbentOwnReach_first _

/-- The action-facing perfect-recall corollary discharges common own reach
without a fixture-specific certificate. -/
theorem firstCommit_perfectRecallRootBridge :
    (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice true))) 3).expect terminalPayoff -
      (information.runBehavioral incumbentBehavioralStrategy 3).expect
        terminalPayoff =
    information.playerReachProbability incumbentBehavioralStrategy ()
        firstSite.2.choose.1.trace *
      information.counterfactualActionRegret incumbentBehavioralStrategy ()
        firstSite terminalPayoff 2 (firstChoice true) := by
  exact
    rootGain_eq_representativeReach_mul_counterfactualActionRegret_of_perfectRecall
      information information_perfectRecall incumbentBehavioralStrategy ()
      firstSite (firstChoice true) 1 2 firstSite_commonDepth terminalPayoff

/-- The generic single-site theorem proves at the root, not merely inside the
information fiber, that changing only the first action gains exactly zero. -/
theorem firstCommit_rootGain_eq_zero :
    (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice true))) 3).expect terminalPayoff -
      (information.runBehavioral incumbentBehavioralStrategy 3).expect
        terminalPayoff = 0 := by
  have hroot :=
    information.rootGain_eq_ownReach_mul_counterfactualRegret
      incumbentBehavioralStrategy () firstSite
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true))
        1 2 firstSite_commonDepth (fun hne =>
          InformationModel.BehavioralPolicy.commit_of_ne
            incumbentBehavioralPolicy firstSite.1 (firstChoice true) hne)
        1 incumbentCommonOwnReach_first terminalPayoff
  rw [show information.counterfactualRegret incumbentBehavioralStrategy ()
      firstSite terminalPayoff 2
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) =
      information.counterfactualActionRegret incumbentBehavioralStrategy ()
        firstSite terminalPayoff 2 (firstChoice true) by rfl,
    first_counterfactualActionRegret, mul_zero] at hroot
  norm_num at hroot ⊢
  exact hroot

theorem firstCommittedOwnReach_secondTrue (hidden : Bool) :
    information.playerReachProbability firstCommittedStrategy ()
      (secondHistory hidden true).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
  rw [show decodeRecord [(Stage.first, true)] =
      [(firstKnowledge, true)] by rfl,
    InformationModel.ownPlayReachProbability]
  have hpolicy : firstCommittedPolicy firstKnowledge =
      FinDist.pure (firstChoice true) := by
    unfold firstCommittedPolicy
    rw [InformationModel.BehavioralPolicy.commit_self (M := information)]
  rw [show firstCommittedStrategy () firstKnowledge =
      FinDist.pure (firstChoice true) from hpolicy]
  simp [firstChoice, InformationModel.ownPlayReachProbability]

theorem firstCommittedCommonOwnReach_secondTrue
    (history : information.InformationHistory () (secondSite true).1) :
    information.playerReachProbability firstCommittedStrategy ()
      history.1.trace = 1 := by
  rw [← (secondHistoryEquivBool true).symm_apply_apply history]
  exact firstCommittedOwnReach_secondTrue _

/-- The same generic root theorem reaches the off-path second update with its
unit alternative-own-reach coefficient. -/
theorem secondCommit_rootGain_eq_counterfactualActionRegret :
    (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 3).expect terminalPayoff -
      (information.runBehavioral firstCommittedStrategy 3).expect
        terminalPayoff =
    information.counterfactualActionRegret firstCommittedStrategy ()
      (secondSite true) terminalPayoff 1 (secondChoice true true) := by
  have hroot :=
    information.rootGain_eq_ownReach_mul_counterfactualRegret
      firstCommittedStrategy () (secondSite true)
        (firstCommittedPolicy.commit (secondSite true).1
          (secondChoice true true)) 2 1 (secondSite_commonDepth true)
        (fun hne =>
          InformationModel.BehavioralPolicy.commit_of_ne firstCommittedPolicy
            (secondSite true).1 (secondChoice true true) hne)
        1 firstCommittedCommonOwnReach_secondTrue terminalPayoff
  norm_num at hroot ⊢
  exact hroot

def incumbentSecondTruePolicy : information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.commit (secondSite true).1
    (secondChoice true true)

def firstCommittedSecondTruePolicy : information.BehavioralPolicy () :=
  firstCommittedPolicy.commit (secondSite true).1 (secondChoice true true)

theorem firstCommitted_eq_incumbent_off_first
    {info : Knowledge} (hinfo : info ≠ firstSite.1) :
    firstCommittedPolicy info = incumbentBehavioralPolicy info := by
  exact InformationModel.BehavioralPolicy.commit_of_ne
    incumbentBehavioralPolicy firstSite.1 (firstChoice true) hinfo

theorem secondTruePolicies_eq_off_first
    {info : Knowledge} (hinfo : info ≠ firstSite.1) :
    firstCommittedSecondTruePolicy info =
      incumbentSecondTruePolicy info := by
  unfold firstCommittedSecondTruePolicy incumbentSecondTruePolicy
  by_cases hsecond : info = (secondSite true).1
  · subst info
    rw [InformationModel.BehavioralPolicy.commit_self (M := information),
      InformationModel.BehavioralPolicy.commit_self (M := information)]
  · rw [InformationModel.BehavioralPolicy.commit_of_ne
        (M := information) _ _ _ hsecond,
      InformationModel.BehavioralPolicy.commit_of_ne
        (M := information) _ _ _ hsecond]
    exact firstCommitted_eq_incumbent_off_first hinfo

theorem counterfactualReach_firstCommitted_eq_incumbent
    (history : information.InformationHistory () (secondSite true).1) :
    information.counterfactualReachProbability firstCommittedStrategy ()
        history.1.trace =
      information.counterfactualReachProbability
        incumbentBehavioralStrategy () history.1.trace := by
  exact information.counterfactualReachProbability_eq_of_eq_off
    (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      history.1.trace

theorem secondInformationHistory_after_firstDepth
    (history : information.InformationHistory () (secondSite true).1) :
    1 < history.1.trace.length := by
  have hlength := secondSite_commonDepth true history
  omega

/-- Earlier first-site commitments are invisible to the later site's local
counterfactual regret. Thus the off-path term remains the proved unit term. -/
theorem firstCommitted_second_counterfactualActionRegret :
    information.counterfactualActionRegret firstCommittedStrategy ()
      (secondSite true) terminalPayoff 1 (secondChoice true true) = 1 := by
  have halternative :
      information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedSecondTruePolicy terminalPayoff 1 =
        information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
            incumbentSecondTruePolicy terminalPayoff 1 := by
    unfold InformationModel.counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    rw [counterfactualReach_firstCommitted_eq_incumbent]
    apply congrArg
      (fun value : ℝ =>
        information.counterfactualReachProbability
            incumbentBehavioralStrategy () history.1.trace * value)
    unfold InformationModel.behavioralContinuationValue
    apply congrArg
      (fun law : FinDist twoStage.History => law.expect terminalPayoff)
    exact information.runBehavioralFrom_eq_of_agree_off_pastSite
      (Profile.update (sig := information.behavioralSignature)
        firstCommittedStrategy () firstCommittedSecondTruePolicy)
      (Profile.update (sig := information.behavioralSignature)
        incumbentBehavioralStrategy () incumbentSecondTruePolicy)
      () firstSite 1 firstSite_commonDepth
      (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      (fun hinfo => by
        rw [Profile.update_same, Profile.update_same]
        exact secondTruePolicies_eq_off_first hinfo)
      history.1 (secondInformationHistory_after_firstDepth history) 1
  have hbaseline :
      information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedPolicy terminalPayoff 1 =
        information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
            incumbentBehavioralPolicy terminalPayoff 1 := by
    unfold InformationModel.counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    rw [counterfactualReach_firstCommitted_eq_incumbent]
    apply congrArg
      (fun value : ℝ =>
        information.counterfactualReachProbability
            incumbentBehavioralStrategy () history.1.trace * value)
    unfold InformationModel.behavioralContinuationValue
    apply congrArg
      (fun law : FinDist twoStage.History => law.expect terminalPayoff)
    exact information.runBehavioralFrom_eq_of_agree_off_pastSite
      (Profile.update (sig := information.behavioralSignature)
        firstCommittedStrategy () firstCommittedPolicy)
      (Profile.update (sig := information.behavioralSignature)
        incumbentBehavioralStrategy () incumbentBehavioralPolicy)
      () firstSite 1 firstSite_commonDepth
      (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      (fun hinfo => by
        rw [Profile.update_same, Profile.update_same]
        exact firstCommitted_eq_incumbent_off_first hinfo)
      history.1 (secondInformationHistory_after_firstDepth history) 1
  unfold InformationModel.counterfactualActionRegret
    InformationModel.counterfactualRegret
  rw [show firstCommittedStrategy () = firstCommittedPolicy by rfl,
    show firstCommittedPolicy.commit (secondSite true).1
        (secondChoice true true) = firstCommittedSecondTruePolicy by rfl,
    halternative, hbaseline,
    show incumbentSecondTruePolicy =
        incumbentBehavioralPolicy.commit (secondSite true).1
          (secondChoice true true) by rfl]
  exact offPathSecond_counterfactualActionRegret

/-- The decisive off-path local update has exact unit root gain. -/
theorem secondCommit_rootGain_eq_one :
    (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 3).expect terminalPayoff -
      (information.runBehavioral firstCommittedStrategy 3).expect
        terminalPayoff = 1 := by
  rw [secondCommit_rootGain_eq_counterfactualActionRegret,
    firstCommitted_second_counterfactualActionRegret]

def finalCommittedStrategy : (who : Unit) →
    information.BehavioralPolicy who :=
  Profile.update (sig := information.behavioralSignature)
    firstCommittedStrategy () firstCommittedSecondTruePolicy

def deviationPath : ℕ → (who : Unit) →
    information.BehavioralPolicy who
  | 0 => incumbentBehavioralStrategy
  | 1 => firstCommittedStrategy
  | _ => finalCommittedStrategy

def pathLocalRegret : ℕ → ℝ
  | 0 => information.counterfactualActionRegret
      incumbentBehavioralStrategy () firstSite terminalPayoff 2
        (firstChoice true)
  | _ => information.counterfactualActionRegret
      firstCommittedStrategy () (secondSite true) terminalPayoff 1
        (secondChoice true true)

theorem firstCommittedStrategy_eq_update :
    firstCommittedStrategy =
      Profile.update (sig := information.behavioralSignature)
        incumbentBehavioralStrategy () firstCommittedPolicy := by
  funext who
  cases who
  rw [Profile.update_same]
  rfl

theorem deviationPath_stepRootGain
    (step : ℕ) (hstep : step < 2) :
    (information.runBehavioral (deviationPath (step + 1)) 3).expect
          terminalPayoff -
        (information.runBehavioral (deviationPath step) 3).expect
          terminalPayoff =
      1 * pathLocalRegret step := by
  interval_cases step
  · rw [show deviationPath (0 + 1) = firstCommittedStrategy by rfl,
      show deviationPath 0 = incumbentBehavioralStrategy by rfl,
      firstCommittedStrategy_eq_update,
      show firstCommittedPolicy =
          incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true) by
        rfl,
      firstCommit_rootGain_eq_zero,
      show pathLocalRegret 0 =
          information.counterfactualActionRegret
            incumbentBehavioralStrategy () firstSite terminalPayoff 2
              (firstChoice true) by rfl,
      first_counterfactualActionRegret, mul_zero]
  · simpa [deviationPath, pathLocalRegret, finalCommittedStrategy,
      firstCommittedSecondTruePolicy] using
        secondCommit_rootGain_eq_counterfactualActionRegret

/-- The two topologically ordered local bridges telescope to the exact whole
behavioral-policy root gain, with both local regret terms visible. -/
theorem wholeDeviation_rootGain_eq_localSum :
    (information.runBehavioral finalCommittedStrategy 3).expect
          terminalPayoff -
        (information.runBehavioral incumbentBehavioralStrategy 3).expect
          terminalPayoff =
      ∑ step ∈ Finset.range 2, 1 * pathLocalRegret step := by
  exact information.rootGain_eq_sum_stepCounterfactualTerms deviationPath
    terminalPayoff 3 2 (fun _ => 1) pathLocalRegret
      deviationPath_stepRootGain

/-- The global root consumer is nonvacuous: the coordinated two-site policy
has exact unit gain although its first local term is zero. -/
theorem wholeDeviation_rootGain_eq_one :
    (information.runBehavioral finalCommittedStrategy 3).expect
          terminalPayoff -
        (information.runBehavioral incumbentBehavioralStrategy 3).expect
          terminalPayoff = 1 := by
  rw [wholeDeviation_rootGain_eq_localSum]
  simp [pathLocalRegret, first_counterfactualActionRegret,
    firstCommitted_second_counterfactualActionRegret]
  norm_num [Finset.sum_range_succ]

end GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
