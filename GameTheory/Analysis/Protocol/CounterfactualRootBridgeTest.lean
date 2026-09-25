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

def rootValue
    (strategy : (who : Unit) → information.BehavioralPolicy who) : ℝ :=
  expect (information.runBehavioral strategy 3) terminalPayoff
    (terminalPayoff_integrable _)

def guardedActionRegret
    (strategy : (who : Unit) → information.BehavioralPolicy who)
    (site : information.InformationSite ())
    [Fintype (information.InformationHistory () site.1)]
    (fuel : ℕ) (choice : information.Choice () site.1) : ℝ :=
  information.counterfactualActionRegret strategy () site terminalPayoff fuel
    choice (counterfactualIntegrable strategy site
      ((strategy ()).commit site.1 choice) fuel)
      (counterfactualIntegrable strategy site (strategy ()) fuel)

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
    rootValue
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice true))) -
      rootValue incumbentBehavioralStrategy =
    information.playerReachProbability incumbentBehavioralStrategy ()
        firstSite.2.choose.1.trace *
      guardedActionRegret incumbentBehavioralStrategy firstSite 2
        (firstChoice true) := by
  simpa [rootValue, guardedActionRegret,
    show incumbentBehavioralStrategy () = incumbentBehavioralPolicy by rfl]
    using
    rootGain_eq_representativeReach_mul_counterfactualActionRegret_of_perfectRecall
      information information_perfectRecall incumbentBehavioralStrategy ()
      firstSite (firstChoice true) 1 2 firstSite_commonDepth terminalPayoff
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) 2)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        incumbentBehavioralPolicy 2)

/-- The generic single-site theorem proves at the root, not merely inside the
information fiber, that changing only the first action gains exactly zero. -/
theorem firstCommit_rootGain_eq_zero :
    rootValue
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice true))) -
      rootValue incumbentBehavioralStrategy = 0 := by
  rw [firstCommit_perfectRecallRootBridge]
  simp only [guardedActionRegret]
  rw [first_counterfactualActionRegret, mul_zero]

theorem firstCommittedOwnReach_secondTrue (hidden : Bool) :
    information.playerReachProbability firstCommittedStrategy ()
      (secondHistory hidden true).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
  rw [show decodeRecord [(Stage.first, true)] =
      [(firstKnowledge, true)] by rfl,
    InformationModel.ownPlayReachProbability]
  have hpolicy : firstCommittedPolicy firstKnowledge =
      PMF.pure (firstChoice true) := by
    unfold firstCommittedPolicy
    rw [InformationModel.BehavioralPolicy.commit_self (M := information)]
  rw [show firstCommittedStrategy () firstKnowledge =
      PMF.pure (firstChoice true) from hpolicy]
  simp [firstChoice, InformationModel.ownPlayReachProbability,
    PMF.pure_map]

theorem firstCommittedCommonOwnReach_secondTrue
    (history : information.InformationHistory () (secondSite true).1) :
    information.playerReachProbability firstCommittedStrategy ()
      history.1.trace = 1 := by
  rw [← (secondHistoryEquivBool true).symm_apply_apply history]
  exact firstCommittedOwnReach_secondTrue _

/-- The same generic root theorem reaches the off-path second update with its
unit alternative-own-reach coefficient. -/
theorem secondCommit_rootGain_eq_counterfactualActionRegret :
    rootValue
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) -
      rootValue firstCommittedStrategy =
    guardedActionRegret firstCommittedStrategy (secondSite true) 1
      (secondChoice true true) := by
  have hroot :=
    information.rootGain_eq_ownReach_mul_counterfactualRegret
      firstCommittedStrategy () (secondSite true)
        (firstCommittedPolicy.commit (secondSite true).1
          (secondChoice true true)) 2 1 (secondSite_commonDepth true)
        (fun hne =>
          InformationModel.BehavioralPolicy.commit_of_ne firstCommittedPolicy
            (secondSite true).1 (secondChoice true true) hne)
        1 firstCommittedCommonOwnReach_secondTrue terminalPayoff
        (terminalPayoff_integrable _) (terminalPayoff_integrable _)
        (counterfactualIntegrable firstCommittedStrategy (secondSite true)
          (firstCommittedPolicy.commit (secondSite true).1
            (secondChoice true true)) 1)
        (counterfactualIntegrable firstCommittedStrategy (secondSite true)
          firstCommittedPolicy 1)
  simpa [rootValue, guardedActionRegret,
    InformationModel.counterfactualActionRegret,
    show firstCommittedStrategy () = firstCommittedPolicy by rfl] using
    hroot

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
    guardedActionRegret firstCommittedStrategy (secondSite true) 1
      (secondChoice true true) = 1 := by
  have halternative :
      information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedSecondTruePolicy terminalPayoff 1
          (counterfactualIntegrable firstCommittedStrategy (secondSite true)
            firstCommittedSecondTruePolicy 1) =
        information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
            incumbentSecondTruePolicy terminalPayoff 1
            (counterfactualIntegrable incumbentBehavioralStrategy
              (secondSite true) incumbentSecondTruePolicy 1) := by
    unfold InformationModel.counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    have hreach := counterfactualReach_firstCommitted_eq_incumbent history
    by_cases hp : information.counterfactualReachProbability
        incumbentBehavioralStrategy () history.1.trace ≠ 0
    · simp only [hreach, dite_eq_left hp]
      apply congrArg
        (fun value : ℝ =>
          information.counterfactualReachProbability
              incumbentBehavioralStrategy () history.1.trace * value)
      unfold InformationModel.behavioralContinuationValue
      apply congrArg
        (fun law : PMF twoStage.History =>
          expect law terminalPayoff (terminalPayoff_integrable law))
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
    · simp only [hreach, dite_eq_right hp]
  have hbaseline :
      information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedPolicy terminalPayoff 1
          (counterfactualIntegrable firstCommittedStrategy (secondSite true)
            firstCommittedPolicy 1) =
        information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
            incumbentBehavioralPolicy terminalPayoff 1
            (counterfactualIntegrable incumbentBehavioralStrategy
              (secondSite true) incumbentBehavioralPolicy 1) := by
    unfold InformationModel.counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    have hreach := counterfactualReach_firstCommitted_eq_incumbent history
    by_cases hp : information.counterfactualReachProbability
        incumbentBehavioralStrategy () history.1.trace ≠ 0
    · simp only [hreach, dite_eq_left hp]
      apply congrArg
        (fun value : ℝ =>
          information.counterfactualReachProbability
              incumbentBehavioralStrategy () history.1.trace * value)
      unfold InformationModel.behavioralContinuationValue
      apply congrArg
        (fun law : PMF twoStage.History =>
          expect law terminalPayoff (terminalPayoff_integrable law))
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
    · simp only [hreach, dite_eq_right hp]
  calc
    guardedActionRegret firstCommittedStrategy (secondSite true) 1
        (secondChoice true true) =
      information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedSecondTruePolicy terminalPayoff 1
          (counterfactualIntegrable firstCommittedStrategy (secondSite true)
            firstCommittedSecondTruePolicy 1) -
        information.counterfactualContinuationValue firstCommittedStrategy ()
          (secondSite true) firstCommittedPolicy terminalPayoff 1
          (counterfactualIntegrable firstCommittedStrategy (secondSite true)
            firstCommittedPolicy 1) := by
        rfl
    _ = information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
          incumbentSecondTruePolicy terminalPayoff 1
          (counterfactualIntegrable incumbentBehavioralStrategy
            (secondSite true) incumbentSecondTruePolicy 1) -
        information.counterfactualContinuationValue
          incumbentBehavioralStrategy () (secondSite true)
          incumbentBehavioralPolicy terminalPayoff 1
          (counterfactualIntegrable incumbentBehavioralStrategy
            (secondSite true) incumbentBehavioralPolicy 1) := by
        rw [halternative, hbaseline]
    _ = 1 := by
      simpa [InformationModel.counterfactualActionRegret,
        InformationModel.counterfactualRegret, incumbentSecondTruePolicy,
        show incumbentBehavioralStrategy () = incumbentBehavioralPolicy by rfl]
        using offPathSecond_counterfactualActionRegret

/-- The decisive off-path local update has exact unit root gain. -/
theorem secondCommit_rootGain_eq_one :
    rootValue
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) -
      rootValue firstCommittedStrategy = 1 := by
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
  | 0 => guardedActionRegret incumbentBehavioralStrategy firstSite 2
      (firstChoice true)
  | _ => guardedActionRegret firstCommittedStrategy (secondSite true) 1
      (secondChoice true true)

theorem pathLocalRegret_zero : pathLocalRegret 0 = 0 := by
  simpa only [pathLocalRegret, guardedActionRegret] using
    first_counterfactualActionRegret

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
    rootValue (deviationPath (step + 1)) -
        rootValue (deviationPath step) =
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
          guardedActionRegret incumbentBehavioralStrategy firstSite 2
            (firstChoice true) by rfl,
      show guardedActionRegret incumbentBehavioralStrategy firstSite 2
          (firstChoice true) = 0 by
        simpa only [guardedActionRegret] using first_counterfactualActionRegret,
      mul_zero]
  · rw [one_mul]
    exact secondCommit_rootGain_eq_counterfactualActionRegret

/-- The two topologically ordered local bridges telescope to the exact whole
behavioral-policy root gain, with both local regret terms visible. -/
theorem wholeDeviation_rootGain_eq_localSum :
    rootValue finalCommittedStrategy -
        rootValue incumbentBehavioralStrategy =
      ∑ step ∈ Finset.range 2, 1 * pathLocalRegret step := by
  have hsum := information.rootGain_eq_sum_stepCounterfactualTerms
      deviationPath
      terminalPayoff 3 2 (fun _ => 1) pathLocalRegret
      (fun step _ => terminalPayoff_integrable _)
      (by
        intro step hstep
        simpa only [rootValue] using deviationPath_stepRootGain step hstep)
  rw [show deviationPath 2 = finalCommittedStrategy by rfl,
    show deviationPath 0 = incumbentBehavioralStrategy by rfl] at hsum
  simpa only [rootValue] using hsum

/-- The global root consumer is nonvacuous: the coordinated two-site policy
has exact unit gain although its first local term is zero. -/
theorem wholeDeviation_rootGain_eq_one :
    rootValue finalCommittedStrategy -
        rootValue incumbentBehavioralStrategy = 1 := by
  rw [wholeDeviation_rootGain_eq_localSum]
  norm_num [Finset.sum_range_succ]
  rw [pathLocalRegret_zero]
  have hsecond : pathLocalRegret 1 = 1 := by
    simpa only [pathLocalRegret] using
      firstCommitted_second_counterfactualActionRegret
  rw [hsecond]
  norm_num

end GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
