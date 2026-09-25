/-
# Experiment 111 test: a realizable live-policy deviation

The empty public history is in the canonical image, so changing a policy
there changes both the canonical public-history law and the payoff.
-/

import GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherence

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherenceTest

open GameTheory.Math.Probability GameTheory.Stochastic
open GameTheory.Stochastic.Game GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherence
open GameTheory.Tests.StochasticContinuation

local instance actionNonempty : ∀ i, Nonempty (actionGame.Action i) :=
  fun _ => ⟨false⟩

def liveRecord : actionGame.StageRecord where
  source := false
  joint := secondActions
  target := false

theorem livePublicProfile_initial (who : Bool) :
    livePublicProfile who [] = PMF.pure (secondActions who) := by
  cases who <;> rfl

theorem empty_history_realizable :
    PublicHistoryRealizable actionGame false [] := by
  exact publicHistoryRealizable_of_history actionGame
    (actionGame.toExecution false).initHistory

theorem liveProfile_not_agreement :
    ¬ PublicHistoryAgreement actionGame false canonicalProfile liveProfile := by
  intro hagree
  have hpolicy := hagree [] empty_history_realizable false
  have hpublic : publicProfile false [] = livePublicProfile false [] := by
    apply (pmf_map_injective
      (actionChoiceEquiv actionGame false false []).injective)
    simpa [canonicalProfile, liveProfile, toBehaviorProfile,
      toBehavioralPolicy] using hpolicy
  exact live_first_action_differs hpublic.symm

theorem live_publicHistoryLaw_one :
    actionGame.publicHistoryLaw false liveProfile 1 =
      PMF.pure [liveRecord] := by
  have hrestart :
      actionGame.restartHistoryLaw liveProfile [] false 1 =
        PMF.pure [liveRecord] := by
    unfold liveProfile
    rw [actionGame.restartHistoryLaw_succ_toPublicProfile
      livePublicProfile [] false 0]
    simp_rw [livePublicProfile_initial]
    rw [independentProduct_pure secondActions, PMF.pure_bind]
    simp only [actionGame, PMF.pure_bindOnSupport]
    rw [Game.restartHistoryLaw_zero, PMF.pure_map]
    simp [liveRecord, secondActions]
  simpa only [Game.restartHistoryLaw, Game.afterPublicHistory_nil] using hrestart

theorem canonical_publicHistoryLaw_one :
    actionGame.publicHistoryLaw false canonicalProfile 1 =
      PMF.pure [firstRecord] := by
  have hrestart :
      actionGame.restartHistoryLaw canonicalProfile [] false 1 =
        PMF.pure [firstRecord] := by
    unfold canonicalProfile
    rw [actionGame.restartHistoryLaw_succ_toPublicProfile
      publicProfile [] false 0]
    simp_rw [publicProfile_initial]
    rw [independentProduct_pure firstActions, PMF.pure_bind]
    simp only [actionGame, PMF.pure_bindOnSupport]
    rw [Game.restartHistoryLaw_zero, PMF.pure_map]
    simp [firstRecord, firstActions]
  simpa only [Game.restartHistoryLaw, Game.afterPublicHistory_nil] using hrestart

theorem live_publicHistoryLaw_differs :
    actionGame.publicHistoryLaw false canonicalProfile 1 ≠
      actionGame.publicHistoryLaw false liveProfile 1 := by
  rw [canonical_publicHistoryLaw_one, live_publicHistoryLaw_one]
  intro heq
  have htargets := congrArg
    (PMF.map (List.map StageRecord.target)) heq
  rw [PMF.pure_map, PMF.pure_map] at htargets
  have hmass := congrArg (fun law : PMF (List Bool) => law [true]) htargets
  simp [firstRecord, liveRecord, PMF.pure_apply] at hmass

/-- The canonical one-step profile has an integrable finite-average payoff. -/
theorem canonical_integrable :
    UtilityIntegrable (actionGame.horizonUtility false 1) false
      ((actionGame.horizonForm false 1).play canonicalProfile) := by
  apply (actionGame.publicFiniteAverageIntegrable_iff
    false 1 canonicalProfile false).mp
  rw [canonical_publicHistoryLaw_one]
  exact payoffIntegrable_pure [firstRecord]
    (fun history => actionGame.publicHistoryAverageUtility 1 history false)

/-- The live one-step profile has an integrable finite-average payoff. -/
theorem live_integrable :
    UtilityIntegrable (actionGame.horizonUtility false 1) false
      ((actionGame.horizonForm false 1).play liveProfile) := by
  apply (actionGame.publicFiniteAverageIntegrable_iff
    false 1 liveProfile false).mp
  rw [live_publicHistoryLaw_one]
  exact payoffIntegrable_pure [liveRecord]
    (fun history => actionGame.publicHistoryAverageUtility 1 history false)

theorem canonical_finiteAveragePayoff_one :
    actionGame.finiteAveragePayoff false 1 canonicalProfile false
      canonical_integrable = 0 := by
  have hpublic := (actionGame.publicFiniteAverageIntegrable_iff
    false 1 canonicalProfile false).mpr canonical_integrable
  rw [← actionGame.publicFiniteAveragePayoff_eq_finiteAveragePayoff
    false 1 canonicalProfile false hpublic canonical_integrable]
  unfold publicFiniteAveragePayoff
  calc
    expectedUtility (actionGame.publicHistoryAverageUtility 1) false
        (actionGame.publicHistoryLaw false canonicalProfile 1) hpublic =
      expectedUtility (actionGame.publicHistoryAverageUtility 1) false
        (PMF.pure [firstRecord])
        (payoffIntegrable_pure [firstRecord]
          (fun history => actionGame.publicHistoryAverageUtility 1 history false)) :=
        expectedUtility_congr_law _ _ canonical_publicHistoryLaw_one _ _
    _ = 0 := by
      simp [publicHistoryAverageUtility, stageRecordUtility, firstRecord,
        actionGame, firstActions]

theorem live_finiteAveragePayoff_one :
    actionGame.finiteAveragePayoff false 1 liveProfile false
      live_integrable = 1 := by
  have hpublic := (actionGame.publicFiniteAverageIntegrable_iff
    false 1 liveProfile false).mpr live_integrable
  rw [← actionGame.publicFiniteAveragePayoff_eq_finiteAveragePayoff
    false 1 liveProfile false hpublic live_integrable]
  unfold publicFiniteAveragePayoff
  calc
    expectedUtility (actionGame.publicHistoryAverageUtility 1) false
        (actionGame.publicHistoryLaw false liveProfile 1) hpublic =
      expectedUtility (actionGame.publicHistoryAverageUtility 1) false
        (PMF.pure [liveRecord])
        (payoffIntegrable_pure [liveRecord]
          (fun history => actionGame.publicHistoryAverageUtility 1 history false)) :=
        expectedUtility_congr_law _ _ live_publicHistoryLaw_one _ _
    _ = 1 := by
      simp [publicHistoryAverageUtility, stageRecordUtility, liveRecord,
        actionGame, secondActions]

theorem finiteAveragePayoff_one_differs :
    actionGame.finiteAveragePayoff false 1 canonicalProfile false
      canonical_integrable ≠
      actionGame.finiteAveragePayoff false 1 liveProfile false
        live_integrable := by
  rw [canonical_finiteAveragePayoff_one, live_finiteAveragePayoff_one]
  norm_num

end GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherenceTest
