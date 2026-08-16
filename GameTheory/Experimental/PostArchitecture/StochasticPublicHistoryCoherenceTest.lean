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
    livePublicProfile who [] = FinDist.pure (secondActions who) := by
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
    apply (FinDist.map_injective
      (actionChoiceEquiv actionGame false false []).injective)
    simpa [canonicalProfile, liveProfile, toBehaviorProfile,
      toBehavioralPolicy] using hpolicy
  exact live_first_action_differs hpublic.symm

theorem live_publicHistoryLaw_one :
    actionGame.publicHistoryLaw false liveProfile 1 =
      FinDist.pure [liveRecord] := by
  have hrestart :
      actionGame.restartHistoryLaw liveProfile [] false 1 =
        FinDist.pure [liveRecord] := by
    unfold liveProfile
    rw [actionGame.restartHistoryLaw_succ_toPublicProfile
      livePublicProfile [] false 0]
    simp_rw [livePublicProfile_initial]
    rw [FinDist.pi_pure secondActions, FinDist.pure_bind]
    simp only [actionGame, FinDist.pure_bindOnSupport]
    rw [Game.restartHistoryLaw_zero, FinDist.map_pure]
    simp [liveRecord, secondActions]
  simpa only [Game.restartHistoryLaw, Game.afterPublicHistory_nil] using hrestart

theorem canonical_publicHistoryLaw_one :
    actionGame.publicHistoryLaw false canonicalProfile 1 =
      FinDist.pure [firstRecord] := by
  have hrestart :
      actionGame.restartHistoryLaw canonicalProfile [] false 1 =
        FinDist.pure [firstRecord] := by
    unfold canonicalProfile
    rw [actionGame.restartHistoryLaw_succ_toPublicProfile
      publicProfile [] false 0]
    simp_rw [publicProfile_initial]
    rw [FinDist.pi_pure firstActions, FinDist.pure_bind]
    simp only [actionGame, FinDist.pure_bindOnSupport]
    rw [Game.restartHistoryLaw_zero, FinDist.map_pure]
    simp [firstRecord, firstActions]
  simpa only [Game.restartHistoryLaw, Game.afterPublicHistory_nil] using hrestart

theorem live_publicHistoryLaw_differs :
    actionGame.publicHistoryLaw false canonicalProfile 1 ≠
      actionGame.publicHistoryLaw false liveProfile 1 := by
  rw [canonical_publicHistoryLaw_one, live_publicHistoryLaw_one]
  intro heq
  have htargets := congrArg
    (FinDist.map (List.map StageRecord.target)) heq
  have hprob := congrArg (fun law => law.prob [true]) htargets
  simp [firstRecord, liveRecord, FinDist.prob_pure_eq_ite] at hprob

theorem canonical_finiteAveragePayoff_one :
    actionGame.finiteAveragePayoff false 1 canonicalProfile false = 0 := by
  rw [← actionGame.publicFiniteAveragePayoff_eq_finiteAveragePayoff
    false 1 canonicalProfile false]
  unfold publicFiniteAveragePayoff
  rw [canonical_publicHistoryLaw_one]
  simp [publicHistoryAverageUtility, stageRecordUtility, firstRecord,
    actionGame, firstActions]

theorem live_finiteAveragePayoff_one :
    actionGame.finiteAveragePayoff false 1 liveProfile false = 1 := by
  rw [← actionGame.publicFiniteAveragePayoff_eq_finiteAveragePayoff
    false 1 liveProfile false]
  unfold publicFiniteAveragePayoff
  rw [live_publicHistoryLaw_one]
  simp [publicHistoryAverageUtility, stageRecordUtility, liveRecord,
    actionGame, secondActions]

theorem finiteAveragePayoff_one_differs :
    actionGame.finiteAveragePayoff false 1 canonicalProfile false ≠
      actionGame.finiteAveragePayoff false 1 liveProfile false := by
  rw [canonical_finiteAveragePayoff_one, live_finiteAveragePayoff_one]
  norm_num

end GameTheory.Experimental.PostArchitecture.StochasticPublicHistoryCoherenceTest
