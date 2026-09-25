/-
# EXP-092 hostile stochastic consumer

A public random transition is observed before the second simultaneous action.
An ordinary public-history policy that follows that signal strictly improves a
player's whole two-stage payoff over a constant policy.  The final comparison
uses the canonical Protocol runner and canonical approximate-Nash predicate.
-/

import GameTheory.Stochastic.History
import GameTheory.Math.Probability.Mixture
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticProofView.Hostile

open GameTheory.Math.Probability Stochastic Protocol Protocol.ExecutionProtocol

/-- A fair public signal represented as the next stochastic-game state. -/
def fairSignal : PMF (Option Bool) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (some false)) (PMF.pure (some true))

/-- The first stage publicly draws a bit. At the second stage player `false`
earns two exactly when its action matches the observed bit. -/
@[reducible]
def signalGame : Stochastic.Game Bool where
  State := Option Bool
  Action := fun _ => Bool
  transition state _ :=
    match state with
    | none => fairSignal
    | some signal => PMF.pure (some signal)
  stageUtility state actions who :=
    if who then 0
    else match state with
      | none => 0
      | some signal => if actions false = signal then 2 else 0

local instance signalGameActionNonempty :
    ∀ i, Nonempty (signalGame.Action i) :=
  fun _ => ⟨false⟩

/-- The status-quo action ignores the public history. -/
def constantFalsePolicy (i : Bool) : Game.PublicPolicy signalGame i :=
  fun _ => PMF.pure false

/-- Player `false` follows the latest public target signal, if one exists. -/
def followSignalPolicy : Game.PublicPolicy signalGame false :=
  fun history =>
    PMF.pure <| match history with
      | [] => false
      | latest :: _ => latest.target.getD false

/-- Both players initially use the constant policy. -/
def constantProfile : Game.PublicProfile signalGame none :=
  fun i => constantFalsePolicy i

/-- The direct unilateral splice installs the history-dependent policy. -/
def contingentProfile : Game.PublicProfile signalGame none :=
  Profile.update constantProfile false followSignalPolicy

/-- A proof-free one-step history ending at a selected public signal. -/
def signalHistory (signal : Bool) : signalGame.PublicHistory :=
  [{ source := none, joint := fun _ => false, target := some signal }]

/-- The replacement really distinguishes the two observed public histories. -/
theorem followSignalPolicy_history_dependent :
    followSignalPolicy (signalHistory false) = PMF.pure false ∧
      followSignalPolicy (signalHistory true) = PMF.pure true := by
  constructor <;> rfl

/-- Both signal values occur with positive probability. -/
theorem fairSignal_nondegenerate :
    some false ∈ fairSignal.support ∧ some true ∈ fairSignal.support := by
  constructor
  · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)
  · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)

theorem fairSignal_support_iff (state : Option Bool) :
    state ∈ fairSignal.support ↔ ∃ signal, state = some signal := by
  cases state with
  | none =>
      simp [fairSignal, PMF.mem_support_iff, mix_apply, PMF.pure_apply]
  | some signal =>
      cases signal
      · exact iff_of_true fairSignal_nondegenerate.1 ⟨false, rfl⟩
      · exact iff_of_true fairSignal_nondegenerate.2 ⟨true, rfl⟩

/-- The joint action used before the signal is observed. -/
def allFalse : ∀ i, signalGame.Action i := fun _ => false

/-- Only player `false` varies in the second-stage comparison. -/
def responseActions (action : Bool) : ∀ i, signalGame.Action i :=
  fun who => if who then false else action

/-- Canonical history immediately after the public signal draw. -/
def firstHistory (signal : Bool) (realized : some signal ∈ fairSignal.support) :
    (signalGame.toExecution none).History :=
  (signalGame.toExecution none).initHistory.extend
    (Game.canonicalJoint signalGame none none allFalse).2
    (Game.canonicalRealized signalGame none realized)

@[simp]
theorem firstHistory_state (signal : Bool)
    (realized : some signal ∈ fairSignal.support) :
    (firstHistory signal realized).state = some signal :=
  rfl

/-- Canonical two-stage history after player `false` selects `action`. -/
def finalHistory (signal : Bool) (firstRealized : some signal ∈ fairSignal.support)
    (action : Bool) : (signalGame.toExecution none).History :=
  (firstHistory signal firstRealized).extend
    (Game.canonicalJoint signalGame none (some signal) (responseActions action)).2
    (Game.canonicalRealized signalGame none
      (state := some signal) (target := some signal)
      (actions := responseActions action) (by simp [signalGame]))

theorem infoOf_firstHistory (signal : Bool)
    (realized : some signal ∈ fairSignal.support) (who : Bool) :
    (signalGame.perfectMonitoring none).infoOf who
        (firstHistory signal realized).trace = signalHistory signal := by
  show [signalGame.stageRecordOfEvent none
      (Game.canonicalEvent signalGame none allFalse realized)] =
    signalHistory signal
  apply congrArg (fun record => [record])
  congr 1

theorem constantProfile_after_signal (signal : Bool)
    (realized : some signal ∈ fairSignal.support) (who : Bool) :
    constantProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (firstHistory signal realized).trace) =
      PMF.pure false :=
  rfl

theorem contingentProfile_after_signal (signal : Bool)
    (realized : some signal ∈ fairSignal.support) (who : Bool) :
    contingentProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (firstHistory signal realized).trace) =
      PMF.pure (responseActions signal who) := by
  rw [infoOf_firstHistory]
  cases who <;>
    simp [contingentProfile, constantProfile, constantFalsePolicy,
      followSignalPolicy, signalHistory, responseActions]

theorem constantProfile_initial (who : Bool) :
    constantProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (signalGame.toExecution none).initHistory.trace) =
      PMF.pure (allFalse who) :=
  rfl

theorem contingentProfile_initial (who : Bool) :
    contingentProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (signalGame.toExecution none).initHistory.trace) =
      PMF.pure (allFalse who) := by
  cases who
  · show followSignalPolicy [] = PMF.pure false
    rfl
  · rfl

private theorem historyAverageUtility_two_steps
    (signal action : Bool)
    (firstRealized : some signal ∈ fairSignal.support) :
    signalGame.historyAverageUtility none 2
        (finalHistory signal firstRealized action) false =
      if action = signal then 1 else 0 := by
  show (2 : ℝ)⁻¹ *
      ((0 + signalGame.eventUtility none
          (Game.canonicalEvent signalGame none allFalse firstRealized) false) +
        signalGame.eventUtility none
          (Game.canonicalEvent signalGame none
            (state := some signal) (target := some signal)
            (responseActions action) (by simp [signalGame])) false) =
      if action = signal then 1 else 0
  simp [signalGame, firstHistory, responseActions]

private theorem secondStageLaw
    (profile : Game.PublicProfile signalGame none) (signal action : Bool)
    (realized : some signal ∈ fairSignal.support)
    (hlaws : ∀ who,
      profile who
          ((signalGame.perfectMonitoring none).infoOf who
            (firstHistory signal realized).trace) =
        PMF.pure (responseActions action who)) :
    (signalGame.perfectMonitoring none).runBehavioralFrom
        (Game.toBehaviorProfile signalGame none profile) 1
        (firstHistory signal realized) =
      PMF.pure (finalHistory signal realized action) := by
  rw [Game.runBehavioralFrom_succ_toBehaviorProfile signalGame none profile 0
    (firstHistory signal realized)]
  simp_rw [hlaws]
  simp only [independentProduct_pure, PMF.pure_bind]
  simp only [firstHistory_state]
  show (PMF.pure (some signal)).bindOnSupport
      (fun _ targetRealized =>
        PMF.pure
          ((firstHistory signal realized).extend
            (Game.canonicalJoint signalGame none (some signal)
              (responseActions action)).2
            (Game.canonicalRealized signalGame none targetRealized))) = _
  rw [PMF.pure_bindOnSupport]
  simp only [finalHistory]

private theorem fairSignal_supported (signal : Bool) :
    some signal ∈ fairSignal.support := by
  cases signal
  · exact fairSignal_nondegenerate.1
  · exact fairSignal_nondegenerate.2

private def finalOutcome (choose : Bool → Bool) (state : Option Bool) :
    (signalGame.toExecution none).History :=
  match state with
  | none => (signalGame.toExecution none).initHistory
  | some signal => finalHistory signal (fairSignal_supported signal) (choose signal)

private theorem twoStageLaw (profile : Game.PublicProfile signalGame none)
    (choose : Bool → Bool)
    (hinitial : ∀ who, profile who
      ((signalGame.perfectMonitoring none).infoOf who
        (signalGame.toExecution none).initHistory.trace) =
        PMF.pure (allFalse who))
    (hresponse : ∀ signal realized who,
      profile who
        ((signalGame.perfectMonitoring none).infoOf who
          (firstHistory signal realized).trace) =
        PMF.pure (responseActions (choose signal) who)) :
    (signalGame.perfectMonitoring none).runBehavioral
        (Game.toBehaviorProfile signalGame none profile) 2 =
      PMF.map (finalOutcome choose) fairSignal := by
  unfold InformationModel.runBehavioral
  rw [Game.runBehavioralFrom_succ_toBehaviorProfile signalGame none profile 1
    (signalGame.toExecution none).initHistory]
  simp_rw [hinitial]
  simp only [independentProduct_pure, PMF.pure_bind]
  show fairSignal.bindOnSupport (fun state stateRealized =>
      (signalGame.perfectMonitoring none).runBehavioralFrom
        (Game.toBehaviorProfile signalGame none profile) 1
        ((signalGame.toExecution none).initHistory.extend
          (Game.canonicalJoint signalGame none none allFalse).2
          (Game.canonicalRealized signalGame none stateRealized))) = _
  calc
    _ = fairSignal.bindOnSupport
        (fun state _ => PMF.pure (finalOutcome choose state)) := by
      apply bindOnSupport_congr
      intro state stateRealized
      obtain ⟨signal, rfl⟩ := (fairSignal_support_iff state).mp stateRealized
      simpa only [firstHistory, finalOutcome] using
        secondStageLaw profile signal (choose signal) stateRealized
          (hresponse signal stateRealized)
    _ = PMF.map (finalOutcome choose) fairSignal := by
      rw [PMF.bindOnSupport_eq_bind]
      exact PMF.bind_pure_comp _ _

private theorem twoStageIntegrable (choose : Bool → Bool) :
    PayoffIntegrable (PMF.map (finalOutcome choose) fairSignal)
      (fun history => signalGame.horizonUtility none 2 history false) := by
  apply (payoffIntegrable_map_iff (finalOutcome choose) fairSignal _).2
  exact payoffIntegrable_of_finite fairSignal _

private theorem twoStagePayoff (profile : Game.PublicProfile signalGame none)
    (choose : Bool → Bool)
    (hinitial : ∀ who, profile who
      ((signalGame.perfectMonitoring none).infoOf who
        (signalGame.toExecution none).initHistory.trace) =
        PMF.pure (allFalse who))
    (hresponse : ∀ signal realized who,
      profile who
        ((signalGame.perfectMonitoring none).infoOf who
          (firstHistory signal realized).trace) =
        PMF.pure (responseActions (choose signal) who)) :
    signalGame.finiteAveragePayoff none 2
        (Game.toBehaviorProfile signalGame none profile) false
        (by rw [signalGame.horizonForm_play,
            twoStageLaw profile choose hinitial hresponse]
            exact twoStageIntegrable choose) =
      ((if choose false = false then 1 else 0) +
        (if choose true = true then 1 else 0)) / 2 := by
  unfold Game.finiteAveragePayoff expectedUtility
  have hlaw :
      (signalGame.horizonForm none 2).play
          (Game.toBehaviorProfile signalGame none profile) =
        PMF.map (finalOutcome choose) fairSignal := by
    rw [signalGame.horizonForm_play]
    exact twoStageLaw profile choose hinitial hresponse
  have hvalue (signal : Bool) :
      signalGame.horizonUtility none 2 (finalOutcome choose (some signal)) false =
        if choose signal = signal then 1 else 0 := by
    exact historyAverageUtility_two_steps signal (choose signal)
      (fairSignal_supported signal)
  calc
    _ = expect (PMF.map (finalOutcome choose) fairSignal)
        (fun history => signalGame.horizonUtility none 2 history false)
        (twoStageIntegrable choose) :=
      expect_congr_law hlaw _ _ _
    _ = expect fairSignal
        ((fun history => signalGame.horizonUtility none 2 history false) ∘
          finalOutcome choose)
        (payoffIntegrable_of_finite fairSignal _) :=
      expect_map (finalOutcome choose) fairSignal _ _ _
    _ = _ := by
      rw [expect_eq_sum]
      simp only [Fintype.sum_option, Fintype.sum_bool]
      simp [fairSignal, mix_apply, PMF.pure_apply]
      rw [hvalue true, hvalue false]
      norm_num
      cases hfalse : choose false <;> cases htrue : choose true <;>
        norm_num [hfalse, htrue]

/-- The constant policy's actual two-step history law integrates its payoff. -/
theorem constantProfileIntegrable :
    UtilityIntegrable (signalGame.horizonUtility none 2) false
      ((signalGame.horizonForm none 2).play
        (Game.toBehaviorProfile signalGame none constantProfile)) := by
  rw [signalGame.horizonForm_play,
    twoStageLaw constantProfile (fun _ => false)
      constantProfile_initial (fun signal realized who => by
        simpa [responseActions] using
          constantProfile_after_signal signal realized who)]
  exact twoStageIntegrable (fun _ => false)

/-- The signal-following policy's actual two-step law integrates its payoff. -/
theorem contingentProfileIntegrable :
    UtilityIntegrable (signalGame.horizonUtility none 2) false
      ((signalGame.horizonForm none 2).play
        (Game.toBehaviorProfile signalGame none contingentProfile)) := by
  rw [signalGame.horizonForm_play,
    twoStageLaw contingentProfile id contingentProfile_initial
      (fun signal realized who =>
        contingentProfile_after_signal signal realized who)]
  exact twoStageIntegrable id

/-- Ignoring the fair signal earns one half of the two-stage average payoff. -/
theorem constantProfile_payoff :
    signalGame.finiteAveragePayoff none 2
        (Game.toBehaviorProfile signalGame none constantProfile) false
        constantProfileIntegrable = 1 / 2 := by
  rw [twoStagePayoff constantProfile (fun _ => false)
    constantProfile_initial (fun signal realized who => by
      simpa [responseActions] using
        constantProfile_after_signal signal realized who)]
  norm_num

/-- Following either realized signal earns the full two-stage average payoff. -/
theorem contingentProfile_payoff :
    signalGame.finiteAveragePayoff none 2
        (Game.toBehaviorProfile signalGame none contingentProfile) false
        contingentProfileIntegrable = 1 := by
  rw [twoStagePayoff contingentProfile id contingentProfile_initial
    (fun signal realized who =>
      contingentProfile_after_signal signal realized who)]
  norm_num

/-- The stochastic-facing unilateral splice compiles to exactly the canonical
Protocol profile replacement. -/
theorem canonical_contingent_update :
    Game.toBehaviorProfile signalGame none contingentProfile =
      Profile.update
        (Game.toBehaviorProfile signalGame none constantProfile) false
        (Game.toBehavioralPolicy signalGame none followSignalPolicy) := by
  unfold contingentProfile
  exact Game.toBehaviorProfile_update signalGame none constantProfile false
    followSignalPolicy

/-- The genuinely history-dependent whole-policy deviation improves the exact
two-stage average by one half. -/
theorem contingent_improvement_exact :
    signalGame.finiteAveragePayoff none 2
          (Game.toBehaviorProfile signalGame none contingentProfile) false
          contingentProfileIntegrable -
        signalGame.finiteAveragePayoff none 2
          (Game.toBehaviorProfile signalGame none constantProfile) false
          constantProfileIntegrable =
      1 / 2 := by
  rw [contingentProfile_payoff, constantProfile_payoff]
  norm_num

/-- Consequently the constant public policy profile fails the canonical
zero-tolerance approximate-Nash predicate. No local stochastic equilibrium
predicate is introduced. -/
theorem constantProfile_not_isZeroHorizonNash :
    ¬ signalGame.IsεHorizonNash none 2 0
      (Game.toBehaviorProfile signalGame none constantProfile) := by
  rw [signalGame.isεHorizonNash_iff]
  intro hNash
  have hdeviation := hNash false
    (Game.toBehavioralPolicy signalGame none followSignalPolicy)
  obtain ⟨hprofile, hchanged, hle⟩ := hdeviation
  have hchangedValue : signalGame.finiteAveragePayoff none 2
      (Profile.update (Game.toBehaviorProfile signalGame none constantProfile)
        false (Game.toBehavioralPolicy signalGame none followSignalPolicy))
      false hchanged = 1 := by
    calc
      _ = signalGame.finiteAveragePayoff none 2
          (Game.toBehaviorProfile signalGame none contingentProfile) false
          contingentProfileIntegrable := by
        exact expectedUtility_congr_law
          (signalGame.horizonUtility none 2) false
          (congrArg (fun profile => (signalGame.horizonForm none 2).play profile)
            canonical_contingent_update.symm) _ _
      _ = 1 := contingentProfile_payoff
  have hprofileValue : signalGame.finiteAveragePayoff none 2
      (Game.toBehaviorProfile signalGame none constantProfile) false hprofile = 1 / 2 := by
    simpa only using constantProfile_payoff
  rw [hchangedValue, hprofileValue] at hle
  norm_num at hle

end GameTheory.Experimental.PostArchitecture.StochasticProofView.Hostile
