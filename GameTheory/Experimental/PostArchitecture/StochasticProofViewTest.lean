/-
# EXP-092 hostile stochastic consumer

A public random transition is observed before the second simultaneous action.
An ordinary public-history policy that follows that signal strictly improves a
player's whole two-stage payoff over a constant policy.  The final comparison
uses the canonical Protocol runner and canonical approximate-Nash predicate.
-/

import GameTheory.Stochastic.History
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticProofView.Hostile

open GameTheory.Math.Probability Stochastic Protocol Protocol.ExecutionProtocol

/-- A fair public signal represented as the next stochastic-game state. -/
def fairSignal : FinDist (Option Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (some false)) (FinDist.pure (some true))

/-- The first stage publicly draws a bit. At the second stage player `false`
earns two exactly when its action matches the observed bit. -/
@[reducible]
def signalGame : Stochastic.Game Bool where
  State := Option Bool
  Action := fun _ => Bool
  transition state _ :=
    match state with
    | none => fairSignal
    | some signal => FinDist.pure (some signal)
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
  fun _ => FinDist.pure false

/-- Player `false` follows the latest public target signal, if one exists. -/
def followSignalPolicy : Game.PublicPolicy signalGame false :=
  fun history =>
    FinDist.pure <| match history with
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
    followSignalPolicy (signalHistory false) = FinDist.pure false ∧
      followSignalPolicy (signalHistory true) = FinDist.pure true := by
  constructor <;> rfl

/-- Both signal values occur with positive probability. -/
theorem fairSignal_nondegenerate :
    some false ∈ fairSignal.support ∧ some true ∈ fairSignal.support := by
  constructor <;>
    exact FinDist.prob_pos_iff.mp
      (by norm_num [fairSignal, FinDist.prob_mix, FinDist.prob_pure_eq_ite])

theorem fairSignal_support_iff (state : Option Bool) :
    state ∈ fairSignal.support ↔ ∃ signal, state = some signal := by
  rw [← FinDist.prob_pos_iff]
  cases state with
  | none => simp [fairSignal, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  | some signal =>
      cases signal <;>
        norm_num [fairSignal, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

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
      (FinDist.mem_support_pure.mpr rfl))

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
      FinDist.pure false :=
  rfl

theorem contingentProfile_after_signal (signal : Bool)
    (realized : some signal ∈ fairSignal.support) (who : Bool) :
    contingentProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (firstHistory signal realized).trace) =
      FinDist.pure (responseActions signal who) := by
  rw [infoOf_firstHistory]
  cases who <;>
    simp [contingentProfile, constantProfile, constantFalsePolicy,
      followSignalPolicy, signalHistory, responseActions]

theorem constantProfile_initial (who : Bool) :
    constantProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (signalGame.toExecution none).initHistory.trace) =
      FinDist.pure (allFalse who) :=
  rfl

theorem contingentProfile_initial (who : Bool) :
    contingentProfile who
        ((signalGame.perfectMonitoring none).infoOf who
          (signalGame.toExecution none).initHistory.trace) =
      FinDist.pure (allFalse who) := by
  cases who
  · show followSignalPolicy [] = FinDist.pure false
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
            (responseActions action) (FinDist.mem_support_pure.mpr rfl)) false) =
      if action = signal then 1 else 0
  simp [signalGame, firstHistory, responseActions]

private theorem secondStagePayoff
    (profile : Game.PublicProfile signalGame none) (signal action : Bool)
    (realized : some signal ∈ fairSignal.support)
    (hlaws : ∀ who,
      profile who
          ((signalGame.perfectMonitoring none).infoOf who
            (firstHistory signal realized).trace) =
        FinDist.pure (responseActions action who)) :
    expectedUtility (signalGame.horizonUtility none 2) false
        ((signalGame.perfectMonitoring none).runBehavioralFrom
          (Game.toBehaviorProfile signalGame none profile) 1
          (firstHistory signal realized)) =
      if action = signal then 1 else 0 := by
  rw [Game.runBehavioralFrom_succ_toBehaviorProfile signalGame none profile 0
    (firstHistory signal realized)]
  simp_rw [hlaws]
  simp only [FinDist.pi_pure, FinDist.pure_bind]
  simp only [firstHistory_state]
  show expectedUtility (signalGame.horizonUtility none 2) false
      ((FinDist.pure (some signal)).bindOnSupport fun _ targetRealized =>
        FinDist.pure
          ((firstHistory signal realized).extend
            (Game.canonicalJoint signalGame none (some signal)
              (responseActions action)).2
            (Game.canonicalRealized signalGame none targetRealized))) = _
  rw [FinDist.pure_bindOnSupport, expectedUtility_pure]
  exact historyAverageUtility_two_steps signal action realized

private def constantBranchValue : Option Bool → ℝ
  | none => 0
  | some signal => if false = signal then 1 else 0

private def contingentBranchValue : Option Bool → ℝ
  | none => 0
  | some _ => 1

/-- Ignoring the fair signal earns one half of the two-stage average payoff. -/
theorem constantProfile_payoff :
    signalGame.finiteAveragePayoff none 2
        (Game.toBehaviorProfile signalGame none constantProfile) false = 1 / 2 := by
  show expectedUtility (signalGame.horizonUtility none 2) false
      ((signalGame.perfectMonitoring none).runBehavioral
        (Game.toBehaviorProfile signalGame none constantProfile) 2) = 1 / 2
  unfold InformationModel.runBehavioral
  rw [Game.runBehavioralFrom_succ_toBehaviorProfile signalGame none constantProfile 1
    (signalGame.toExecution none).initHistory]
  simp only [constantProfile, constantFalsePolicy, FinDist.pi_pure,
    FinDist.pure_bind]
  show expectedUtility (signalGame.horizonUtility none 2) false
      (fairSignal.bindOnSupport fun state stateRealized =>
        (signalGame.perfectMonitoring none).runBehavioralFrom
          (Game.toBehaviorProfile signalGame none constantProfile) 1
          ((signalGame.toExecution none).initHistory.extend
            (Game.canonicalJoint signalGame none none allFalse).2
            (Game.canonicalRealized signalGame none stateRealized))) = 1 / 2
  unfold expectedUtility
  calc
    FinDist.expect
        (fairSignal.bindOnSupport fun state stateRealized =>
          (signalGame.perfectMonitoring none).runBehavioralFrom
            (Game.toBehaviorProfile signalGame none constantProfile) 1
            ((signalGame.toExecution none).initHistory.extend
              (Game.canonicalJoint signalGame none none allFalse).2
              (Game.canonicalRealized signalGame none stateRealized)))
        (fun history => signalGame.horizonUtility none 2 history false) =
      FinDist.expect
        (fairSignal.bindOnSupport fun state _ =>
          FinDist.pure (constantBranchValue state)) id := by
        apply FinDist.expect_bindOnSupport_congr
        intro state stateRealized
        obtain ⟨signal, rfl⟩ := (fairSignal_support_iff state).mp stateRealized
        have hbranch := secondStagePayoff constantProfile signal false stateRealized
          (fun who => by
            have hconstant :=
              constantProfile_after_signal signal stateRealized who
            cases who <;> simpa [responseActions] using hconstant)
        unfold expectedUtility at hbranch
        simpa [firstHistory, constantBranchValue] using hbranch
    _ = FinDist.expect (FinDist.map constantBranchValue fairSignal) id := by
      rw [FinDist.bindOnSupport_eq_bind]
      rfl
    _ = 1 / 2 := by
      rw [FinDist.expect_map]
      unfold fairSignal
      rw [FinDist.expect_mix]
      norm_num [constantBranchValue]

/-- Following either realized signal earns the full two-stage average payoff. -/
theorem contingentProfile_payoff :
    signalGame.finiteAveragePayoff none 2
        (Game.toBehaviorProfile signalGame none contingentProfile) false = 1 := by
  show expectedUtility (signalGame.horizonUtility none 2) false
      ((signalGame.perfectMonitoring none).runBehavioral
        (Game.toBehaviorProfile signalGame none contingentProfile) 2) = 1
  unfold InformationModel.runBehavioral
  rw [Game.runBehavioralFrom_succ_toBehaviorProfile signalGame none contingentProfile 1
    (signalGame.toExecution none).initHistory]
  have hinitial (who : Bool) :
      contingentProfile who
          ((signalGame.perfectSignals none).infoOf who
            (signalGame.toExecution none).initHistory.trace) =
        FinDist.pure (allFalse who) :=
    contingentProfile_initial who
  simp_rw [hinitial]
  simp only [FinDist.pi_pure, FinDist.pure_bind]
  show expectedUtility (signalGame.horizonUtility none 2) false
      (fairSignal.bindOnSupport fun state stateRealized =>
        (signalGame.perfectMonitoring none).runBehavioralFrom
          (Game.toBehaviorProfile signalGame none contingentProfile) 1
          ((signalGame.toExecution none).initHistory.extend
            (Game.canonicalJoint signalGame none none allFalse).2
            (Game.canonicalRealized signalGame none stateRealized))) = 1
  unfold expectedUtility
  calc
    FinDist.expect
        (fairSignal.bindOnSupport fun state stateRealized =>
          (signalGame.perfectMonitoring none).runBehavioralFrom
            (Game.toBehaviorProfile signalGame none contingentProfile) 1
            ((signalGame.toExecution none).initHistory.extend
              (Game.canonicalJoint signalGame none none allFalse).2
              (Game.canonicalRealized signalGame none stateRealized)))
        (fun history => signalGame.horizonUtility none 2 history false) =
      FinDist.expect
        (fairSignal.bindOnSupport fun state _ =>
          FinDist.pure (contingentBranchValue state)) id := by
        apply FinDist.expect_bindOnSupport_congr
        intro state stateRealized
        obtain ⟨signal, rfl⟩ := (fairSignal_support_iff state).mp stateRealized
        have hbranch := secondStagePayoff contingentProfile signal signal stateRealized
          (contingentProfile_after_signal signal stateRealized)
        unfold expectedUtility at hbranch
        simpa [firstHistory, contingentBranchValue] using hbranch
    _ = FinDist.expect (FinDist.map contingentBranchValue fairSignal) id := by
      rw [FinDist.bindOnSupport_eq_bind]
      rfl
    _ = 1 := by
      rw [FinDist.expect_map]
      unfold fairSignal
      rw [FinDist.expect_mix]
      norm_num [contingentBranchValue]

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
          (Game.toBehaviorProfile signalGame none contingentProfile) false -
        signalGame.finiteAveragePayoff none 2
          (Game.toBehaviorProfile signalGame none constantProfile) false =
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
  rw [← canonical_contingent_update, contingentProfile_payoff,
    constantProfile_payoff] at hdeviation
  norm_num at hdeviation

end GameTheory.Experimental.PostArchitecture.StochasticProofView.Hostile
