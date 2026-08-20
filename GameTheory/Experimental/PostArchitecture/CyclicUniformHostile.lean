/-
# EXP-114: hostile cyclic uniformity slice

This file is the falsification fixture for the all-phase interface.  The
controller can switch the state on, while the target can only score after that
switch; the constant-false profile is therefore initially safe but fails after
the reachable one-step phase.
-/

import GameTheory.Experimental.PostArchitecture.CyclicUniformInterface

noncomputable section

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability
open GameTheory.Protocol.InformationModel
open GameTheory.Protocol.ExecutionProtocol

@[reducible]
def hostileGame : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition state joint := FinDist.pure (if state then true else joint false)
  stageUtility state joint who :=
    if who then if state ∧ joint true then 2 else 0 else 0

local instance hostileActionNonempty : ∀ i, Nonempty (hostileGame.Action i) :=
  fun _ => ⟨false⟩

def constantFalsePublicProfile : hostileGame.PublicProfile false :=
  fun _ _ => FinDist.pure false

def constantFalseProfile : hostileGame.BehaviorProfile false :=
  hostileGame.toBehaviorProfile false constantFalsePublicProfile

def falseChoice (initial : Bool) (i : Bool)
    (info : (hostileGame.perfectMonitoring initial).InfoState i) :
    (hostileGame.perfectMonitoring initial).Choice i info :=
  ⟨some false, by simp [Game.activeMenu]⟩

theorem constantFalseProfile_apply
    (i : Bool) (info : (hostileGame.perfectMonitoring false).InfoState i) :
    (hostileGame.toBehaviorProfile false constantFalsePublicProfile) i info =
      FinDist.pure (falseChoice false i info) := by
  rw [Game.toBehaviorProfile, Game.toBehavioralPolicy,
    constantFalsePublicProfile, FinDist.map_pure]
  apply congrArg FinDist.pure
  apply Subtype.ext
  rfl

theorem hostile_transition_support (state action : Bool) :
    (if state then true else action) ∈
      (hostileGame.transition state (fun _ => action)).support := by
  simp [hostileGame]

theorem hostile_stageRecord_boundary
    (initial : Bool) (event : (hostileGame.toExecution initial).StepEvent) :
    event.joint = fun i =>
        some ((hostileGame.stageRecordOfEvent initial event).joint i) := by
  exact Game.event_joint_eq_some_stageRecordOfEvent_joint
    hostileGame initial event

theorem hostile_stageRecord_target_boundary
    (initial : Bool) (event : (hostileGame.toExecution initial).StepEvent) :
    (hostileGame.stageRecordOfEvent initial event).target ∈
      (hostileGame.transition
        (hostileGame.stageRecordOfEvent initial event).source
        (hostileGame.stageRecordOfEvent initial event).joint).support := by
  exact Game.stageRecordOfEvent_target_mem_transition_support
    hostileGame initial event

theorem behavioralJoint_coord_eq_false
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    (owner : Bool) {state : Bool}
    (trace : (hostileGame.toExecution initial).Trace state)
    (hterm : ¬ (hostileGame.toExecution initial).terminal state)
    (hpolicy : ∀ info,
      policies owner info = FinDist.pure (falseChoice initial owner info))
    {draw : {joint : (i : Bool) → Option Bool //
      (hostileGame.toExecution initial).Legal state joint}}
    (hdraw : draw ∈ ((hostileGame.perfectMonitoring initial).behavioralJoint
      policies trace hterm).support) :
    draw.1 owner = some false := by
  rw [behavioralJoint, FinDist.support_map] at hdraw
  obtain ⟨draws, hdraws, hdraw⟩ := hdraw
  have hcoord := FinDist.mem_support_pi.mp hdraws owner
  rw [hpolicy] at hcoord
  rw [FinDist.mem_support_pure] at hcoord
  rw [← hdraw]
  have hcoord' := congrArg (fun choice => choice.1) hcoord
  have hfalse :
      (falseChoice initial owner
        ((hostileGame.perfectMonitoring initial).infoOf owner trace)).1 =
        some false := rfl
  rw [hfalse] at hcoord'
  simpa using hcoord'

theorem shifted_constantFalse_apply (restart : Bool)
    (observed : hostileGame.PublicHistory) (i : Bool)
    (continuation : hostileGame.PublicHistory) :
    (hostileGame.afterPublicHistory (restart := restart)
      constantFalseProfile observed) i continuation =
      FinDist.pure (falseChoice restart i continuation) := by
  unfold Game.afterPublicHistory
  unfold constantFalseProfile
  rw [Game.toBehaviorProfile, Game.toBehavioralPolicy,
    constantFalsePublicProfile, FinDist.map_pure]
  apply congrArg FinDist.pure
  apply Subtype.ext
  rfl

theorem run_support_state_false
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    (hcontroller : ∀ info,
      policies false info = FinDist.pure (falseChoice initial false info)) :
    ∀ (fuel : ℕ) (start result : (hostileGame.toExecution initial).History),
      start.state = false →
      result ∈ ((hostileGame.perfectMonitoring initial).runBehavioralFrom
          policies fuel start).support →
      result.state = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start result hstart hresult
      rw [runBehavioralFrom,
        runRandomizedFor_zero,
        FinDist.mem_support_pure] at hresult
      subst result
      exact hstart
  | succ fuel ih =>
      intro start result hstart hresult
      rw [runBehavioralFrom_succ_of_not_terminal
        (hostileGame.perfectMonitoring initial) policies fuel (by simp)] at hresult
      rw [FinDist.support_bind] at hresult
      obtain ⟨draw, hdraw, hresult⟩ := Set.mem_iUnion₂.mp hresult
      rw [FinDist.support_bindOnSupport] at hresult
      obtain ⟨target, realized, hresult⟩ := Set.mem_iUnion₂.mp hresult
      have hdrawFalse := behavioralJoint_coord_eq_false
        initial policies false start.trace (by simp) hcontroller hdraw
      let hevent : (hostileGame.toExecution initial).StepEvent :=
        { source := start.state
          joint := draw.1
          isLegal := draw.2
          target := target
          realized := realized }
      have hnative := hostile_stageRecord_target_boundary initial hevent
      have hjoint := hostile_stageRecord_boundary initial hevent
      have hrecord :
          (hostileGame.stageRecordOfEvent initial hevent).joint false = false := by
        have hcoord := congrFun hjoint false
        dsimp [hevent] at hcoord
        rw [hdrawFalse] at hcoord
        exact (Option.some.inj hcoord).symm
      have hsource : hevent.source = false := by
        simpa [hevent] using hstart
      have hrecord' :
          (hostileGame.stageRecordOfEvent initial
            { source := start.state
              joint := draw.1
              isLegal := draw.2
              target := target
              realized := realized }).joint false = false := by
        simpa [hevent] using hrecord
      have htarget : target = false := by
        have hnative' := hnative
        have hnative'' : target ∈
            (hostileGame.transition start.state
              (hostileGame.stageRecordOfEvent initial
                { source := start.state
                  joint := draw.1
                  isLegal := draw.2
                  target := target
                  realized := realized }).joint).support := by
          simpa using hnative'
        clear hnative'
        have hnative' := hnative''
        simp only [hostileGame] at hnative'
        rw [hrecord'] at hnative'
        simpa [hostileGame, hstart] using hnative'
      have hprior := ih (start.extend draw.2 realized) result
        (by simp [History.extend, htarget]) hresult
      exact hprior

theorem trace_valueSum_zero (initial who : Bool) :
    ∀ {state : Bool}
      (trace : (hostileGame.toExecution initial).Trace state),
      state = false →
      trace.valueSum (fun event =>
        hostileGame.eventUtility initial event who) = 0
  | _, .start, _ => rfl
  | state, .extend (source := source) prior joint isLegal realized, htarget => by
      let target := state
      let event : (hostileGame.toExecution initial).StepEvent :=
        { source := _
          joint := joint
          isLegal := isLegal
          target := _
          realized := realized }
      have hnative := hostile_stageRecord_target_boundary initial event
      have hsource : source = false := by
        by_cases hsource : source = false
        · exact hsource
        · have hsource' : source = true := Bool.eq_true_of_not_eq_false hsource
          have hbad : target = true := by
            simpa [event, hostileGame, hsource'] using hnative
          exact False.elim (by
            have hbad' : state = true := by simpa [target] using hbad
            rw [htarget] at hbad'
            cases hbad')
      simp only [Trace.valueSum_extend]
      rw [trace_valueSum_zero initial who prior hsource]
      simp [eventUtility, hostileGame, hsource]

theorem finiteAveragePayoff_zero_of_controllerFalse
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring false).BehavioralPolicy i)
    (hcontroller : ∀ info,
      policies false info = FinDist.pure (falseChoice false false info))
    (horizon : ℕ) :
    hostileGame.finiteAveragePayoff false horizon policies true = 0 := by
  rw [Game.finiteAveragePayoff, Game.horizonForm_play]
  unfold expectedUtility
  rw [FinDist.expect_eq_sum_support]
  apply Finset.sum_eq_zero
  intro history hhistory
  have hhistory' : history ∈
      ((hostileGame.perfectMonitoring false).runBehavioral policies horizon).support := by
    simpa [runBehavioral] using hhistory
  have hstate := run_support_state_false false policies hcontroller
    horizon (hostileGame.toExecution false).initHistory history (by rfl) hhistory'
  have hsum := trace_valueSum_zero false true history.trace hstate
  have hsum' : history.valueSum (fun event =>
      hostileGame.eventUtility false event true) = 0 := by
    simpa [History.valueSum] using hsum
  clear hsum
  unfold Game.horizonUtility Game.historyAverageUtility
  rw [hsum']
  simp

theorem trace_controller_valueSum_zero (initial : Bool) :
    ∀ {state : Bool}
      (trace : (hostileGame.toExecution initial).Trace state),
      trace.valueSum (fun event =>
        hostileGame.eventUtility initial event false) = 0
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      simp only [Trace.valueSum_extend]
      rw [trace_controller_valueSum_zero initial prior]
      simp [eventUtility]

theorem finiteAveragePayoff_controller_zero
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    (horizon : ℕ) :
    hostileGame.finiteAveragePayoff initial horizon policies false = 0 := by
  rw [Game.finiteAveragePayoff, Game.horizonForm_play]
  unfold expectedUtility
  rw [FinDist.expect_eq_sum_support]
  apply Finset.sum_eq_zero
  intro history _
  have hsum := trace_controller_valueSum_zero initial history.trace
  have hsum' : history.valueSum (fun event =>
      hostileGame.eventUtility initial event false) = 0 := by
    simpa [History.valueSum] using hsum
  unfold Game.horizonUtility Game.historyAverageUtility
  rw [hsum']
  simp

theorem updated_controller_constantFalse
    (replacement :
      (hostileGame.perfectMonitoring false).BehavioralPolicy true)
    (info : (hostileGame.perfectMonitoring false).InfoState false) :
    (Profile.update constantFalseProfile true replacement) false info =
      FinDist.pure (falseChoice false false info) := by
  rw [Profile.update_of_ne _ _ (by decide)]
  exact constantFalseProfile_apply false info

theorem constantFalse_initial_uniform :
    hostileGame.IsUniformεEquilibrium false 0 constantFalseProfile := by
  unfold IsUniformεEquilibrium Math.EventuallyAtAll
  refine ⟨0, fun horizon _ => ?_⟩
  show hostileGame.IsεHorizonNash false horizon 0 constantFalseProfile
  rw [hostileGame.isεHorizonNash_iff]
  intro who replacement
  cases who with
  | false =>
      rw [finiteAveragePayoff_controller_zero,
        finiteAveragePayoff_controller_zero]
      norm_num

  | true =>
      have hbase := finiteAveragePayoff_zero_of_controllerFalse
        constantFalseProfile (fun info =>
          constantFalseProfile_apply false info) horizon
      have hdev := finiteAveragePayoff_zero_of_controllerFalse
        (Profile.update constantFalseProfile true replacement)
        (updated_controller_constantFalse replacement) horizon
      rw [hbase, hdev]
      norm_num

def traceTargetFalse (initial : Bool) :
    {state : Bool} → (hostileGame.toExecution initial).Trace state → Prop
  | _, .start => True
  | _, .extend prior joint _ _ =>
      traceTargetFalse initial prior ∧ joint true = some false

theorem run_support_traceTargetFalse
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    (htarget : ∀ info,
      policies true info = FinDist.pure (falseChoice initial true info)) :
    ∀ (fuel : ℕ) (start result : (hostileGame.toExecution initial).History),
      traceTargetFalse initial start.trace →
      result ∈ ((hostileGame.perfectMonitoring initial).runBehavioralFrom
        policies fuel start).support →
      traceTargetFalse initial result.trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro start result hstart hmem
      rw [runBehavioralFrom, runRandomizedFor_zero,
        FinDist.mem_support_pure] at hmem
      subst result
      exact hstart
  | succ fuel ih =>
      intro start result hstart hmem
      rw [runBehavioralFrom_succ_of_not_terminal
        (hostileGame.perfectMonitoring initial) policies fuel (by simp)] at hmem
      rw [FinDist.support_bind] at hmem
      obtain ⟨draw, hdraw, hmem⟩ := Set.mem_iUnion₂.mp hmem
      rw [FinDist.support_bindOnSupport] at hmem
      obtain ⟨target, realized, hmem⟩ := Set.mem_iUnion₂.mp hmem
      have hdrawFalse := behavioralJoint_coord_eq_false
        initial policies true start.trace (by simp) htarget hdraw
      have hstart' : traceTargetFalse initial
          (start.extend draw.2 realized).trace :=
        ⟨hstart, hdrawFalse⟩
      exact ih (start.extend draw.2 realized) result hstart' hmem

theorem trace_valueSum_zero_of_targetFalse (initial : Bool) :
    ∀ {state : Bool}
      (trace : (hostileGame.toExecution initial).Trace state),
      traceTargetFalse initial trace →
      trace.valueSum (fun event =>
        hostileGame.eventUtility initial event true) = 0
  | _, .start, _ => rfl
  | _, .extend prior joint isLegal realized, htrace => by
      let event : (hostileGame.toExecution initial).StepEvent :=
        { source := _
          joint := joint
          isLegal := isLegal
          target := _
          realized := realized }
      have htrace' : traceTargetFalse initial prior ∧
          joint true = some false := by
        simpa [traceTargetFalse] using htrace
      have hjoint := hostile_stageRecord_boundary initial event
      have hcoord := congrFun hjoint true
      have hraw := htrace'.2
      have hrecord :
          (hostileGame.stageRecordOfEvent initial event).joint true = false := by
        dsimp [event] at hcoord
        rw [hraw] at hcoord
        exact (Option.some.inj hcoord).symm
      simp only [Trace.valueSum_extend]
      rw [trace_valueSum_zero_of_targetFalse initial prior htrace'.1]
      simp [eventUtility, hostileGame, event, hrecord]

theorem finiteAveragePayoff_zero_of_targetFalse
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    (htarget : ∀ info,
      policies true info = FinDist.pure (falseChoice initial true info))
    (horizon : ℕ) :
    hostileGame.finiteAveragePayoff initial horizon policies true = 0 := by
  rw [Game.finiteAveragePayoff, Game.horizonForm_play]
  unfold expectedUtility
  rw [FinDist.expect_eq_sum_support]
  apply Finset.sum_eq_zero
  intro history hhistory
  have hhistory' : history ∈
      ((hostileGame.perfectMonitoring initial).runBehavioral policies horizon).support := by
    simpa [runBehavioral] using hhistory
  have htrace := run_support_traceTargetFalse initial policies htarget horizon
    (hostileGame.toExecution initial).initHistory history (by trivial) hhistory'
  have hsum := trace_valueSum_zero_of_targetFalse initial history.trace htrace
  have hsum' : history.valueSum (fun event =>
      hostileGame.eventUtility initial event true) = 0 := by
    simpa [History.valueSum] using hsum
  unfold Game.horizonUtility Game.historyAverageUtility
  rw [hsum']
  simp

def offPhaseActions : ∀ i : Bool, hostileGame.Action i :=
  fun i => if i then false else true

def trueChoice (initial : Bool) (i : Bool)
    (info : (hostileGame.perfectMonitoring initial).InfoState i) :
    (hostileGame.perfectMonitoring initial).Choice i info :=
  ⟨some true, by simp [Game.activeMenu]⟩

def constantTruePolicy (initial : Bool) :
    (hostileGame.perfectMonitoring initial).BehavioralPolicy true :=
  fun info => FinDist.pure (trueChoice initial true info)

theorem behavioralJoint_coord_eq_true
    (initial : Bool)
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring initial).BehavioralPolicy i)
    {state : Bool} (trace : (hostileGame.toExecution initial).Trace state)
    (hterm : ¬ (hostileGame.toExecution initial).terminal state)
    (hpolicy : ∀ info,
      policies true info = FinDist.pure (trueChoice initial true info))
    {draw : {joint : (i : Bool) → Option Bool //
      (hostileGame.toExecution initial).Legal state joint}}
    (hdraw : draw ∈
      ((hostileGame.perfectMonitoring initial).behavioralJoint
        policies trace hterm).support) :
    draw.1 true = some true := by
  rw [behavioralJoint, FinDist.support_map] at hdraw
  obtain ⟨draws, hdraws, hdraw⟩ := hdraw
  have hcoord := FinDist.mem_support_pi.mp hdraws true
  rw [hpolicy] at hcoord
  rw [FinDist.mem_support_pure] at hcoord
  rw [← hdraw]
  have hcoord' := congrArg (fun choice => choice.1) hcoord
  have htrue :
      (trueChoice initial true
        ((hostileGame.perfectMonitoring initial).infoOf true trace)).1 =
        some true := rfl
  rw [htrue] at hcoord'
  simpa using hcoord'

def offPhaseHistory : (hostileGame.toExecution false).History :=
  let realized : true ∈
      (hostileGame.transition false offPhaseActions).support := by
    simp [hostileGame, offPhaseActions]
  (hostileGame.toExecution false).initHistory.extend
    (hostileGame.canonicalJoint false false offPhaseActions).2
    (hostileGame.canonicalRealized false realized)

theorem offPhaseHistory_state : offPhaseHistory.state = true := by
  simp [offPhaseHistory, hostileGame]

def traceTrue :
    {state : Bool} → (hostileGame.toExecution true).Trace state → Prop
  | _, .start => True
  | _, .extend prior joint _ _ =>
      traceTrue prior ∧ joint false = some false ∧ joint true = some true

theorem run_support_traceTrue
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring true).BehavioralPolicy i)
    (hcontroller : ∀ info,
      policies false info = FinDist.pure (falseChoice true false info))
    (htarget : ∀ info,
      policies true info = FinDist.pure (trueChoice true true info)) :
    ∀ (fuel : ℕ) (start result : (hostileGame.toExecution true).History),
      traceTrue start.trace →
      result ∈ ((hostileGame.perfectMonitoring true).runBehavioralFrom
        policies fuel start).support →
      traceTrue result.trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro start result htrace hmem
      rw [runBehavioralFrom, runRandomizedFor_zero,
        FinDist.mem_support_pure] at hmem
      subst result
      exact htrace
  | succ fuel ih =>
      intro start result htrace hmem
      rw [runBehavioralFrom_succ_of_not_terminal
        (hostileGame.perfectMonitoring true) policies fuel (by simp)] at hmem
      rw [FinDist.support_bind] at hmem
      obtain ⟨draw, hdraw, hmem⟩ := Set.mem_iUnion₂.mp hmem
      rw [FinDist.support_bindOnSupport] at hmem
      obtain ⟨target, realized, hmem⟩ := Set.mem_iUnion₂.mp hmem
      have hfalse := behavioralJoint_coord_eq_false
        true policies false start.trace (by simp) hcontroller hdraw
      have htrue := behavioralJoint_coord_eq_true
        true policies start.trace (by simp) htarget hdraw
      have htrace' : traceTrue (start.extend draw.2 realized).trace :=
        ⟨htrace, hfalse, htrue⟩
      exact ih (start.extend draw.2 realized) result htrace' hmem

theorem trace_state_true :
    ∀ {state : Bool} (_trace : (hostileGame.toExecution true).Trace state),
      state = true
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      have hsource := trace_state_true prior
      let event : (hostileGame.toExecution true).StepEvent :=
        { source := _
          joint := joint
          isLegal := isLegal
          target := _
          realized := realized }
      have htarget := hostile_stageRecord_target_boundary true event
      simpa [event, hostileGame, hsource] using htarget

theorem trace_valueSum_two_of_traceTrue :
    ∀ {state : Bool}
      (trace : (hostileGame.toExecution true).Trace state),
      traceTrue trace →
      trace.valueSum (fun event =>
        hostileGame.eventUtility true event true) = 2 * trace.length
  | _, .start, _ => by simp [Trace.length]
  | _, .extend prior joint isLegal realized, htrace => by
      let event : (hostileGame.toExecution true).StepEvent :=
        { source := _
          joint := joint
          isLegal := isLegal
          target := _
          realized := realized }
      have htrace' : traceTrue prior ∧
          joint false = some false ∧ joint true = some true := by
        simpa [traceTrue] using htrace
      have hjoint := hostile_stageRecord_boundary true event
      have hcoord := congrFun hjoint true
      have hrecord :
          (hostileGame.stageRecordOfEvent true event).joint true = true := by
        dsimp [event] at hcoord
        rw [htrace'.2.2] at hcoord
        exact (Option.some.inj hcoord).symm
      have hsource := trace_state_true prior
      have hevent : hostileGame.eventUtility true event true = 2 := by
        simp only [eventUtility, hostileGame]
        dsimp only [event] at hrecord ⊢
        rw [if_pos True.intro, if_pos ⟨hsource, hrecord⟩]
      have hevent' : hostileGame.eventUtility true
          { source := _
            joint := joint
            isLegal := isLegal
            target := _
            realized := realized } true = 2 := by
        simpa [event] using hevent
      simp only [Trace.valueSum_extend, Trace.length]
      rw [trace_valueSum_two_of_traceTrue prior htrace'.1]
      rw [hevent']
      norm_num
      ring

theorem finiteAveragePayoff_two
    (policies : (i : Bool) →
      (hostileGame.perfectMonitoring true).BehavioralPolicy i)
    (hcontroller : ∀ info,
      policies false info = FinDist.pure (falseChoice true false info))
    (htarget : ∀ info,
      policies true info = FinDist.pure (trueChoice true true info))
    (horizon : ℕ) (hpositive : 0 < horizon) :
    hostileGame.finiteAveragePayoff true horizon policies true = 2 := by
  rw [Game.finiteAveragePayoff, Game.horizonForm_play]
  unfold expectedUtility
  rw [FinDist.expect_eq_sum_support]
  calc
    _ = ∑ history ∈
        ((hostileGame.perfectMonitoring true).runBehavioral
          policies horizon).supportFinset,
          (((hostileGame.perfectMonitoring true).runBehavioral
            policies horizon).prob history) * 2 := by
      apply Finset.sum_congr rfl
      intro history hhistory
      have hhistorySupport : history ∈
          ((hostileGame.perfectMonitoring true).runBehavioral
            policies horizon).support :=
        FinDist.mem_supportFinset.mp hhistory
      have htrace := run_support_traceTrue policies hcontroller htarget
        horizon (hostileGame.toExecution true).initHistory history
        (by trivial) (by simpa [runBehavioral] using hhistorySupport)
      have hsum := trace_valueSum_two_of_traceTrue history.trace htrace
      have hsum' : history.valueSum (fun event =>
          hostileGame.eventUtility true event true) =
          2 * history.trace.length := by
        simpa [History.valueSum] using hsum
      have hlength :=
        trace_length_eq_of_mem_support_runRandomizedFor
          ((hostileGame.perfectMonitoring true).randomizedChooser policies)
          (fun _ => by simp) horizon
          (hostileGame.toExecution true).initHistory history
          (by simpa [runBehavioral, runBehavioralFrom] using hhistorySupport)
      unfold Game.horizonUtility Game.historyAverageUtility
      rw [hsum']
      have hlength' : history.trace.length = horizon := by
        simpa [initHistory, Trace.length] using hlength
      rw [hlength']
      have hhorizon : (horizon : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hpositive
      field_simp [hhorizon]
    _ = 2 := by
      rw [← FinDist.expect_eq_sum_support]
      exact FinDist.expect_const _ 2

def offPhaseObserved : hostileGame.PublicHistory :=
  hostileGame.publicHistoryOfTrace false offPhaseHistory.trace

def offPhaseContinuation : hostileGame.BehaviorProfile true :=
  hostileGame.afterPublicHistory (restart := true)
    constantFalseProfile offPhaseObserved

theorem offPhaseContinuation_apply (i : Bool)
    (info : (hostileGame.perfectMonitoring true).InfoState i) :
    offPhaseContinuation i info =
      FinDist.pure (falseChoice true i info) := by
  exact shifted_constantFalse_apply true offPhaseObserved i info

theorem updated_offPhase_controller_false
    (info : (hostileGame.perfectMonitoring true).InfoState false) :
    (Profile.update offPhaseContinuation true (constantTruePolicy true))
        false info =
      FinDist.pure (falseChoice true false info) := by
  rw [Profile.update_of_ne _ _ (by decide)]
  exact offPhaseContinuation_apply false info

theorem updated_offPhase_target_true
    (info : (hostileGame.perfectMonitoring true).InfoState true) :
    (Profile.update offPhaseContinuation true (constantTruePolicy true))
        true info =
      FinDist.pure (trueChoice true true info) := by
  rw [Profile.update_same]
  rfl

theorem offPhaseContinuation_payoff_zero (horizon : ℕ) :
    hostileGame.finiteAveragePayoff true horizon
      offPhaseContinuation true = 0 := by
  exact finiteAveragePayoff_zero_of_targetFalse true offPhaseContinuation
    (fun info => offPhaseContinuation_apply true info) horizon

theorem offPhaseDeviation_payoff_two (horizon : ℕ)
    (hpositive : 0 < horizon) :
    hostileGame.finiteAveragePayoff true horizon
      (Profile.update offPhaseContinuation true (constantTruePolicy true))
      true = 2 := by
  exact finiteAveragePayoff_two
    (Profile.update offPhaseContinuation true (constantTruePolicy true))
    updated_offPhase_controller_false updated_offPhase_target_true
    horizon hpositive

theorem offPhase_not_horizonNash (horizon : ℕ) (hpositive : 0 < horizon) :
    ¬ hostileGame.IsεHorizonNash true horizon 1 offPhaseContinuation := by
  intro hnash
  have hdeviation :=
    (hostileGame.isεHorizonNash_iff true horizon 1
      offPhaseContinuation).mp hnash true (constantTruePolicy true)
  rw [offPhaseDeviation_payoff_two horizon hpositive,
    offPhaseContinuation_payoff_zero horizon] at hdeviation
  norm_num at hdeviation

theorem offPhase_not_uniform :
    ¬ hostileGame.IsUniformεEquilibrium true 1 offPhaseContinuation := by
  intro huniform
  rcases huniform with ⟨threshold, hthreshold⟩
  have hpositive : 0 < threshold + 1 := Nat.zero_lt_succ threshold
  exact offPhase_not_horizonNash (threshold + 1) hpositive
    (hthreshold (threshold + 1) (Nat.le_succ threshold))

theorem constantFalse_not_allPhase_uniform :
    ¬ hostileGame.IsAllPhaseUniformεEquilibrium false 1
      constantFalseProfile := by
  intro hallPhase
  have hoffPhase := hallPhase offPhaseHistory
  have hoffPhase' :
      hostileGame.IsUniformεEquilibrium true 1 offPhaseContinuation := by
    simpa [offPhaseContinuation, offPhaseObserved, offPhaseHistory]
      using hoffPhase
  exact offPhase_not_uniform hoffPhase'

end GameTheory.Stochastic.Game
