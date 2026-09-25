/-
# Counterfactual reach on canonical protocol histories

Counterfactual reach is derived from the existing behavioral history law.  A
one-step coefficient is proved to be the exact mass of a canonical history
extension, canonical history reach satisfies the corresponding continuation
equation, and full reach factors into a player's own action contribution and
the contribution of every other player and chance.

There is no alternate history carrier, runner, or probability abstraction in
this module.
-/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.HistoryPathMass
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

private def traceLastJoint? : ∀ {state : E.State}, E.Trace state →
    Option ((player : ι) → Option (E.Action player))
  | _, .start => none
  | _, .extend _ joint _ _ => some joint

private def historyLastJoint? (history : E.History) :
    Option ((player : ι) → Option (E.Action player)) :=
  traceLastJoint? history.trace

@[simp]
private theorem historyLastJoint?_extend (history : E.History)
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal history.state joint)
    {target : E.State}
    (realized : target ∈ (E.step history.state ⟨joint, isLegal⟩).support) :
    historyLastJoint? (history.extend isLegal realized) = some joint :=
  rfl

/-- A history in a behavioral run either stopped early at a terminal state or
used the entire fuel budget. This is the bounded-cut fact needed to compare a
root run with continuation values at one information depth. -/
theorem terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
    [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player) :
    ∀ (fuel : ℕ) (start target : E.History),
      target ∈ (M.runBehavioralFrom policies fuel start).support →
        E.terminal target.state ∨
          target.trace.length = start.trace.length + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target htarget
      rw [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero,
        PMF.mem_support_pure_iff] at htarget
      subst target
      exact Or.inr (by omega)
  | succ fuel ih =>
      intro start target htarget
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal policies (fuel + 1) hterm,
          PMF.mem_support_pure_iff] at htarget
        subst target
        exact Or.inl hterm
      · rw [M.runBehavioralFrom_succ_of_not_terminal policies fuel hterm,
          PMF.support_bind] at htarget
        simp only [Set.mem_iUnion] at htarget
        obtain ⟨draw, _hdraw, hinner⟩ := htarget
        rw [PMF.support_bindOnSupport] at hinner
        simp only [Set.mem_iUnion] at hinner
        obtain ⟨reached, realized, hrest⟩ := hinner
        rcases ih (start.extend draw.2 realized) target hrest with
          htargetTerminal | hlength
        · exact Or.inl htargetTerminal
        · right
          simp [ExecutionProtocol.History.extend,
            ExecutionProtocol.Trace.length] at hlength ⊢
          omega

/-- Read a certified legal joint as one information-local choice per player. -/
def choicesOfLegal {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (player : ι) : M.Choice player (M.infoOf player trace) :=
  ⟨joint.1 player, (M.menu_adequate player trace (joint.1 player)).mpr
    (E.legalOption_of_legal joint.2 player)⟩

private def jointOfChoices {state : E.State} (trace : E.Trace state)
    (hterm : ¬ E.terminal state)
    (choices : (player : ι) → M.Choice player (M.infoOf player trace)) :
    { action : ∀ i, Option (E.Action i) // E.Legal state action } :=
  ⟨fun player => (choices player).1,
    E.legal_of_legalOption hterm fun player =>
      (M.menu_adequate player trace (choices player).1).mp
        (choices player).2⟩

private theorem jointOfChoices_injective {state : E.State}
    (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    Function.Injective (jointOfChoices M trace hterm) := by
  intro first second heq
  funext player
  apply Subtype.ext
  exact congrArg (fun joint => joint.1 player) heq

@[simp]
private theorem jointOfChoices_choicesOfLegal {state : E.State}
    (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
    jointOfChoices M trace joint.2.1
      (fun player => choicesOfLegal M trace joint player) = joint := by
  apply Subtype.ext
  rfl

/-- The canonical behavioral joint law factors into its information-local
coordinate masses. -/
theorem behavioralJoint_prob_eq_prod [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    {state : E.State} (trace : E.Trace state)
    (hterm : ¬ E.terminal state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
    ((M.behavioralJoint policies trace hterm) joint).toReal =
      ∏ player,
        ((policies player (M.infoOf player trace))
          (choicesOfLegal M trace joint player)).toReal := by
  classical
  let choices := fun player => choicesOfLegal M trace joint player
  have hbehavioral : M.behavioralJoint policies trace hterm =
      PMF.map (jointOfChoices M trace hterm)
        (independentProduct fun player =>
          policies player (M.infoOf player trace)) := by
    unfold InformationModel.behavioralJoint
    apply congrArg (fun assemble =>
      PMF.map assemble
        (independentProduct fun player =>
          policies player (M.infoOf player trace)))
    funext draws
    apply Subtype.ext
    rfl
  calc
    ((M.behavioralJoint policies trace hterm) joint).toReal =
        ((independentProduct fun player =>
          policies player (M.infoOf player trace)) choices).toReal := by
      rw [hbehavioral, ← jointOfChoices_choicesOfLegal M trace joint]
      exact congrArg ENNReal.toReal
        (pmf_map_apply_of_injective
          (independentProduct fun player =>
            policies player (M.infoOf player trace))
          (jointOfChoices_injective M trace hterm) choices)
    _ = _ := by
      rw [independentProduct_apply, ENNReal.toReal_prod]

/-- The focal player's own contribution to one selected legal joint. -/
def playerStepProb (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
    ℝ :=
  ((policies who (M.infoOf who trace))
    (choicesOfLegal M trace joint who)).toReal

/-- The other players' independent contribution to one selected legal joint. -/
def opponentsStepProb [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
  ℝ :=
  ∏ other ∈ Finset.univ.erase who,
    ((policies other (M.infoOf other trace))
      (choicesOfLegal M trace joint other)).toReal

/-- The actual probability coefficient of one joint/transition pair. -/
def stepProb [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) : ℝ :=
  ((M.behavioralJoint policies trace joint.2.1) joint).toReal *
    ((E.step state joint) target).toReal

/-- The PMF mass of an extended history factors into its joint and transition
masses in the canonical one-step continuation law. -/
private theorem runBehavioralFrom_one_apply_extend [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (joint : { action : ∀ i, Option (E.Action i) //
      E.Legal history.state action })
    (target : E.State)
    (realized : target ∈ (E.step history.state joint).support) :
    (M.runBehavioralFrom policies 1 history)
        (history.extend joint.2 realized) =
      (M.behavioralJoint policies history.trace hterm) joint *
        (E.step history.state joint) target := by
  classical
  let extended := history.extend joint.2 realized
  let jointLaw := M.behavioralJoint policies history.trace hterm
  let transition := E.step history.state joint
  let kernel := fun draw =>
    (E.step history.state draw).bindOnSupport fun reached realized' =>
      M.runBehavioralFrom policies 0 (history.extend draw.2 realized')
  have hrun : M.runBehavioralFrom policies 1 history = jointLaw.bind kernel := by
    rw [show 1 = 0 + 1 by omega,
      M.runBehavioralFrom_succ_of_not_terminal policies 0 hterm]
  have hmass : (M.runBehavioralFrom policies 1 history) extended =
      jointLaw joint * transition target := by
    rw [hrun, PMF.bind_apply]
    have hinner : kernel joint extended = transition target := by
        simp only [kernel, InformationModel.runBehavioralFrom,
          ExecutionProtocol.runRandomizedFor_zero]
        exact bindOnSupport_pure_apply_of_injective transition
          (fun reached realized' => history.extend joint.2 realized')
          (fun first _ second _ hext =>
            congrArg ExecutionProtocol.History.state hext)
          target realized
    calc
      (∑' draw, jointLaw draw * kernel draw extended) =
          jointLaw joint * kernel joint extended := by
        apply tsum_eq_single joint
        intro draw hdraw
        have hzero : kernel draw extended = 0 := by
          by_contra hnonzero
          have hmem : extended ∈ (kernel draw).support :=
            (PMF.mem_support_iff _ _).mpr hnonzero
          have hmem' : extended ∈
              ((E.step history.state draw).bindOnSupport fun reached realized' =>
                M.runBehavioralFrom policies 0
                  (history.extend draw.2 realized')).support := by
            simpa only [kernel] using hmem
          -- The support of the continuation bind exposes its realized step.
          rw [PMF.support_bindOnSupport] at hmem'
          simp only [Set.mem_iUnion] at hmem'
          obtain ⟨reached, realized', hpure⟩ := hmem'
          rw [InformationModel.runBehavioralFrom,
            ExecutionProtocol.runRandomizedFor_zero,
            PMF.mem_support_pure_iff] at hpure
          apply hdraw
          apply Subtype.ext
          have hlast := congrArg (historyLastJoint? (E := E)) hpure
          have hlast' : some joint.1 = some draw.1 := by
            simpa only [extended, historyLastJoint?_extend] using hlast
          exact Option.some.inj hlast'.symm
        simp [hzero]
      _ = jointLaw joint * transition target := by rw [hinner]
  exact hmass

/-- The step coefficient is exactly the mass of the corresponding extended
history in the canonical one-step continuation law. -/
theorem runBehavioralFrom_one_prob_extend [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal history.state action })
    (target : E.State)
    (realized : target ∈ (E.step history.state joint).support) :
    ((M.runBehavioralFrom policies 1 history)
        (history.extend joint.2 realized)).toReal =
      stepProb M policies history.trace joint target := by
  have hmass := runBehavioralFrom_one_apply_extend M policies history hterm
    joint target realized
  rw [hmass]
  simp only [stepProb, ENNReal.toReal_mul]

/-- Canonical history reach has the continuation equation: prior reach times
the exact one-step joint/transition coefficient. -/
theorem historyReachProbability_extend [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    (M.historyReachWeight policies
        ⟨target, prior.extend joint isLegal realized⟩).toReal =
      (M.historyReachWeight policies ⟨source, prior⟩).toReal *
        stepProb M policies prior ⟨joint, isLegal⟩ target := by
  classical
  let previous : E.History := ⟨source, prior⟩
  let extended : E.History :=
    ⟨target, prior.extend joint isLegal realized⟩
  have hweight : M.historyReachWeight policies extended =
      M.historyReachWeight policies previous *
        (M.runBehavioralFrom policies 1 previous) extended := by
    simp only [InformationModel.historyReachWeight, InformationModel.runBehavioral,
      InformationModel.runBehavioralFrom]
    rw [show extended.trace.length = prior.length + 1 by
      simp [extended, ExecutionProtocol.Trace.length]]
    exact E.runRandomizedFor_apply_of_trace_succ (M.randomizedChooser policies)
      prior.length E.initHistory extended (by simp [extended,
        ExecutionProtocol.Trace.length, ExecutionProtocol.initHistory])
  have hstep := runBehavioralFrom_one_apply_extend M policies previous
    isLegal.1 ⟨joint, isLegal⟩ target realized
  calc
    (M.historyReachWeight policies extended).toReal =
        (M.historyReachWeight policies previous *
          (M.runBehavioralFrom policies 1 previous) extended).toReal :=
      congrArg ENNReal.toReal hweight
    _ = (M.historyReachWeight policies previous).toReal *
          stepProb M policies prior ⟨joint, isLegal⟩ target := by
      have hstep' : (M.runBehavioralFrom policies 1 previous) extended =
          (M.behavioralJoint policies prior isLegal.1) ⟨joint, isLegal⟩ *
            (E.step source ⟨joint, isLegal⟩) target := by
        simpa [extended, previous, ExecutionProtocol.History.extend] using hstep
      rw [ENNReal.toReal_mul, hstep']
      simp only [stepProb, ENNReal.toReal_mul]

/-- Counterfactual one-step reach for `who`: every other player's action
factor together with the stochastic transition, excluding `who`'s own action
factor. -/
def counterfactualStepProb [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
  (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) : ℝ :=
  opponentsStepProb M policies who trace joint *
    ((E.step state joint) target).toReal

/-- Actual one-step reach factors into the focal player's contribution and
the counterfactual coefficient. -/
theorem stepProb_eq_player_mul_counterfactual
    [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) :
    stepProb M policies trace joint target =
      playerStepProb M policies who trace joint *
        counterfactualStepProb M policies who trace joint target := by
  classical
  rw [stepProb,
    behavioralJoint_prob_eq_prod M policies trace joint.2.1 joint]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun player =>
      ((policies player (M.infoOf player trace))
        (choicesOfLegal M trace joint player)).toReal)
    (Finset.mem_univ who)]
  simp only [playerStepProb, counterfactualStepProb, opponentsStepProb]
  ring

/-- Counterfactual one-step reach is invariant under changing only the focal
player's behavioral policy. -/
theorem counterfactualStepProb_eq_of_eq_off
    [Fintype ι] [DecidableEq ι]
    {first second : (player : ι) → M.BehavioralPolicy player}
    {who : ι} (hagree : ∀ other, other ≠ who → first other = second other)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) :
    counterfactualStepProb M first who trace joint target =
      counterfactualStepProb M second who trace joint target := by
  unfold counterfactualStepProb opponentsStepProb
  congr 1
  apply Finset.prod_congr rfl
  intro other hother
  rw [hagree other (Finset.ne_of_mem_erase hother)]

/-- Product of the focal player's own action factors along a canonical trace. -/
def playerReachProbability
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) :
    {state : E.State} → E.Trace state → ℝ
  | _, .start => 1
  | _, .extend prior joint isLegal _ =>
      playerReachProbability policies who prior *
        playerStepProb M policies who prior ⟨joint, isLegal⟩

/-- Product of all nonfocal action and transition factors along a canonical
trace. This is the finite-history counterfactual reach coefficient. -/
def counterfactualReachProbability [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) :
    {state : E.State} → E.Trace state → ℝ
  | _, .start => 1
  | target, .extend prior joint isLegal _ =>
      counterfactualReachProbability policies who prior *
        counterfactualStepProb M policies who prior ⟨joint, isLegal⟩ target

@[simp]
theorem playerReachProbability_start
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) :
    playerReachProbability M policies who
      (ExecutionProtocol.Trace.start : E.Trace E.init) = 1 :=
  rfl

@[simp]
theorem counterfactualReachProbability_start [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι) :
    counterfactualReachProbability M policies who
      (ExecutionProtocol.Trace.start : E.Trace E.init) = 1 :=
  rfl

/-- Full counterfactual reach, not merely its last step, is unchanged when
only the focal behavioral policy changes. -/
theorem counterfactualReachProbability_eq_of_eq_off
    [Fintype ι] [DecidableEq ι]
    {first second : (player : ι) → M.BehavioralPolicy player}
    {who : ι} (hagree : ∀ other, other ≠ who → first other = second other)
    {state : E.State} (trace : E.Trace state) :
    counterfactualReachProbability M first who trace =
      counterfactualReachProbability M second who trace := by
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      rw [counterfactualReachProbability, counterfactualReachProbability, ih,
        counterfactualStepProb_eq_of_eq_off M hagree]

/-- Canonical behavioral history reach factors into the focal player's own
reach and the counterfactual reach used by continuation and regret analyses. -/
theorem historyReachProbability_eq_player_mul_counterfactual
    [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    (M.historyReachWeight policies ⟨state, trace⟩).toReal =
      playerReachProbability M policies who trace *
        counterfactualReachProbability M policies who trace := by
  classical
  induction trace with
  | start =>
      rw [playerReachProbability_start, counterfactualReachProbability_start,
        one_mul]
      simp [InformationModel.historyReachWeight, InformationModel.runBehavioral,
        InformationModel.runBehavioralFrom, ExecutionProtocol.Trace.length,
        ExecutionProtocol.initHistory]
  | @extend source target prior joint isLegal realized ih =>
      rw [historyReachProbability_extend M policies prior joint isLegal realized,
        playerReachProbability, counterfactualReachProbability,
        stepProb_eq_player_mul_counterfactual M policies who, ih]
      ring

/-- Probability of an own-action record under one behavioral policy. Inactive
steps are absent because their only legal choice has probability one. -/
def ownPlayReachProbability {who : ι} (policy : M.BehavioralPolicy who) :
    List (M.InfoState who × E.Action who) → ℝ
  | [] => 1
  | (info, action) :: prior =>
      ((PMF.map (fun choice => choice.1) (policy info)) (some action)).toReal *
        ownPlayReachProbability policy prior

private theorem playerStepProb_eq_one_of_none
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (hchoice : joint.1 who = none) :
    M.playerStepProb strategy who trace joint = 1 := by
  classical
  have hinactive : ¬ E.active state who := by
    have hlegal := E.legalOption_of_legal joint.2 who
    simpa [hchoice, LegalOption] using hlegal
  let : Subsingleton (M.Choice who (M.infoOf who trace)) :=
    ⟨fun first second => by
      apply Subtype.ext
      have hfirst := (M.menu_adequate who trace first.1).mp first.2
      have hsecond := (M.menu_adequate who trace second.1).mp second.2
      rw [LegalOption.eq_none_of_inactive first.1 hfirst hinactive,
        LegalOption.eq_none_of_inactive second.1 hsecond hinactive]⟩
  unfold playerStepProb
  rw [eq_pure_of_subsingleton (strategy who (M.infoOf who trace))
    (M.choicesOfLegal trace joint who)]
  simp

/-- The recursive focal reach is exactly the probability of the canonical
own-action record. Consequently it ignores chance, opponents, and forced
inactive coordinates. -/
theorem playerReachProbability_eq_ownPlayReachProbability
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability strategy who trace =
      ownPlayReachProbability M (strategy who) (M.ownPlay who trace) := by
  classical
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      show
        M.playerReachProbability strategy who prior *
            M.playerStepProb strategy who prior ⟨joint, isLegal⟩ =
          ownPlayReachProbability M (strategy who)
            (M.ownPlay who (prior.extend joint isLegal realized))
      rw [InfoSignals.ownPlay_extend, ih]
      cases hchoice : joint who with
      | none =>
          rw [playerStepProb_eq_one_of_none M strategy who prior
            ⟨joint, isLegal⟩ hchoice, mul_one]
      | some action =>
          rw [ownPlayReachProbability]
          have hstep :
              M.playerStepProb strategy who prior ⟨joint, isLegal⟩ =
                ((PMF.map (fun choice => choice.1)
                  (strategy who (M.infoOf who prior))) (some action)).toReal := by
            have hvalue :
                (M.choicesOfLegal prior ⟨joint, isLegal⟩ who).1 =
                  some action := by
              simp [choicesOfLegal, hchoice]
            have hmass := pmf_map_apply_of_injective
              (f := fun choice : M.Choice who (M.infoOf who prior) => choice.1)
              (strategy who (M.infoOf who prior)) Subtype.val_injective
              (M.choicesOfLegal prior ⟨joint, isLegal⟩ who)
            rw [hvalue] at hmass
            unfold playerStepProb
            exact congrArg ENNReal.toReal hmass.symm
          rw [hstep]
          exact mul_comm _ _

/-- Perfect recall discharges the common-own-reach premise used by the
counterfactual/Bayes normalization theorem. -/
theorem playerReachProbability_eq_of_perfectRecall
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {firstState secondState : E.State}
    (first : E.Trace firstState) (second : E.Trace secondState)
    (hinfo : M.infoOf who first = M.infoOf who second) :
    M.playerReachProbability strategy who first =
      M.playerReachProbability strategy who second := by
  rw [playerReachProbability_eq_ownPlayReachProbability M,
    playerReachProbability_eq_ownPlayReachProbability M,
    hrecall who first second hinfo]

/-- Counterfactual reach is nonnegative because every recursive factor is a
finite product of distribution masses. -/
theorem counterfactualReachProbability_nonneg
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    0 ≤ M.counterfactualReachProbability strategy who trace := by
  classical
  induction trace with
  | start => norm_num [counterfactualReachProbability]
  | @extend source target prior joint isLegal realized ih =>
      rw [counterfactualReachProbability]
      apply mul_nonneg ih
      unfold counterfactualStepProb opponentsStepProb
      apply mul_nonneg
      · exact Finset.prod_nonneg fun other _ => ENNReal.toReal_nonneg
      · exact ENNReal.toReal_nonneg

end InformationModel

end GameTheory.Protocol
