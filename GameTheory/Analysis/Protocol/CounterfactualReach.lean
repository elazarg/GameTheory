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

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

private theorem prob_bindOnSupport_pure_of_injective [DecidableEq α]
    [DecidableEq β] (μ : FinDist α) (f : ∀ a ∈ μ.support, β)
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b)
    (a : α) (ha : a ∈ μ.support) :
    (μ.bindOnSupport fun b hb => FinDist.pure (f b hb)).prob (f a ha) =
      μ.prob a := by
  classical
  obtain ⟨fallback, hfallback⟩ := μ.support_nonempty
  let total : α → FinDist β := fun b =>
    if hb : b ∈ μ.support then FinDist.pure (f b hb)
    else FinDist.pure (f fallback hfallback)
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
      (g := total) (fun b hb => by simp [total, hb]),
    FinDist.prob_bind]
  calc
    μ.expect (fun b => (total b).prob (f a ha)) =
        μ.expect (fun b => if a = b then 1 else 0) := by
      apply FinDist.expect_congr
      intro b hb
      simp only [total, hb, dite_true, FinDist.prob_pure_eq_ite]
      by_cases hab : a = b
      · subst b
        simp
      · have hne : f a ha ≠ f b hb := fun heq => hab (hf a ha b hb heq)
        simp [hab, hne]
    _ = μ.prob a := FinDist.expect_ite_eq μ a 1 |>.trans (mul_one _)

private def traceLastJoint? : ∀ {state : E.State}, E.Trace state →
    Option ((player : ι) → Option (E.Action player))
  | _, .start => none
  | _, .extend _ joint _ _ => some joint

private def historyLastJoint? (history : E.History) :
    Option ((player : ι) → Option (E.Action player)) :=
  traceLastJoint? history.trace

private def tracePrior? : ∀ {state : E.State}, E.Trace state → Option E.History
  | _, .start => none
  | _, .extend prior _ _ _ => some ⟨_, prior⟩

private def historyPrior? (history : E.History) : Option E.History :=
  tracePrior? history.trace

@[simp]
private theorem historyLastJoint?_extend (history : E.History)
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal history.state joint)
    {target : E.State}
    (realized : target ∈ (E.step history.state ⟨joint, isLegal⟩).support) :
    historyLastJoint? (history.extend isLegal realized) = some joint :=
  rfl

@[simp]
private theorem historyPrior?_extend (history : E.History)
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal history.state joint)
    {target : E.State}
    (realized : target ∈ (E.step history.state ⟨joint, isLegal⟩).support) :
    historyPrior? (history.extend isLegal realized) = some history :=
  rfl

private theorem reachesWithin_of_mem_support_runBehavioralFrom
    [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player) :
    ∀ (fuel : ℕ) (start target : E.History),
      target ∈ (M.runBehavioralFrom policies fuel start).support →
        E.ReachesWithin fuel start target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target htarget
      rw [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero,
        FinDist.mem_support_pure] at htarget
      subst target
      exact .refl 0 start
  | succ fuel ih =>
      intro start target htarget
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal policies (fuel + 1) hterm,
          FinDist.mem_support_pure] at htarget
        subst target
        exact .refl (fuel + 1) start
      · rw [M.runBehavioralFrom_succ_of_not_terminal policies fuel hterm,
          FinDist.support_bind] at htarget
        simp only [Set.mem_iUnion] at htarget
        obtain ⟨draw, _hdraw, hinner⟩ := htarget
        rw [FinDist.support_bindOnSupport] at hinner
        simp only [Set.mem_iUnion] at hinner
        obtain ⟨reached, realized, hrest⟩ := hinner
        exact .step draw.1 draw.2 realized
          (ih (start.extend draw.2 realized) target hrest)

private theorem trace_length_le_of_reachesWithin {fuel : ℕ}
    {start target : E.History} (hreach : E.ReachesWithin fuel start target) :
    target.trace.length ≤ start.trace.length + fuel := by
  induction hreach with
  | refl fuel history => omega
  | step joint isLegal realized rest ih =>
      simp only [ExecutionProtocol.History.extend,
        ExecutionProtocol.Trace.length] at ih
      omega

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
        FinDist.mem_support_pure] at htarget
      subst target
      exact Or.inr (by omega)
  | succ fuel ih =>
      intro start target htarget
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal policies (fuel + 1) hterm,
          FinDist.mem_support_pure] at htarget
        subst target
        exact Or.inl hterm
      · rw [M.runBehavioralFrom_succ_of_not_terminal policies fuel hterm,
          FinDist.support_bind] at htarget
        simp only [Set.mem_iUnion] at htarget
        obtain ⟨draw, _hdraw, hinner⟩ := htarget
        rw [FinDist.support_bindOnSupport] at hinner
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
    (M.behavioralJoint policies trace hterm).prob joint =
      ∏ player,
        (policies player (M.infoOf player trace)).prob
          (choicesOfLegal M trace joint player) := by
  classical
  let choices := fun player => choicesOfLegal M trace joint player
  have hbehavioral : M.behavioralJoint policies trace hterm =
      FinDist.map (jointOfChoices M trace hterm)
        (FinDist.pi fun player =>
          policies player (M.infoOf player trace)) := by
    unfold InformationModel.behavioralJoint
    apply congrArg (fun assemble =>
      FinDist.map assemble
        (FinDist.pi fun player =>
          policies player (M.infoOf player trace)))
    funext draws
    apply Subtype.ext
    rfl
  calc
    (M.behavioralJoint policies trace hterm).prob joint =
        (M.behavioralJoint policies trace hterm).prob
          (jointOfChoices M trace hterm choices) := by
      rw [jointOfChoices_choicesOfLegal M trace joint]
    _ = (FinDist.pi fun player =>
          policies player (M.infoOf player trace)).prob choices := by
      rw [hbehavioral]
      exact FinDist.prob_map_of_injective
        (jointOfChoices M trace hterm)
        (jointOfChoices_injective M trace hterm)
        (FinDist.pi fun player =>
          policies player (M.infoOf player trace)) choices
    _ = _ := FinDist.prob_pi _ _

/-- The focal player's own contribution to one selected legal joint. -/
def playerStepProb (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
    ℝ :=
  (policies who (M.infoOf who trace)).prob
    (choicesOfLegal M trace joint who)

/-- The other players' independent contribution to one selected legal joint. -/
def opponentsStepProb [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action }) :
    ℝ :=
  ∏ other ∈ Finset.univ.erase who,
    (policies other (M.infoOf other trace)).prob
      (choicesOfLegal M trace joint other)

/-- The actual probability coefficient of one joint/transition pair. -/
def stepProb [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) : ℝ :=
  (M.behavioralJoint policies trace joint.2.1).prob joint *
    (E.step state joint).prob target

/-- The step coefficient is exactly the mass of the corresponding extended
history in the canonical one-step continuation law. -/
theorem runBehavioralFrom_one_prob_extend [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (joint : { action : ∀ i, Option (E.Action i) //
      E.Legal history.state action })
    (target : E.State)
    (realized : target ∈ (E.step history.state joint).support) :
    (M.runBehavioralFrom policies 1 history).prob
        (history.extend joint.2 realized) =
      stepProb M policies history.trace joint target := by
  classical
  rw [show 1 = 0 + 1 by omega,
    M.runBehavioralFrom_succ_of_not_terminal policies 0 hterm,
    FinDist.prob_bind]
  calc
    (M.behavioralJoint policies history.trace hterm).expect
        (fun draw => ((E.step history.state draw).bindOnSupport fun reached realized' =>
          M.runBehavioralFrom policies 0 (history.extend draw.2 realized')).prob
            (history.extend joint.2 realized)) =
      (M.behavioralJoint policies history.trace hterm).expect
        (fun draw => if joint = draw then (E.step history.state joint).prob target else 0) := by
      apply FinDist.expect_congr
      intro draw hdraw
      simp only [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero]
      by_cases heq : joint = draw
      · subst draw
        rw [if_pos rfl]
        exact prob_bindOnSupport_pure_of_injective
          (E.step history.state joint)
          (fun reached realized' => history.extend joint.2 realized')
          (fun first _ second _ hext => congrArg ExecutionProtocol.History.state hext)
          target realized
      · rw [if_neg heq, FinDist.prob_eq_zero_iff]
        intro hmem
        rw [FinDist.support_bindOnSupport] at hmem
        simp only [Set.mem_iUnion] at hmem
        obtain ⟨reached, reachedRealized, hpure⟩ := hmem
        rw [FinDist.mem_support_pure] at hpure
        apply heq
        apply Subtype.ext
        have hlast := congrArg (historyLastJoint? (E := E)) hpure
        exact Option.some.inj (by simpa only [historyLastJoint?_extend] using hlast)
    _ = (M.behavioralJoint policies history.trace hterm).prob joint *
          (E.step history.state joint).prob target :=
      FinDist.expect_ite_eq _ joint _
    _ = stepProb M policies history.trace joint target := rfl

/-- Canonical history reach has the continuation equation: prior reach times
the exact one-step joint/transition coefficient. -/
theorem historyReachProbability_extend [Fintype ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    M.historyReachProbability policies
        ⟨target, prior.extend joint isLegal realized⟩ =
      M.historyReachProbability policies ⟨source, prior⟩ *
        stepProb M policies prior ⟨joint, isLegal⟩ target := by
  classical
  let previous : E.History := ⟨source, prior⟩
  let extended : E.History :=
    ⟨target, prior.extend joint isLegal realized⟩
  unfold InformationModel.historyReachProbability
  simp only [ExecutionProtocol.Trace.length]
  rw [InformationModel.runBehavioral,
    M.runBehavioralFrom_add policies prior.length 1 E.initHistory,
    FinDist.prob_bind]
  calc
    (M.runBehavioralFrom policies prior.length E.initHistory).expect
        (fun history => (M.runBehavioralFrom policies 1 history).prob extended) =
      (M.runBehavioralFrom policies prior.length E.initHistory).expect
        (fun history => if previous = history then
          stepProb M policies prior ⟨joint, isLegal⟩ target else 0) := by
      apply FinDist.expect_congr
      intro history hhistory
      by_cases heq : previous = history
      · subst history
        rw [if_pos rfl]
        exact runBehavioralFrom_one_prob_extend M policies previous
          isLegal.1 ⟨joint, isLegal⟩ target realized
      · rw [if_neg heq, FinDist.prob_eq_zero_iff]
        intro hbranch
        by_cases hterm : E.terminal history.state
        · rw [M.runBehavioralFrom_of_terminal policies 1 hterm,
            FinDist.mem_support_pure] at hbranch
          have hreach : E.ReachesWithin prior.length E.initHistory history :=
            reachesWithin_of_mem_support_runBehavioralFrom M policies
              prior.length E.initHistory history hhistory
          have hbound := trace_length_le_of_reachesWithin hreach
          have hlength := congrArg
            (fun current : E.History => current.trace.length) hbranch
          simp [extended, ExecutionProtocol.Trace.length,
            ExecutionProtocol.initHistory] at hlength hbound
          omega
        · rw [show 1 = 0 + 1 by omega,
            M.runBehavioralFrom_succ_of_not_terminal policies 0 hterm,
            FinDist.support_bind] at hbranch
          simp only [Set.mem_iUnion] at hbranch
          obtain ⟨draw, _hdraw, hinner⟩ := hbranch
          rw [FinDist.support_bindOnSupport] at hinner
          simp only [Set.mem_iUnion] at hinner
          obtain ⟨reached, reachedRealized, hrest⟩ := hinner
          rw [InformationModel.runBehavioralFrom,
            ExecutionProtocol.runRandomizedFor_zero,
            FinDist.mem_support_pure] at hrest
          apply heq
          have hprior := congrArg (historyPrior? (E := E)) hrest
          have hextended : historyPrior? extended = some previous := by
            rfl
          rw [hextended, historyPrior?_extend] at hprior
          exact Option.some.inj hprior
    _ = (M.runBehavioralFrom policies prior.length E.initHistory).prob previous *
          stepProb M policies prior ⟨joint, isLegal⟩ target :=
      FinDist.expect_ite_eq _ previous _
    _ = M.historyReachProbability policies ⟨source, prior⟩ *
          stepProb M policies prior ⟨joint, isLegal⟩ target := by
      rfl

/-- Counterfactual one-step reach for `who`: every other player's action
factor together with the stochastic transition, excluding `who`'s own action
factor. -/
def counterfactualStepProb [Fintype ι] [DecidableEq ι]
    (policies : (player : ι) → M.BehavioralPolicy player)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ i, Option (E.Action i) // E.Legal state action })
    (target : E.State) : ℝ :=
  opponentsStepProb M policies who trace joint *
    (E.step state joint).prob target

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
      (policies player (M.infoOf player trace)).prob
        (choicesOfLegal M trace joint player))
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
    M.historyReachProbability policies ⟨state, trace⟩ =
      playerReachProbability M policies who trace *
        counterfactualReachProbability M policies who trace := by
  classical
  induction trace with
  | start =>
      rw [playerReachProbability_start, counterfactualReachProbability_start,
        one_mul]
      unfold InformationModel.historyReachProbability
      simp [InformationModel.runBehavioral,
        InformationModel.runBehavioralFrom,
        ExecutionProtocol.Trace.length,
        ExecutionProtocol.initHistory]
  | @extend source target prior joint isLegal realized ih =>
      rw [historyReachProbability_extend M policies prior joint isLegal realized,
        playerReachProbability, counterfactualReachProbability,
        stepProb_eq_player_mul_counterfactual M policies who, ih]
      ring

end InformationModel

end GameTheory.Protocol
