/-
# Countably branching backward-law gate

A single chance transition has infinitely many terminal successors. The
well-founded law agrees with the forward runner; a divergent payoff leaves the
law intact but cannot be read as a finite real backward value.
-/

import GameTheory.Protocol.Backward
import GameTheory.Protocol.Zermelo
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Experimental.PostArchitecture.PMFSequentialGate

noncomputable section

namespace GameTheory.Experimental.PMFBackwardGate

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

abbrev execution : ExecutionProtocol PUnit where
  State := Option ℕ
  Action := fun _ => Unit
  init := none
  active := fun state _ => state.isNone = true
  available := fun _ _ => Set.univ
  terminal := fun state => match state with | none => False | some _ => True
  step := fun state joint =>
    match state with
    | none => geometric.map some
    | some _ => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | none =>
        refine ⟨fun _ => some (), ?_⟩
        intro i
        cases i
        simp
    | some n => exact False.elim (hterm trivial)

def rank : Option ℕ → ℕ
  | none => 1
  | some _ => 0

theorem wellFounded : execution.WellFoundedPlay := by
  apply execution.wellFoundedPlay_of_rank rank
  intro source target hsucc
  obtain ⟨joint, legal, realized⟩ := hsucc
  cases source with
  | none =>
      rw [PMF.mem_support_map_iff] at realized
      obtain ⟨n, _, rfl⟩ := realized
      simp [rank]
  | some n => exact False.elim (legal.1 trivial)

def chooser : execution.Chooser :=
  fun _state hterm =>
    ⟨Classical.choose (execution.exists_legal hterm),
      Classical.choose_spec (execution.exists_legal hterm)⟩

theorem runZero : execution.runFor chooser 0 = PMF.pure := by
  funext state
  exact execution.runFor_zero chooser state

theorem stopsWithinOne : execution.StopsWithin chooser 1 none := by
  intro reached hreach
  rw [execution.runFor_succ_of_not_terminal chooser 0 (by simp)] at hreach
  rw [runZero, PMF.bind_pure, PMF.mem_support_map_iff] at hreach
  obtain ⟨n, _, rfl⟩ := hreach
  trivial

theorem backwardLaw_eq_geometric :
    execution.backwardLaw wellFounded chooser none = geometric.map some := by
  rw [execution.backwardLaw_eq_runFor stopsWithinOne,
    execution.runFor_succ_of_not_terminal chooser 0 (by simp)]
  rw [runZero, PMF.bind_pure]

theorem backwardLaw_infiniteSupport :
    (execution.backwardLaw wellFounded chooser none).support.Infinite := by
  rw [backwardLaw_eq_geometric]
  apply (Set.infinite_range_of_injective (Option.some_injective ℕ)).mono
  rintro state ⟨n, rfl⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

def payoff : Option ℕ → ℝ
  | none => 0
  | some n => exploding n

theorem divergentPayoffRejected :
    ¬ PayoffIntegrable
      (execution.backwardLaw wellFounded chooser none) payoff := by
  rw [backwardLaw_eq_geometric]
  intro hintegrable
  have hsource :=
    (payoffIntegrable_map_iff (f := some) (p := geometric) (u := payoff)).mp
      hintegrable
  exact GameTheory.Experimental.PMFSequentialGate.exploding_not_integrable
    (by simpa [payoff, Function.comp_def] using hsource)

end GameTheory.Experimental.PMFBackwardGate

namespace GameTheory.Experimental.PMFBackwardGate.ChoiceChance

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

abbrev execution : ExecutionProtocol.{0, 0, 0} PUnit where
  State := Option (Bool × ℕ)
  Action := fun _ => Bool
  init := none
  active := fun state _ => state.isNone = true
  available := fun _ _ => Set.univ
  terminal := fun state => match state with | none => False | some _ => True
  step := fun state joint =>
    match state with
    | none => geometric.map (fun n => some ((joint.1 PUnit.unit).getD false, n))
    | some _ => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | none =>
        refine ⟨fun _ => some true, ?_⟩
        intro i
        cases i
        simp
    | some x => exact False.elim (hterm trivial)

def rank : Option (Bool × ℕ) → ℕ
  | none => 1
  | some _ => 0

theorem wellFounded : execution.WellFoundedPlay := by
  apply execution.wellFoundedPlay_of_rank rank
  intro source target hsucc
  obtain ⟨joint, legal, realized⟩ := hsucc
  cases source with
  | none =>
      rw [PMF.mem_support_map_iff] at realized
      obtain ⟨n, _, rfl⟩ := realized
      simp [rank]
  | some x => exact False.elim (legal.1 trivial)

def chooser (b : Bool) : execution.Chooser := fun state hterm =>
  match state with
  | none => ⟨fun _ => some b, by
      constructor
      · simp
      · intro i
        cases i
        simp [execution]⟩
  | some _ => False.elim (hterm trivial)

def payoff : Option (Bool × ℕ) → ℝ
  | none => 0
  | some (b, _) => if b then 1 else 0

theorem payoff_bounded (state : Option (Bool × ℕ)) : |payoff state| ≤ 1 := by
  cases state with
  | none => simp [payoff]
  | some pair => cases pair with
      | mk b n => cases b <;> simp [payoff]

theorem step_support_terminal
    (joint : { joint : ∀ i, Option (execution.Action i) //
      execution.Legal none joint })
    {target : execution.State} (htarget : target ∈ (execution.step none joint).support) :
    execution.terminal target := by
  rw [PMF.mem_support_map_iff] at htarget
  obtain ⟨n, _, rfl⟩ := htarget
  trivial

theorem contextLaw (b : Bool)
    (joint : { joint : ∀ i, Option (execution.Action i) //
      execution.Legal none joint }) :
    (execution.oneShotContext wellFounded (chooser b) payoff none (by simp)).outcome
      joint = execution.step none joint := by
  unfold ExecutionProtocol.oneShotContext
  calc
    (execution.step none joint).bind (execution.backwardLaw wellFounded (chooser b)) =
        (execution.step none joint).bind PMF.pure := by
          apply bind_congr_on_support
          intro target htarget
          exact execution.backwardLaw_of_terminal (step_support_terminal joint htarget)
    _ = execution.step none joint := PMF.bind_pure _

theorem contextValue (b : Bool)
    (joint : { joint : ∀ i, Option (execution.Action i) //
      execution.Legal none joint })
    (h : (execution.oneShotContext wellFounded (chooser b) payoff none
      (by simp)).IntegrableAt joint) :
    (execution.oneShotContext wellFounded (chooser b) payoff none
      (by simp)).value joint h =
        (if (joint.1 PUnit.unit).getD false then (1 : ℝ) else 0) := by
  let c : ℝ := if (joint.1 PUnit.unit).getD false then 1 else 0
  have hc : PayoffIntegrable (execution.step none joint) (fun _ => c) :=
    payoffIntegrable_of_bounded _ _ (C := 1) (fun _ => by
      simp only [c]
      split_ifs <;> norm_num)
  have hpoint : ∀ target ∈ (execution.step none joint).support,
      payoff target = c := by
    intro target htarget
    rw [PMF.mem_support_map_iff] at htarget
    obtain ⟨n, _, rfl⟩ := htarget
    rfl
  calc
    _ = expect (execution.step none joint) payoff (by
          rw [← contextLaw b joint]
          exact h) := by
            unfold GameTheory.Protocol.Context.value expect
            rw [contextLaw b joint]
            rfl
    _ = expect (execution.step none joint) (fun _ => c) hc := by
          apply expect_congr_on_support hpoint
    _ = c := expect_constant _ _ hc
    _ = _ := rfl

theorem payoff_le_one (state : execution.State) : payoff state ≤ 1 := by
  cases state with
  | none => simp [payoff]
  | some pair => cases pair with
      | mk b n => cases b <;> simp [payoff]

theorem optimal_oneShot :
    execution.IsOneShotOptimal wellFounded (chooser true) payoff := by
  intro state hterm
  cases state with
  | some pair => exact False.elim (hterm trivial)
  | none =>
      let ctx := execution.oneShotContext wellFounded (chooser true) payoff none hterm
      have hintegrable (joint : { joint : ∀ i, Option (execution.Action i) //
          execution.Legal none joint }) : ctx.IntegrableAt joint :=
        payoffIntegrable_of_bounded _ _ payoff_bounded
      refine ⟨hintegrable (chooser true none hterm),
        (fun joint _ => hintegrable joint), ?_⟩
      intro joint _ hinc halt
      have hconst : PayoffIntegrable (ctx.outcome joint) (fun _ => (1 : ℝ)) :=
        payoffIntegrable_of_bounded _ _ (C := 1) (fun _ => by norm_num)
      have hmax : ctx.value joint halt ≤ 1 := by
        calc
          ctx.value joint halt ≤
              expect (ctx.outcome joint) (fun _ => (1 : ℝ)) hconst := by
                unfold GameTheory.Protocol.Context.value
                apply expect_mono
                intro target _
                exact payoff_le_one target
          _ = 1 := expect_constant _ _ hconst
      have hown : ctx.value (chooser true none hterm) hinc = 1 := by
        simpa [ctx, chooser] using
          (contextValue true (chooser true none hterm) hinc)
      exact le_trans hmax hown.symm.le

theorem suboptimal_not_oneShot :
    ¬ execution.IsOneShotOptimal wellFounded (chooser false) payoff := by
  intro hbad
  let good := chooser true none (by simp)
  let ctx := execution.oneShotContext wellFounded (chooser false) payoff none
    (by simp)
  have hlocal := hbad none (by simp)
  have hinc : ctx.IntegrableAt (chooser false none (by simp)) :=
    hlocal.1
  have halt : ctx.IntegrableAt good := hlocal.2.1 good (Set.mem_univ _)
  have hle := hlocal.2.2 good (Set.mem_univ _) hinc halt
  have hgood : ctx.value good halt = 1 := by
    simpa [ctx, good, chooser] using (contextValue false good halt)
  have hfalse : ctx.value (chooser false none (by simp)) hinc = 0 := by
    simpa [ctx, chooser] using
      (contextValue false (chooser false none (by simp)) hinc)
  rw [hgood, hfalse] at hle
  norm_num at hle

theorem stopsWithinOne (b : Bool) :
    execution.StopsWithin (chooser b) 1 none := by
  intro reached hreach
  rw [execution.runFor_succ_of_not_terminal (chooser b) 0 (by simp)] at hreach
  have hzero : execution.runFor (chooser b) 0 = PMF.pure := by
    funext state
    exact execution.runFor_zero (chooser b) state
  rw [hzero, PMF.bind_pure, PMF.mem_support_map_iff] at hreach
  obtain ⟨n, _, rfl⟩ := hreach
  trivial

theorem backwardValue_choice (b : Bool) :
    execution.backwardValue wellFounded (chooser b) payoff none
      (payoffIntegrable_of_bounded _ _ payoff_bounded) =
        (if b then (1 : ℝ) else 0) := by
  let hterm : ¬ execution.terminal none := by simp
  let joint := chooser b none hterm
  have hctx :
      (execution.oneShotContext wellFounded (chooser b) payoff none hterm).IntegrableAt
        joint :=
    payoffIntegrable_of_bounded _ _ payoff_bounded
  have hval := contextValue b joint hctx
  unfold GameTheory.Protocol.Context.value at hval
  unfold expect at hval
  unfold backwardValue expect
  rw [execution.oneShotContext_incumbentLaw hterm] at hval
  simpa [joint, chooser, ExecutionProtocol.oneShotContext] using hval

theorem strict_backwardComparison :
    execution.backwardValue wellFounded (chooser false) payoff none
        (payoffIntegrable_of_bounded _ _ payoff_bounded) <
      execution.backwardValue wellFounded (chooser true) payoff none
        (payoffIntegrable_of_bounded _ _ payoff_bounded) := by
  rw [backwardValue_choice false, backwardValue_choice true]
  norm_num

theorem backwardLaw_eq_geometricChoice (b : Bool) :
    execution.backwardLaw wellFounded (chooser b) none =
      geometric.map (fun n => some (b, n)) := by
  let hterm : ¬ execution.terminal none := by simp
  calc
    execution.backwardLaw wellFounded (chooser b) none =
        (execution.oneShotContext wellFounded (chooser b) payoff none hterm).outcome
          (chooser b none hterm) :=
      (execution.oneShotContext_incumbentLaw hterm).symm
    _ = execution.step none (chooser b none hterm) := contextLaw b _
    _ = geometric.map (fun n => some (b, n)) := by simp [execution, chooser]

theorem backwardLaw_infiniteSupport (b : Bool) :
    (execution.backwardLaw wellFounded (chooser b) none).support.Infinite := by
  rw [backwardLaw_eq_geometricChoice]
  have hinj : Function.Injective (fun n : ℕ => some (b, n)) := by
    intro n m h
    exact congrArg Prod.snd (Option.some_injective _ h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro state ⟨n, rfl⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

theorem runnerOptimalAgainstBad :
    ∃ hgood : PayoffIntegrable (execution.runFor (chooser true) 1 none) payoff,
      expect (execution.runFor (chooser false) 1 none) payoff
          (payoffIntegrable_of_bounded _ _ payoff_bounded) ≤
        expect (execution.runFor (chooser true) 1 none) payoff hgood := by
  exact execution.expect_runFor_le_of_isOneShotOptimal optimal_oneShot
    (chooser false) (stopsWithinOne false) (stopsWithinOne true)
    (payoffIntegrable_of_bounded _ _ payoff_bounded)

/-- The root decision is observed directly; the infinitely many terminal
successors retain their ordinary state observations. -/
@[reducible]
def signals : InfoSignals execution where
  PublicSignal := Option (Bool × ℕ)
  PrivateSignal _ := PUnit
  initialPublic := none
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Option (Bool × ℕ)
  initInfo _ _ observation := observation
  pushInfo _ _ _ _ observation := observation

private theorem infoOf_state {state : execution.State}
    (trace : execution.Trace state) : signals.infoOf PUnit.unit trace = state := by
  cases trace <;> rfl

def menu : Option (Bool × ℕ) → Set (Option Bool)
  | none => {some false, some true}
  | some _ => {none}

@[reducible]
def information : InformationModel execution where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro _ state trace choice
    rw [infoOf_state]
    cases state with
    | none =>
        cases choice with
        | none => simp [menu, LegalOption, execution]
        | some action => cases action <;> simp [menu, LegalOption, execution]
    | some pair =>
        cases choice <;> simp [menu, LegalOption, execution]

private instance (info : information.InfoState PUnit.unit) :
    Finite (information.Choice PUnit.unit info) := by
  dsimp [InformationModel.Choice]
  infer_instance

private instance (info : information.InfoState PUnit.unit) :
    Nonempty (information.Choice PUnit.unit info) := by
  cases info with
  | none => exact ⟨⟨some true, by simp [menu]⟩⟩
  | some pair => exact ⟨⟨none, by simp [menu]⟩⟩

def fallbackProfile : Profile information.strategicSignature :=
  fun _ _ => Classical.choice inferInstance

theorem finiteDecisionChoices : information.HasFiniteDecisionChoices := by
  intro _ info _ _
  exact inferInstance

theorem singleMover (state : execution.State) {first second : PUnit}
    (_ : execution.active state first) (_ : execution.active state second) :
    first = second := by cases first; cases second; rfl

private theorem init_not_mem_step (source : execution.State)
    (joint : ∀ i, Option (execution.Action i))
    (legal : execution.Legal source joint) :
    none ∉ (execution.step source ⟨joint, legal⟩).support := by
  cases source with
  | none =>
      intro hmem
      rw [PMF.mem_support_map_iff] at hmem
      obtain ⟨n, _, hnone⟩ := hmem
      cases hnone
  | some pair => exact False.elim (legal.1 trivial)

private theorem legal_root_joint_some
    (joint : ∀ i, Option (execution.Action i))
    (legal : execution.Legal none joint) :
    ∃ action : Bool, joint PUnit.unit = some action := by
  cases haction : joint PUnit.unit with
  | none =>
      have hoption :=
        (isLegalJoint_iff_legalOption (E := execution) none joint).mp
          legal.2 PUnit.unit
      simp [LegalOption, execution, haction] at hoption
  | some action => exact ⟨action, rfl⟩

private theorem predecessor_unique
    {target firstSource secondSource : execution.State}
    {firstJoint secondJoint : ∀ i, Option (execution.Action i)}
    (firstLegal : execution.Legal firstSource firstJoint)
    (secondLegal : execution.Legal secondSource secondJoint)
    (firstRealized : target ∈
      (execution.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      (execution.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirstSource : firstSource = none := by
    cases firstSource with
    | none => rfl
    | some pair => exact False.elim (firstLegal.1 trivial)
  have hsecondSource : secondSource = none := by
    cases secondSource with
    | none => rfl
    | some pair => exact False.elim (secondLegal.1 trivial)
  subst firstSource
  subst secondSource
  obtain ⟨firstAction, hfirstAction⟩ :=
    legal_root_joint_some firstJoint firstLegal
  obtain ⟨secondAction, hsecondAction⟩ :=
    legal_root_joint_some secondJoint secondLegal
  rw [PMF.mem_support_map_iff] at firstRealized secondRealized
  obtain ⟨firstN, _, hfirstTarget⟩ := firstRealized
  obtain ⟨secondN, _, hsecondTarget⟩ := secondRealized
  have haction : firstAction = secondAction := by
    have hpair := Option.some.inj (hfirstTarget.trans hsecondTarget.symm)
    have hfirst := congrArg Prod.fst hpair
    simpa [hfirstAction, hsecondAction] using hfirst
  refine ⟨rfl, ?_⟩
  funext player
  cases player
  rw [hfirstAction, hsecondAction, haction]

theorem treeShaped : execution.IsTreeShaped :=
  execution.isTreeShaped_of_predecessor_unique init_not_mem_step
    predecessor_unique

private theorem rootHistory_unique (history : execution.History)
    (hstate : history.state = none) :
    history = (⟨none, ExecutionProtocol.Trace.start⟩ : execution.History) := by
  cases history with
  | mk state trace =>
      dsimp at hstate
      subst state
      exact congrArg (fun current : execution.Trace none =>
        (⟨none, current⟩ : execution.History))
        ((treeShaped none).elim trace ExecutionProtocol.Trace.start)

theorem perfect : information.SeparatesDecisionHistories := by
  intro _ first second _ hfirst _ hsecond _
  have hsfirst : first.state = none := by
    cases h : first.state with
    | none => rfl
    | some pair => simp [execution, h] at hfirst
  have hssecond : second.state = none := by
    cases h : second.state with
    | none => rfl
    | some pair => simp [execution, h] at hsecond
  exact (rootHistory_unique first hsfirst).trans
    (rootHistory_unique second hssecond).symm

def historyUtility (history : execution.History) (_ : PUnit) : ℝ :=
  payoff history.state

theorem backwardIntegrable (historyChooser : execution.HistoryChooser)
    (history : execution.History) (who : PUnit) :
    PayoffIntegrable
      (execution.historyBackwardLaw wellFounded historyChooser history)
      (fun outcome => historyUtility outcome who) :=
  payoffIntegrable_of_bounded _ _ (C := 1)
    (fun outcome => payoff_bounded outcome.state)

/-- Generic Zermelo backward induction applies despite every root action
having infinitely many terminal successors. -/
theorem exists_subgamePerfect :
    ∃ profile : Profile information.strategicSignature,
      information.IsSubgamePerfect wellFounded profile historyUtility :=
  information.exists_isSubgamePerfect singleMover fallbackProfile
    finiteDecisionChoices wellFounded perfect historyUtility backwardIntegrable

end GameTheory.Experimental.PMFBackwardGate.ChoiceChance
