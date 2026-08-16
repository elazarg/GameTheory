/-
# Safe and unsafe MAID observation reduction

A genuinely fair Boolean signal feeds one Boolean decision.  Removing the
signal is safe when utility rewards the action alone: the always-true reduced
profile covers every full deviation and hence remains Nash after expansion.
With the same diagram and pruning, matching the signal makes the observation
valuable.  Every signal-blind reduced policy earns one half, while the full
copying policy earns one.
-/

import GameTheory.Languages.MAID.ObservationPruning

noncomputable section

namespace GameTheory.Tests.MAIDSafeReduction

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence

inductive Node
  | signal
  | decision
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .signal => ∅
  | .decision => {.signal}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .decision]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit Node where
  kind
    | .signal => .chance
    | .decision => .decision ()
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := fun _ => id
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

def topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents :=
  topologicalParents

def fairSignal : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem fairSignal_expect (score : Bool → ℝ) :
    fairSignal.expect score = (score false + score true) / 2 := by
  rw [fairSignal, FinDist.expect_mix,
    FinDist.expect_pure, FinDist.expect_pure]
  ring

@[reducible]
def testSemantics (matchSignal : Bool) : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact fairSignal
    | decision => simp at hchance
  utility _ assignment :=
    if matchSignal
    then if assignment .decision = assignment .signal then 1 else 0
    else if assignment .decision then 1 else 0

abbrev irrelevantSemantics := testSemantics false

abbrev matchingSemantics := testSemantics true

/-- Remove the fair signal from the sole decision rule. -/
def pruning : Pruning diagram where
  kept _ := ∅
  kept_sub_observed _ := by simp

def decisionSite : DecisionSite diagram () := ⟨.decision, rfl⟩

def observedConfig (signal : Bool) :
    Config diagram (diagram.observedParents .decision) :=
  fun _ => signal

def reducedPure (value : Bool) : pruning.ReducedPolicy :=
  fun _ _ _ => FinDist.pure value

theorem pruning_kept_decision : pruning.kept decisionSite.1 = ∅ := by
  rfl

theorem node_not_mem_empty (node : Node) : node ∉ (∅ : Finset Node) := by
  simp

def fullCopySignal : Policy diagram :=
  fun _ site observed =>
    match hnode : site.1 with
    | .signal => by
        have hkind := site.2
        simp [diagram, hnode] at hkind
    | .decision =>
        FinDist.pure (observed ⟨.signal, by simp [diagram, parents, hnode]⟩)

def assignmentOf (signal action : Bool) : Assignment diagram
  | .signal => signal
  | .decision => action

theorem restrict_after_signal (matchSignal signal : Bool) :
    Assignment.restrict diagram
        (Stage.Assignment.setOne (testSemantics matchSignal).defaultValue
          ⟨.signal, signal⟩)
        (diagram.observedParents .decision) =
      observedConfig signal := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, observedConfig,
      Stage.Assignment.setOne, Assignment.resolve] at hnode ⊢

theorem set_decision_after_signal (matchSignal signal action : Bool) :
    Stage.Assignment.setOne
        (Stage.Assignment.setOne (testSemantics matchSignal).defaultValue
          ⟨.signal, signal⟩)
        ⟨.decision, action⟩ =
      assignmentOf signal action := by
  funext node
  cases node <;>
    simp [Stage.Assignment.setOne, Assignment.resolve, assignmentOf]

theorem assignmentNodeLaw_signal (matchSignal : Bool) (policy : Policy diagram)
    (assignment : Assignment diagram) :
    assignmentNodeLaw (testSemantics matchSignal) policy assignment .signal =
      fairSignal := by
  rfl

theorem assignmentNodeLaw_decision_after_signal
    (matchSignal signal : Bool) (policy : Policy diagram) :
    assignmentNodeLaw (testSemantics matchSignal) policy
        (Stage.Assignment.setOne (testSemantics matchSignal).defaultValue
          ⟨.signal, signal⟩) .decision =
      policy () decisionSite (observedConfig signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy () decisionSite)
    (restrict_after_signal matchSignal signal)

/-- The native law of any full policy is the direct fair-signal experiment. -/
theorem native_play_eq (matchSignal : Bool) (policy : Policy diagram) :
    (nativeBehavioralGameForm (testSemantics matchSignal)).play policy =
      fairSignal.bind fun signal =>
        (policy () decisionSite (observedConfig signal)).map
          (assignmentOf signal) := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological
      (testSemantics matchSignal) policy]
  change assignmentRun (testSemantics matchSignal) policy
      [.signal, .decision] (testSemantics matchSignal).defaultValue = _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_signal,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro signal _
  rw [assignmentRun, assignmentStep,
    assignmentNodeLaw_decision_after_signal,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro action _
  rw [assignmentRun]
  exact congrArg FinDist.pure
    (set_decision_after_signal matchSignal signal action)

/-- In the irrelevant-utility game, only the chosen action enters payoff. -/
theorem irrelevant_expectedUtility (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => irrelevantSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm irrelevantSemantics).play policy) =
      fairSignal.expect fun signal =>
        (policy () decisionSite (observedConfig signal)).expect fun action =>
          if action then 1 else 0 := by
  unfold expectedUtility
  rw [native_play_eq false, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _
  rw [FinDist.expect_map]
  rfl

/-- In the observation-sensitive game, payoff is the signal-match indicator. -/
theorem matching_expectedUtility (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play policy) =
      fairSignal.expect fun signal =>
        (policy () decisionSite (observedConfig signal)).expect fun action =>
          if action = signal then 1 else 0 := by
  unfold expectedUtility
  rw [native_play_eq true, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _
  rw [FinDist.expect_map]
  rfl

/-- Expanding a reduced policy cannot recover the observation that was removed. -/
theorem expanded_reduced_ignores_signal (policy : pruning.ReducedPolicy)
    (first second : Bool) :
    pruning.expandPolicy policy () decisionSite (observedConfig first) =
      pruning.expandPolicy policy () decisionSite (observedConfig second) := by
  unfold Pruning.expandPolicy Pruning.expandOwnerPolicy
  apply congrArg (policy () decisionSite)
  funext node
  have hmember : node.1 ∈ (∅ : Finset Node) := node.2
  exact (node_not_mem_empty node.1 hmember).elim

/-- The two Boolean match indicators partition probability one. -/
theorem expect_match_false_add_true (law : FinDist Bool) :
    law.expect (fun action => if action = false then 1 else 0) +
        law.expect (fun action => if action = true then 1 else 0) =
      1 := by
  rw [← FinDist.expect_add]
  calc
    law.expect (fun action =>
        (if action = false then 1 else 0) +
          (if action = true then 1 else 0)) =
        law.expect (fun _ => 1) := by
      apply FinDist.expect_congr
      intro action _
      cases action <;> norm_num
    _ = 1 := FinDist.expect_const law 1

/-- Signal-blind policies earn exactly one half when payoff rewards matching. -/
theorem matching_expanded_reduced_expectedUtility
    (policy : pruning.ReducedPolicy) :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          (pruning.expandPolicy policy)) =
      1 / 2 := by
  rw [matching_expectedUtility, fairSignal_expect,
    expanded_reduced_ignores_signal policy false true,
    expect_match_false_add_true]

/-- The always-true reduced policy receives the maximal irrelevant payoff. -/
theorem irrelevant_expanded_true_expectedUtility :
    expectedUtility
        (fun assignment owner => irrelevantSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm irrelevantSemantics).play
          (pruning.expandPolicy (reducedPure true))) =
      1 := by
  rw [irrelevant_expectedUtility, fairSignal_expect]
  norm_num [Pruning.expandPolicy, Pruning.expandOwnerPolicy, reducedPure]

/-- No full policy can exceed the maximal irrelevant payoff. -/
theorem irrelevant_expectedUtility_le_one (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => irrelevantSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm irrelevantSemantics).play policy) ≤
      1 := by
  rw [irrelevant_expectedUtility]
  apply FinDist.expect_le_of_forall
  intro signal _
  apply FinDist.expect_le_of_forall
  intro action _
  cases action <;> norm_num

theorem fullCopySignal_decision (signal : Bool) :
    fullCopySignal () decisionSite (observedConfig signal) =
      FinDist.pure signal := by
  rfl

/-- Observing and copying the fair signal wins surely in the matching game. -/
theorem matching_copy_expectedUtility :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          fullCopySignal) =
      1 := by
  rw [matching_expectedUtility, fairSignal_expect]
  rw [fullCopySignal_decision, fullCopySignal_decision,
    FinDist.expect_pure, FinDist.expect_pure]
  norm_num

/-! ## Safe positive case -/

/-- The always-true reduced policy is Nash in the reduced native game. -/
theorem irrelevant_reduced_true_isNash :
    IsNash (pruning.reducedNativeGameForm irrelevantSemantics)
      (euPreference fun assignment owner =>
        irrelevantSemantics.utility owner assignment)
      (reducedPure true) := by
  rw [isNash_iff]
  intro owner replacement
  rw [euPreference_apply]
  change expectedUtility
      (fun assignment owner => irrelevantSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm irrelevantSemantics).play
        (pruning.expandPolicy
          (Profile.update (reducedPure true) owner replacement))) ≤
    expectedUtility
      (fun assignment owner => irrelevantSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm irrelevantSemantics).play
        (pruning.expandPolicy (reducedPure true)))
  rw [irrelevant_expanded_true_expectedUtility]
  exact irrelevant_expectedUtility_le_one _

/-- Every full deviation is covered by retaining the always-true reduced rule. -/
theorem irrelevant_true_coversFullDeviations :
    pruning.CoversFullDeviationsAt irrelevantSemantics
      (reducedPure true) := by
  intro owner fullReplacement
  refine ⟨(reducedPure true) owner, ?_⟩
  rw [euPreference_apply, Profile.update_eq_self]
  change expectedUtility
      (fun assignment owner => irrelevantSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm irrelevantSemantics).play
        (Profile.update (pruning.expandPolicy (reducedPure true))
          owner fullReplacement)) ≤
    expectedUtility
      (fun assignment owner => irrelevantSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm irrelevantSemantics).play
        (pruning.expandPolicy (reducedPure true)))
  rw [irrelevant_expanded_true_expectedUtility]
  exact irrelevant_expectedUtility_le_one _

/-- The public safe-reduction theorem transfers reduced Nash to full Nash. -/
theorem irrelevant_expanded_true_isNash :
    IsNash (nativeBehavioralGameForm irrelevantSemantics)
      (euPreference fun assignment owner =>
        irrelevantSemantics.utility owner assignment)
      (pruning.expandPolicy (reducedPure true)) :=
  pruning.isNash_expanded_of_isNash_reduced irrelevantSemantics
    (reducedPure true) irrelevant_true_coversFullDeviations
    irrelevant_reduced_true_isNash

/-- At the certified profile the reduced and full Nash questions coincide. -/
theorem irrelevant_true_nash_transfer :
    IsNash (nativeBehavioralGameForm irrelevantSemantics)
        (euPreference fun assignment owner =>
          irrelevantSemantics.utility owner assignment)
        (pruning.expandPolicy (reducedPure true)) ↔
      IsNash (pruning.reducedNativeGameForm irrelevantSemantics)
        (euPreference fun assignment owner =>
          irrelevantSemantics.utility owner assignment)
        (reducedPure true) :=
  pruning.isNash_expanded_iff_reducedNative_of_covers irrelevantSemantics
    (reducedPure true) irrelevant_true_coversFullDeviations

/-! ## Unsafe nearby case -/

/-- Every reduced profile is Nash when all signal-blind policies earn one half. -/
theorem matching_reduced_isNash (policy : pruning.ReducedPolicy) :
    IsNash (pruning.reducedNativeGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      policy := by
  rw [isNash_iff]
  intro owner replacement
  rw [euPreference_apply]
  change expectedUtility
      (fun assignment owner => matchingSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm matchingSemantics).play
        (pruning.expandPolicy (Profile.update policy owner replacement))) ≤
    expectedUtility
      (fun assignment owner => matchingSemantics.utility owner assignment)
      () ((nativeBehavioralGameForm matchingSemantics).play
        (pruning.expandPolicy policy))
  rw [matching_expanded_reduced_expectedUtility,
    matching_expanded_reduced_expectedUtility]

theorem matching_reduced_false_isNash :
    IsNash (pruning.reducedNativeGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      (reducedPure false) :=
  matching_reduced_isNash (reducedPure false)

/-- The observation-responsive policy is genuinely outside the reduced image. -/
theorem fullCopySignal_not_represented :
    ¬ pruning.Represents fullCopySignal := by
  rintro ⟨policy, hpolicy⟩
  have hblind := expanded_reduced_ignores_signal policy false true
  rw [hpolicy, fullCopySignal_decision, fullCopySignal_decision] at hblind
  have hprob := congrArg (fun law : FinDist Bool => law.prob true) hblind
  rw [FinDist.prob_pure_of_ne (by decide), FinDist.prob_pure_self] at hprob
  norm_num at hprob

theorem update_expanded_false_to_copy :
    Profile.update (sig := nativeBehavioralSignature diagram)
        (pruning.expandPolicy (reducedPure false)) ()
        (fullCopySignal ()) =
      fullCopySignal := by
  funext owner
  cases owner
  simp

/-- The copying full deviation strictly improves on the signal-blind profile. -/
theorem matching_copy_is_profitable :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          (pruning.expandPolicy (reducedPure false))) <
      expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          (Profile.update (pruning.expandPolicy (reducedPure false)) ()
            (fullCopySignal ()))) := by
  rw [update_expanded_false_to_copy, matching_copy_expectedUtility,
    matching_expanded_reduced_expectedUtility]
  norm_num

/-- The signal-blind reduced Nash profile expands to a non-Nash full profile. -/
theorem matching_expanded_false_not_isNash :
    ¬ IsNash (nativeBehavioralGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      (pruning.expandPolicy (reducedPure false)) := by
  intro hnash
  have hdeviation := (isNash_iff _).mp hnash () (fullCopySignal ())
  rw [euPreference_apply, update_expanded_false_to_copy,
    matching_copy_expectedUtility,
    matching_expanded_reduced_expectedUtility] at hdeviation
  norm_num at hdeviation

/-- The negative example also refutes the exact missing coverage certificate. -/
theorem matching_false_not_coversFullDeviations :
    ¬ pruning.CoversFullDeviationsAt matchingSemantics
      (reducedPure false) := by
  intro hcover
  apply matching_expanded_false_not_isNash
  exact pruning.isNash_expanded_of_isNash_reduced matchingSemantics
    (reducedPure false) hcover matching_reduced_false_isNash

end GameTheory.Tests.MAIDSafeReduction
