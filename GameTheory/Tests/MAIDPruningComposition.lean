/-
# Nested MAID observation-pruning composition

One decision originally observes two Boolean signals.  The coarse pruning
retains the first signal, while the fine pruning retains neither.  Action
reward validates nested deviation coverage and preference orientation.  A
nearby signal-matching payoff makes the first pruning step unsafe while the
coarse-to-full step remains safe.  No graphical or recall claim is made.
-/

import GameTheory.Languages.MAID.ObservationPruning
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Tests.MAIDPruningComposition

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence

local syntax:max "expectedUtility" term:max term:max term:max : term
local macro_rules
  | `(expectedUtility $utility $who $law) =>
      `(GameTheory.expectedUtility $utility $who $law
        (payoffIntegrable_of_finite $law _))

set_option backward.isDefEq.respectTransparency false in
inductive Node
  | firstSignal
  | secondSignal
  | decision
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .firstSignal => ∅
  | .secondSignal => ∅
  | .decision => {.firstSignal, .secondSignal}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.firstSignal, .secondSignal, .decision]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · simp [parents] at hparent
    · rcases Finset.mem_insert.mp hparent with hfirst | hsecond
      · subst parent
        exact ⟨0, by decide, rfl⟩
      · have hparent : parent = .secondSignal := by
          simpa [parents] using hsecond
        subst parent
        exact ⟨1, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit Node where
  kind
    | .firstSignal => .chance
    | .secondSignal => .chance
    | .decision => .decision ()
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := fun _ => id
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

def topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents :=
  topologicalParents

def fairSignal : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

theorem fairSignal_expect (score : Bool → ℝ) :
    expect fairSignal score (payoffIntegrable_of_finite fairSignal score) =
      (score false + score true) / 2 := by
  rw [fairSignal]
  rw [expect_mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true) score
    (payoffIntegrable_pure false score) (payoffIntegrable_pure true score)]
  rw [expect_pure false score (payoffIntegrable_pure false score),
    expect_pure true score (payoffIntegrable_pure true score)]
  norm_num
  ring

@[reducible]
def testSemantics (matchSignal : Bool) : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | firstSignal => exact fairSignal
    | secondSignal => exact PMF.pure false
    | decision => simp at hchance
  utility _ assignment :=
    if matchSignal then
      if assignment .decision = assignment .firstSignal then 1 else 0
    else if assignment .decision then 1 else 0

abbrev actionSemantics := testSemantics false

abbrev matchingSemantics := testSemantics true

/-- Retain only the first signal at the decision. -/
def coarse : Pruning diagram where
  kept
    | .firstSignal => ∅
    | .secondSignal => ∅
    | .decision => {.firstSignal}
  kept_sub_observed node := by
    cases node <;> simp [parents]

/-- Retain no observation at the decision. -/
def fine : Pruning diagram where
  kept _ := ∅
  kept_sub_observed _ := by simp

/-- Both pruning steps remove a genuinely present observation. -/
theorem decision_information_chain :
    diagram.observedParents .decision =
        {.firstSignal, .secondSignal} ∧
      coarse.kept .decision = {.firstSignal} ∧
      fine.kept .decision = ∅ := by
  simp [diagram, parents, coarse, fine]

theorem fine_refines_coarse : fine.Refines coarse := by
  intro node
  cases node <;> simp [fine, coarse]

def decisionSite : DecisionSite diagram () := ⟨.decision, rfl⟩

def assignmentOf (first second action : Bool) : Assignment diagram
  | .firstSignal => first
  | .secondSignal => second
  | .decision => action

def observedConfig (first second : Bool) :
    Config diagram (diagram.observedParents decisionSite.1) :=
  Assignment.restrict diagram (assignmentOf first second false)
    (diagram.observedParents .decision)

theorem restrict_after_signals (matchSignal first second : Bool) :
    Assignment.restrict diagram
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne
            (testSemantics matchSignal).defaultValue
            ⟨.firstSignal, first⟩)
          ⟨.secondSignal, second⟩)
        (diagram.observedParents .decision) =
      observedConfig first second := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, observedConfig,
      Stage.Assignment.setOne, Assignment.resolve, assignmentOf] at hnode ⊢

theorem set_decision_after_signals
    (matchSignal first second action : Bool) :
    Stage.Assignment.setOne
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne
            (testSemantics matchSignal).defaultValue
            ⟨.firstSignal, first⟩)
          ⟨.secondSignal, second⟩)
        ⟨.decision, action⟩ =
      assignmentOf first second action := by
  funext node
  cases node <;>
    simp [Stage.Assignment.setOne, Assignment.resolve, assignmentOf]

theorem assignmentNodeLaw_first (matchSignal : Bool)
    (policy : Policy diagram) (assignment : Assignment diagram) :
    assignmentNodeLaw (testSemantics matchSignal) policy assignment
        .firstSignal =
      fairSignal := by
  rfl

theorem assignmentNodeLaw_second (matchSignal : Bool)
    (policy : Policy diagram) (assignment : Assignment diagram) :
    assignmentNodeLaw (testSemantics matchSignal) policy assignment
        .secondSignal =
      PMF.pure false := by
  rfl

theorem assignmentNodeLaw_decision_after_signals
    (matchSignal first second : Bool) (policy : Policy diagram) :
    assignmentNodeLaw (testSemantics matchSignal) policy
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne
            (testSemantics matchSignal).defaultValue
            ⟨.firstSignal, first⟩)
          ⟨.secondSignal, second⟩) .decision =
      policy () decisionSite (observedConfig first second) := by
  unfold assignmentNodeLaw
  exact congrArg (policy () decisionSite)
    (restrict_after_signals matchSignal first second)

theorem native_play_eq (matchSignal : Bool) (policy : Policy diagram) :
    (nativeBehavioralGameForm (testSemantics matchSignal)).play policy =
      fairSignal.bind fun first =>
        (policy () decisionSite (observedConfig first false)).map
          (assignmentOf first false) := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological
      (testSemantics matchSignal) policy]
  show assignmentRun (testSemantics matchSignal) policy
      [.firstSignal, .secondSignal, .decision]
      (testSemantics matchSignal).defaultValue = _
  simp only [assignmentRun.eq_def]
  rw [assignmentStep.eq_def, assignmentNodeLaw_first, PMF.bind_map]
  apply bind_congr_on_support
  intro first _
  simp only [Function.comp_apply]
  simp only [assignmentRun.eq_def]
  rw [assignmentStep.eq_def, assignmentNodeLaw_second,
    PMF.pure_map, PMF.pure_bind]
  simp only [assignmentRun.eq_def]
  rw [assignmentStep.eq_def,
    assignmentNodeLaw_decision_after_signals, PMF.bind_map]
  apply bind_congr_on_support
  intro action _
  exact congrArg PMF.pure
    (set_decision_after_signals matchSignal first false action)

theorem action_expectedUtility (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm actionSemantics).play policy) =
      expect fairSignal (fun first =>
        expect (policy () decisionSite (observedConfig first false))
          (fun action => if action then 1 else 0)
          (payoffIntegrable_of_finite _ _))
        (payoffIntegrable_of_finite _ _) := by
  rw [native_play_eq false]
  rw [expectedUtility_bind
    (fun assignment owner => actionSemantics.utility owner assignment)
    () fairSignal
    (fun first =>
      (policy () decisionSite (observedConfig first false)).map
        (assignmentOf first false))
    (payoffIntegrable_of_finite _ _)
    (fun first => payoffIntegrable_of_finite _ _)]
  apply expect_congr_on_support
  intro first _
  rw [expectedUtility_map]
  simp only [GameTheory.expectedUtility]
  rfl

theorem matching_expectedUtility (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play policy) =
      expect fairSignal (fun first =>
        expect (policy () decisionSite (observedConfig first false))
          (fun action => if action = first then 1 else 0)
          (payoffIntegrable_of_finite _ _))
        (payoffIntegrable_of_finite _ _) := by
  rw [native_play_eq true]
  rw [expectedUtility_bind
    (fun assignment owner => matchingSemantics.utility owner assignment)
    () fairSignal
    (fun first =>
      (policy () decisionSite (observedConfig first false)).map
        (assignmentOf first false))
    (payoffIntegrable_of_finite _ _)
    (fun first => payoffIntegrable_of_finite _ _)]
  apply expect_congr_on_support
  intro first _
  rw [expectedUtility_map]
  simp only [GameTheory.expectedUtility]
  rfl

theorem node_not_mem_empty (node : Node) : node ∉ (∅ : Finset Node) := by
  simp

theorem fine_expanded_ignores_first (policy : fine.ReducedPolicy)
    (first second : Bool) :
    fine.expandPolicy policy () decisionSite
        (observedConfig first false) =
      fine.expandPolicy policy () decisionSite
        (observedConfig second false) := by
  unfold Pruning.expandPolicy Pruning.expandOwnerPolicy
  apply congrArg (policy () decisionSite)
  funext node
  exact (node_not_mem_empty node.1 node.2).elim

theorem expect_match_false_add_true (law : PMF Bool) :
    expect law (fun action => if action = false then 1 else 0)
        (payoffIntegrable_of_finite law _) +
        expect law (fun action => if action = true then 1 else 0)
          (payoffIntegrable_of_finite law _) =
      1 := by
  rw [← expect_add (payoffIntegrable_of_finite law _)
    (payoffIntegrable_of_finite law _)]
  calc
    expect law (fun action =>
        (if action = false then 1 else 0) +
          (if action = true then 1 else 0))
        (payoffIntegrable_of_finite law _) =
        expect law (fun _ => 1) (payoffIntegrable_of_finite law _) := by
      apply expect_congr_on_support
      intro action _
      cases action <;> norm_num
    _ = 1 := expect_constant law 1 (payoffIntegrable_of_finite law _)

def finePolicy : fine.ReducedPolicy :=
  fun _ _ _ => PMF.pure true

def coarsePolicy : coarse.ReducedPolicy :=
  fine.expandPolicyTo coarse fine_refines_coarse finePolicy

def fineFalse : fine.ReducedPolicy :=
  fun _ _ _ => PMF.pure false

def coarseCopyFirst : coarse.ReducedPolicy :=
  fun _ site observed =>
    match hnode : site.1 with
    | .firstSignal => by
        have hkind := site.2
        simp [diagram, hnode] at hkind
    | .secondSignal => by
        have hkind := site.2
        simp [diagram, hnode] at hkind
    | .decision =>
        PMF.pure
          (observed ⟨.firstSignal, by simp [coarse, hnode]⟩)

theorem action_expanded_fine_true_expectedUtility :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm actionSemantics).play
          (fine.expandPolicy finePolicy)) =
      1 := by
  rw [action_expectedUtility, fairSignal_expect]
  simp [Pruning.expandPolicy, Pruning.expandOwnerPolicy, finePolicy,
    expect_pure]

theorem action_expectedUtility_le_one (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm actionSemantics).play policy) ≤
      1 := by
  rw [action_expectedUtility]
  apply expect_le_const
  intro first _
  apply expect_le_const
  intro action _
  cases action <;> norm_num

theorem matching_expanded_fine_expectedUtility
    (policy : fine.ReducedPolicy) :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          (fine.expandPolicy policy)) =
      1 / 2 := by
  rw [matching_expectedUtility, fairSignal_expect,
    fine_expanded_ignores_first policy false true,
    expect_match_false_add_true]

theorem matching_expectedUtility_le_one (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play policy) ≤
      1 := by
  rw [matching_expectedUtility]
  apply expect_le_const
  intro first _
  apply expect_le_const
  intro action _
  by_cases hmatch : action = first <;> simp [hmatch]

theorem coarseCopyFirst_decision (first second : Bool) :
    coarse.expandPolicy coarseCopyFirst () decisionSite
        (observedConfig first second) =
      PMF.pure first := by
  rfl

theorem matching_coarse_copy_expectedUtility :
    expectedUtility
        (fun assignment owner => matchingSemantics.utility owner assignment)
        () ((nativeBehavioralGameForm matchingSemantics).play
          (coarse.expandPolicy coarseCopyFirst)) =
      1 := by
  rw [matching_expectedUtility, fairSignal_expect,
    coarseCopyFirst_decision, coarseCopyFirst_decision,
    expect_pure, expect_pure]
  norm_num

/-- Expanding through the intermediate policy domain is literal composition. -/
theorem expand_in_stages :
    coarse.expandPolicy coarsePolicy = fine.expandPolicy finePolicy :=
  fine.expandPolicy_expandPolicyTo coarse fine_refines_coarse finePolicy

/-- Nested expansion respects an actual unilateral policy replacement. -/
theorem expand_update_in_stages
    (replacement : fine.ReducedOwnerPolicy ()) :
    fine.expandPolicyTo coarse fine_refines_coarse
        (Profile.update (sig := fine.reducedBehavioralSignature)
          finePolicy () replacement) =
      Profile.update (sig := coarse.reducedBehavioralSignature)
        coarsePolicy ()
        (fine.expandOwnerPolicyTo coarse fine_refines_coarse ()
          replacement) :=
  fine.expandPolicyTo_update coarse fine_refines_coarse finePolicy ()
    replacement

/-- The intermediate and direct policies induce the same canonical law. -/
theorem coarse_native_play_eq_fine_native_play :
    (coarse.reducedNativeGameForm actionSemantics).play coarsePolicy =
      (fine.reducedNativeGameForm actionSemantics).play finePolicy :=
  fine.reducedNative_play_expandPolicyTo coarse fine_refines_coarse
    actionSemantics finePolicy

theorem action_fine_true_reduced_expectedUtility :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((fine.reducedNativeGameForm actionSemantics).play finePolicy) =
      1 :=
  action_expanded_fine_true_expectedUtility

theorem action_coarsePolicy_reduced_expectedUtility :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((coarse.reducedNativeGameForm actionSemantics).play
          coarsePolicy) =
      1 := by
  rw [coarse_native_play_eq_fine_native_play]
  exact action_fine_true_reduced_expectedUtility

theorem action_fine_expectedUtility_le_one
    (policy : fine.ReducedPolicy) :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((fine.reducedNativeGameForm actionSemantics).play policy) ≤
      1 :=
  action_expectedUtility_le_one (fine.expandPolicy policy)

theorem action_coarse_expectedUtility_le_one
    (policy : coarse.ReducedPolicy) :
    expectedUtility
        (fun assignment owner => actionSemantics.utility owner assignment)
        () ((coarse.reducedNativeGameForm actionSemantics).play policy) ≤
      1 :=
  action_expectedUtility_le_one (coarse.expandPolicy policy)

/-- Maximal action reward orients the fine-to-coarse preference correctly. -/
theorem fine_covers_coarse :
    fine.CoversReducedDeviationsAt coarse fine_refines_coarse
      actionSemantics finePolicy := by
  intro owner coarseReplacement
  refine ⟨finePolicy owner, ?_⟩
  rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _), Profile.update_eq_self,
    action_fine_true_reduced_expectedUtility]
  exact action_coarse_expectedUtility_le_one _

/-- Maximal action reward also covers every original full-policy deviation. -/
theorem coarse_covers_full :
    coarse.CoversFullDeviationsAt actionSemantics coarsePolicy := by
  intro owner fullReplacement
  refine ⟨coarsePolicy owner, ?_⟩
  rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _), Profile.update_eq_self,
    action_coarsePolicy_reduced_expectedUtility]
  exact action_expectedUtility_le_one _

/-- The two genuine stage certificates compose to full deviation coverage. -/
theorem fine_covers_full :
    fine.CoversFullDeviationsAt actionSemantics finePolicy :=
  Pruning.CoversReducedDeviationsAt.coversFull
    fine coarse fine_refines_coarse
    actionSemantics finePolicy fine_covers_coarse coarse_covers_full

/-- The maximal action-reward policy is Nash in the fine policy space. -/
theorem fine_isNash :
    IsNash (fine.reducedNativeGameForm actionSemantics)
      (euPreference fun assignment owner =>
        actionSemantics.utility owner assignment)
      finePolicy := by
  rw [isNash_iff]
  intro owner replacement
  rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    action_fine_true_reduced_expectedUtility]
  exact action_fine_expectedUtility_le_one _

/-- Composed coverage transfers fine Nash through both pruning stages. -/
theorem expanded_fine_isNash :
    IsNash (nativeBehavioralGameForm actionSemantics)
      (euPreference fun assignment owner =>
        actionSemantics.utility owner assignment)
      (fine.expandPolicy finePolicy) :=
  fine.isNash_expanded_of_isNash_reduced actionSemantics finePolicy
    fine_covers_full fine_isNash

/-! ## A load-bearing intermediate certificate -/

def matchingCoarseBase : coarse.ReducedPolicy :=
  fine.expandPolicyTo coarse fine_refines_coarse fineFalse

theorem update_matchingCoarseBase_to_copy :
    Profile.update (sig := coarse.reducedBehavioralSignature)
        matchingCoarseBase () (coarseCopyFirst ()) =
      coarseCopyFirst := by
  funext owner
  cases owner
  simp

theorem update_expanded_fineFalse_to_copy :
    Profile.update (sig := nativeBehavioralSignature diagram)
        (fine.expandPolicy fineFalse) ()
        ((coarse.expandPolicy coarseCopyFirst) ()) =
      coarse.expandPolicy coarseCopyFirst := by
  funext owner
  cases owner
  simp

/-- Retaining the payoff-relevant first signal still covers every full
deviation, even when the baseline coarse policy arose from the fine space. -/
theorem matching_coarse_covers_full :
    coarse.CoversFullDeviationsAt matchingSemantics
      matchingCoarseBase := by
  intro owner fullReplacement
  refine ⟨coarseCopyFirst owner, ?_⟩
  rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  have howner : owner = () := by cases owner; rfl
  subst owner
  rw [update_matchingCoarseBase_to_copy,
    matching_coarse_copy_expectedUtility]
  exact matching_expectedUtility_le_one _

/-- Every fine policy is signal-blind and therefore earns exactly one half. -/
theorem matching_fine_isNash (policy : fine.ReducedPolicy) :
    IsNash (fine.reducedNativeGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      policy := by
  rw [isNash_iff]
  intro owner replacement
  rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  rw [matching_expanded_fine_expectedUtility,
    matching_expanded_fine_expectedUtility]

theorem matching_fineFalse_isNash :
    IsNash (fine.reducedNativeGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      fineFalse :=
  matching_fine_isNash fineFalse

/-- The copying full deviation refutes Nash after the unsafe fine expansion. -/
theorem matching_expanded_fineFalse_not_isNash :
    ¬ IsNash (nativeBehavioralGameForm matchingSemantics)
      (euPreference fun assignment owner =>
        matchingSemantics.utility owner assignment)
      (fine.expandPolicy fineFalse) := by
  intro hnash
  have hdeviation := (isNash_iff _).mp hnash ()
    ((coarse.expandPolicy coarseCopyFirst) ())
  rcases hdeviation with ⟨hbase, hcopy, hle⟩
  have hbase' := expectedUtility_congr_law
    (fun assignment who => matchingSemantics.utility who assignment) ()
    rfl hbase (payoffIntegrable_of_finite
      ((nativeBehavioralGameForm matchingSemantics).play
        (fine.expandPolicy fineFalse)) _)
  have hcopyLaw :
      (nativeBehavioralGameForm matchingSemantics).play
          (Profile.update (fine.expandPolicy fineFalse) ()
            ((coarse.expandPolicy coarseCopyFirst) ())) =
        (nativeBehavioralGameForm matchingSemantics).play
          (coarse.expandPolicy coarseCopyFirst) := by
    exact congrArg (nativeBehavioralGameForm matchingSemantics).play
      update_expanded_fineFalse_to_copy
  have hcopy' := expectedUtility_congr_law
    (fun assignment who => matchingSemantics.utility who assignment) ()
    hcopyLaw hcopy (payoffIntegrable_of_finite
      ((nativeBehavioralGameForm matchingSemantics).play
        (coarse.expandPolicy coarseCopyFirst)) _)
  rw [hcopy', hbase', matching_coarse_copy_expectedUtility,
    matching_expanded_fine_expectedUtility] at hle
  norm_num at hle

/-- The first pruning step is not covered.  Otherwise its composition with the
valid coarse-to-full certificate would transfer the fine Nash profile to the
full game, contradicting the explicit copying deviation. -/
theorem matching_fine_not_covers_coarse :
    ¬ fine.CoversReducedDeviationsAt coarse fine_refines_coarse
      matchingSemantics fineFalse := by
  intro hstep
  have hfull : fine.CoversFullDeviationsAt matchingSemantics fineFalse :=
    Pruning.CoversReducedDeviationsAt.coversFull
      fine coarse fine_refines_coarse matchingSemantics fineFalse
      hstep matching_coarse_covers_full
  apply matching_expanded_fineFalse_not_isNash
  exact fine.isNash_expanded_of_isNash_reduced matchingSemantics
    fineFalse hfull matching_fineFalse_isNash

/-- The same two-stage fixture shows exactly which semantic premise is
load-bearing: coarse-to-full coverage survives, fine-to-coarse coverage does
not, and reduced Nash consequently does not transfer to the original game. -/
theorem intermediate_stage_certificate_is_load_bearing :
    coarse.CoversFullDeviationsAt matchingSemantics matchingCoarseBase ∧
      ¬ fine.CoversReducedDeviationsAt coarse fine_refines_coarse
        matchingSemantics fineFalse ∧
      IsNash (fine.reducedNativeGameForm matchingSemantics)
        (euPreference fun assignment owner =>
          matchingSemantics.utility owner assignment)
        fineFalse ∧
      ¬ IsNash (nativeBehavioralGameForm matchingSemantics)
        (euPreference fun assignment owner =>
          matchingSemantics.utility owner assignment)
        (fine.expandPolicy fineFalse) :=
  ⟨matching_coarse_covers_full, matching_fine_not_covers_coarse,
    matching_fineFalse_isNash, matching_expanded_fineFalse_not_isNash⟩

end GameTheory.Tests.MAIDPruningComposition
