/-
# EXP-107: Forgetful Movie Star source audit

This fixture instantiates the qualitative payoffs in Milch--Koller's
Forgetful Movie Star example with small rational values.  It validates the
advertised edge-addition fixpoint and same-owner s-reachability cycle, then
checks the paper's proposed independent-uniform reduced profile against the
library's whole-owner behavioral Nash predicate.  A constant replacement at
both star decisions is already profitable in the reduced game.

The result is deliberately about this parameterization and this profile.  It
does not dispute the graph theorem or claim that every imperfect-recall
fixpoint is safe.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDForgetfulMovieStarAudit

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

inductive Player
  | star
  | robot
  deriving DecidableEq, Fintype

inductive Node
  | sponsorship
  | starFirst
  | starSecond
  | robotChoice
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .sponsorship => ∅
  | .starFirst => {.sponsorship}
  | .starSecond => {.sponsorship}
  | .robotChoice => ∅

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.sponsorship, .starFirst, .starSecond, .robotChoice]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsponsor : parent = .sponsorship := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · have hsponsor : parent = .sponsorship := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · simp [parents] at hparent

@[reducible]
def diagram : Structure Player Node where
  kind
    | .sponsorship => .chance
    | .starFirst => .decision .star
    | .starSecond => .decision .star
    | .robotChoice => .decision .robot
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

def fairBool : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem fairBool_expect (score : Bool → ℝ) :
    fairBool.expect score = (score false + score true) / 2 := by
  rw [fairBool, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure]
  ring

def avoidScore (starChoice robotChoice : Bool) : ℝ :=
  if starChoice ≠ robotChoice then 2 else 0

def consistencyScore (first second : Bool) : ℝ :=
  if first = second then 1 else 0

def robotScore (starChoice robotChoice : Bool) : ℝ :=
  if starChoice = robotChoice then 1 else 0

@[reducible]
def semantics : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | sponsorship => exact fairBool
    | starFirst => simp at hchance
    | starSecond => simp at hchance
    | robotChoice => simp at hchance
  utility player assignment :=
    match player with
    | .star =>
        avoidScore (assignment .starFirst) (assignment .robotChoice) +
          consistencyScore (assignment .starFirst) (assignment .starSecond)
    | .robot => robotScore (assignment .starFirst) (assignment .robotChoice)

def avoidTerm : UtilityTerm diagram where
  parents := {.starFirst, .robotChoice}
  payoff configuration :=
    avoidScore
      (configuration ⟨.starFirst, by simp⟩)
      (configuration ⟨.robotChoice, by simp⟩)

def consistencyTerm : UtilityTerm diagram where
  parents := {.starFirst, .starSecond}
  payoff configuration :=
    consistencyScore
      (configuration ⟨.starFirst, by simp⟩)
      (configuration ⟨.starSecond, by simp⟩)

def robotTerm : UtilityTerm diagram where
  parents := {.starFirst, .robotChoice}
  payoff configuration :=
    robotScore
      (configuration ⟨.starFirst, by simp⟩)
      (configuration ⟨.robotChoice, by simp⟩)

def utilityView : UtilityView semantics where
  terms
    | .star => [avoidTerm, consistencyTerm]
    | .robot => [robotTerm]
  utility_eq_sum player assignment := by
    cases player <;>
      simp [avoidTerm, consistencyTerm, robotTerm, UtilityTerm.value,
        Assignment.restrict]

def pruning : Pruning diagram where
  kept _ := ∅
  kept_sub_observed _ := by simp

def firstSite : DecisionSite diagram .star := ⟨.starFirst, rfl⟩

def secondSite : DecisionSite diagram .star := ⟨.starSecond, rfl⟩

def robotSite : DecisionSite diagram .robot := ⟨.robotChoice, rfl⟩

def consistencySite : utilityView.UtilitySite .star :=
  ⟨1, by simp [utilityView]⟩

private def firstGraphParents :
    utilityView.GraphNode .star → Finset (utilityView.GraphNode .star) :=
  UtilityView.graphParentsUnder utilityView
    (Pruning.restoreAllAt pruning firstSite)

private def secondGraphParents :
    utilityView.GraphNode .star → Finset (utilityView.GraphNode .star) :=
  UtilityView.graphParentsUnder utilityView
    (Pruning.restoreAllAt pruning secondSite)

private def firstEvidence : Finset (utilityView.GraphNode .star) :=
  UtilityView.conditioningUnder utilityView
    (Pruning.restoreAllAt pruning firstSite) firstSite
    (Pruning.missingAt pruning firstSite)

private def secondEvidence : Finset (utilityView.GraphNode .star) :=
  UtilityView.conditioningUnder utilityView
    (Pruning.restoreAllAt pruning secondSite) secondSite
    (Pruning.missingAt pruning secondSite)

private theorem sponsorship_not_term_parent
    (site : utilityView.UtilitySite .star) :
    (.base .sponsorship : utilityView.GraphNode .star) ∉
      (utilityView.term site).parents.image UtilityView.GraphNode.base := by
  intro hmem
  obtain ⟨node, hnode, heq⟩ := Finset.mem_image.mp hmem
  cases node with
  | sponsorship =>
      fin_cases site <;>
        simp [UtilityView.term, utilityView, avoidTerm, consistencyTerm]
          at hnode
  | starFirst =>
      have := UtilityView.GraphNode.base.inj heq
      cases this
  | starSecond =>
      have := UtilityView.GraphNode.base.inj heq
      cases this
  | robotChoice =>
      have := UtilityView.GraphNode.base.inj heq
      cases this

private theorem first_signal_child_eq
    {next : utilityView.GraphNode .star}
    (hedge : FiniteBNMoralSeparation.DirectedEdge firstGraphParents
      (.base .sponsorship) next) :
    next = .base .starFirst := by
  cases next with
  | base node =>
      cases node <;>
        simp [FiniteBNMoralSeparation.DirectedEdge, firstGraphParents,
          UtilityView.graphParentsUnder, effectiveParentsUnder,
          Pruning.restoreAllAt, pruning, diagram, parents, firstSite]
          at hedge ⊢
  | utility site =>
      exfalso
      apply sponsorship_not_term_parent site
      simpa [FiniteBNMoralSeparation.DirectedEdge, firstGraphParents,
        UtilityView.graphParentsUnder]
        using hedge

private theorem second_signal_child_eq
    {next : utilityView.GraphNode .star}
    (hedge : FiniteBNMoralSeparation.DirectedEdge secondGraphParents
      (.base .sponsorship) next) :
    next = .base .starSecond := by
  cases next with
  | base node =>
      cases node <;>
        simp [FiniteBNMoralSeparation.DirectedEdge, secondGraphParents,
          UtilityView.graphParentsUnder, effectiveParentsUnder,
          Pruning.restoreAllAt, pruning, diagram, parents, secondSite]
          at hedge ⊢
  | utility site =>
      exfalso
      apply sponsorship_not_term_parent site
      simpa [FiniteBNMoralSeparation.DirectedEdge, secondGraphParents,
        UtilityView.graphParentsUnder]
        using hedge

private theorem no_edge_into_signal
    (selectedParents : DecisionParentMap Node)
    {previous : utilityView.GraphNode .star}
    (hedge : FiniteBNMoralSeparation.DirectedEdge
      (UtilityView.graphParentsUnder utilityView selectedParents)
      previous (.base .sponsorship)) : False := by
  simp [FiniteBNMoralSeparation.DirectedEdge,
    UtilityView.graphParentsUnder, effectiveParentsUnder, diagram, parents]
    at hedge

private theorem first_parent_eq_signal
    {previous : utilityView.GraphNode .star}
    (hedge : FiniteBNMoralSeparation.DirectedEdge firstGraphParents
      previous (.base .starFirst)) :
    previous = .base .sponsorship := by
  cases previous with
  | base node =>
      cases node <;>
        simp [FiniteBNMoralSeparation.DirectedEdge, firstGraphParents,
          UtilityView.graphParentsUnder, effectiveParentsUnder,
          Pruning.restoreAllAt, diagram, parents, firstSite]
          at hedge ⊢
  | utility site =>
      simp [FiniteBNMoralSeparation.DirectedEdge, firstGraphParents,
        UtilityView.graphParentsUnder] at hedge

private theorem second_parent_eq_signal
    {previous : utilityView.GraphNode .star}
    (hedge : FiniteBNMoralSeparation.DirectedEdge secondGraphParents
      previous (.base .starSecond)) :
    previous = .base .sponsorship := by
  cases previous with
  | base node =>
      cases node <;>
        simp [FiniteBNMoralSeparation.DirectedEdge, secondGraphParents,
          UtilityView.graphParentsUnder, effectiveParentsUnder,
          Pruning.restoreAllAt, diagram, parents, secondSite]
          at hedge ⊢
  | utility site =>
      simp [FiniteBNMoralSeparation.DirectedEdge, secondGraphParents,
        UtilityView.graphParentsUnder] at hedge

private theorem first_signal_not_connected
    (term : utilityView.UtilitySite .star) :
    ¬ UtilityView.DConnectedUnder utilityView
      (Pruning.restoreAllAt pruning firstSite) (.base .sponsorship)
      (.utility term)
      (UtilityView.conditioningUnder utilityView
        (Pruning.restoreAllAt pruning firstSite) firstSite
        (Pruning.missingAt pruning firstSite)) := by
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ FiniteBNMoralSeparation.MoralAdjacent firstGraphParents
        {(.base .sponsorship : UtilityView.GraphNode utilityView .star)}
        {(.utility term)} firstEvidence
        (.base .sponsorship) next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · have hnext := first_signal_child_eq hforward
      subst next
      exact hnextOpen (by
        simp [firstEvidence, UtilityView.conditioningUnder, firstSite])
    · exact no_edge_into_signal
        (Pruning.restoreAllAt pruning firstSite) hbackward
    · obtain ⟨child, _, hsponsor, hnext⟩ := hcoparents
      have hchild := first_signal_child_eq hsponsor
      subst child
      have hnextEq := first_parent_eq_signal hnext
      exact hne hnextEq.symm
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

private theorem second_signal_not_connected
    (term : utilityView.UtilitySite .star) :
    ¬ UtilityView.DConnectedUnder utilityView
      (Pruning.restoreAllAt pruning secondSite) (.base .sponsorship)
      (.utility term)
      (UtilityView.conditioningUnder utilityView
        (Pruning.restoreAllAt pruning secondSite) secondSite
        (Pruning.missingAt pruning secondSite)) := by
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ FiniteBNMoralSeparation.MoralAdjacent secondGraphParents
        {(.base .sponsorship : UtilityView.GraphNode utilityView .star)}
        {(.utility term)} secondEvidence
        (.base .sponsorship) next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · have hnext := second_signal_child_eq hforward
      subst next
      exact hnextOpen (by
        simp [secondEvidence, UtilityView.conditioningUnder, secondSite])
    · exact no_edge_into_signal
        (Pruning.restoreAllAt pruning secondSite) hbackward
    · obtain ⟨child, _, hsponsor, hnext⟩ := hcoparents
      have hchild := second_signal_child_eq hsponsor
      subst child
      have hnextEq := second_parent_eq_signal hnext
      exact hne hnextEq.symm
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem candidate_isEdgeAdditionFixpoint :
    UtilityView.IsEdgeAdditionFixpoint utilityView pruning := by
  intro owner site
  cases owner with
  | star =>
      rcases site with ⟨node, hkind⟩
      cases node with
      | sponsorship => simp at hkind
      | starFirst =>
          constructor
          · simp [Pruning.restoreAllAt, Pruning.missingAt, pruning,
              diagram, parents]
          · intro term _ observation hobservation
            have hsponsor : observation = .sponsorship := by
              simpa [Pruning.missingAt, pruning, diagram, parents,
                firstSite] using hobservation
            subst observation
            exact first_signal_not_connected term
      | starSecond =>
          constructor
          · simp [Pruning.restoreAllAt, Pruning.missingAt, pruning,
              diagram, parents]
          · intro term _ observation hobservation
            have hsponsor : observation = .sponsorship := by
              simpa [Pruning.missingAt, pruning, diagram, parents,
                secondSite] using hobservation
            subst observation
            exact second_signal_not_connected term
      | robotChoice => simp at hkind
  | robot =>
      rcases site with ⟨node, hkind⟩
      cases node with
      | sponsorship => simp at hkind
      | starFirst => simp at hkind
      | starSecond => simp at hkind
      | robotChoice =>
          constructor
          · simp [Pruning.restoreAllAt, Pruning.missingAt, pruning,
              diagram, parents]
          · intro _ _ observation hobservation
            simp [Pruning.missingAt, pruning, diagram, parents] at hobservation

private theorem consistency_relevant_first :
    utilityView.IsRelevantUtilityTerm firstSite consistencySite := by
  apply Relation.TransGen.single
  show (.base .starFirst : utilityView.GraphNode .star) ∈
    (utilityView.term consistencySite).parents.image
      UtilityView.GraphNode.base
  apply Finset.mem_image.mpr
  exact ⟨.starFirst, by simp [UtilityView.term, utilityView,
    consistencySite, consistencyTerm], rfl⟩

private theorem consistency_relevant_second :
    utilityView.IsRelevantUtilityTerm secondSite consistencySite := by
  apply Relation.TransGen.single
  show (.base .starSecond : utilityView.GraphNode .star) ∈
    (utilityView.term consistencySite).parents.image
      UtilityView.GraphNode.base
  apply Finset.mem_image.mpr
  exact ⟨.starSecond, by simp [UtilityView.term, utilityView,
    consistencySite, consistencyTerm], rfl⟩

private theorem mechanism_connected_to_consistency
    (source target : DecisionSite diagram .star)
    (sourceNode : Node)
    (hsource : source.1 = sourceNode)
    (hsourceOpen : sourceNode ≠ target.1 ∧
      sourceNode ∉ diagram.observedParents target.1)
    (hparent : sourceNode ∈ (utilityView.term consistencySite).parents) :
    FiniteBNMoralSeparation.Connected
      (UtilityView.mechanismGraphParents utilityView source)
      {.mechanism} {.object (.utility consistencySite)}
      (UtilityView.sReachConditioning utilityView target)
      .mechanism (.object (.utility consistencySite)) := by
  let graphParents := UtilityView.mechanismGraphParents utilityView source
  let evidence := UtilityView.sReachConditioning utilityView target
  let mechanismNode : UtilityView.MechanismGraphNode utilityView .star :=
    .mechanism
  let sourceBase : UtilityView.MechanismGraphNode utilityView .star :=
    .object (.base sourceNode)
  let utility : UtilityView.MechanismGraphNode utilityView .star :=
    .object (.utility consistencySite)
  have mechanismSource :
      FiniteBNMoralSeparation.DirectedEdge graphParents
        mechanismNode sourceBase := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents,
      mechanismNode, sourceBase, UtilityView.mechanismGraphParents,
      hsource]
  have sourceUtility :
      FiniteBNMoralSeparation.DirectedEdge graphParents
        sourceBase utility := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents, sourceBase,
      utility, UtilityView.mechanismGraphParents]
    exact hparent
  have mechanismOpen : mechanismNode ∉ evidence := by
    simp [mechanismNode, evidence, UtilityView.sReachConditioning]
  have sourceOpen : sourceBase ∉ evidence := by
    simpa [sourceBase, evidence, UtilityView.sReachConditioning]
      using hsourceOpen
  have utilityOpen : utility ∉ evidence := by
    simp [utility, evidence, UtilityView.sReachConditioning]
  have mechanismAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence mechanismNode := by
    refine ⟨mechanismNode, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have sourceAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence sourceBase := by
    refine ⟨utility, ?_, Relation.ReflTransGen.single sourceUtility⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have utilityAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence utility := by
    refine ⟨utility, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have firstStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence mechanismNode sourceBase :=
    ⟨by simp [mechanismNode, sourceBase], mechanismOpen, sourceOpen,
      mechanismAncestor, sourceAncestor, Or.inl mechanismSource⟩
  have secondStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence sourceBase utility :=
    ⟨by simp [sourceBase, utility], sourceOpen, utilityOpen,
      sourceAncestor, utilityAncestor, Or.inl sourceUtility⟩
  refine ⟨mechanismOpen, utilityOpen, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single firstStep) secondStep

theorem second_sReachable_first :
    UtilityView.SReachable utilityView secondSite firstSite := by
  refine ⟨consistencySite, consistency_relevant_first, ?_⟩
  apply mechanism_connected_to_consistency secondSite firstSite .starSecond rfl
    (by simp [firstSite, diagram, parents])
  simp [UtilityView.term, utilityView, consistencySite, consistencyTerm]

theorem first_sReachable_second :
    UtilityView.SReachable utilityView firstSite secondSite := by
  refine ⟨consistencySite, consistency_relevant_second, ?_⟩
  apply mechanism_connected_to_consistency firstSite secondSite .starFirst rfl
    (by simp [secondSite, diagram, parents])
  simp [UtilityView.term, utilityView, consistencySite, consistencyTerm]

theorem not_sReachAcyclic : ¬ UtilityView.SReachAcyclic utilityView := by
  intro hacyclic
  have cycle : Relation.TransGen
      (fun source target : DecisionSite diagram .star =>
        UtilityView.OrientedRelevance utilityView source target)
      firstSite firstSite :=
    Relation.TransGen.tail
      (Relation.TransGen.single first_sReachable_second)
      second_sReachable_first
  exact hacyclic .star firstSite cycle

def firstObservation (signal : Bool) :
    Config diagram {.sponsorship} :=
  fun _ => signal

def secondObservation (signal : Bool) :
    Config diagram {.sponsorship} :=
  fun _ => signal

def robotObservation :
    Config diagram ∅ :=
  fun parent => (Finset.notMem_empty parent.1 parent.2).elim

def assignmentOf (signal first second robot : Bool) : Assignment diagram
  | .sponsorship => signal
  | .starFirst => first
  | .starSecond => second
  | .robotChoice => robot

private theorem restrict_first_after_signal (signal : Bool) :
    Assignment.restrict diagram
        (ToEFG.Stage.Assignment.setOne semantics.defaultValue
          ⟨.sponsorship, signal⟩)
        (diagram.observedParents .starFirst) =
      firstObservation signal := by
  funext parent
  rcases parent with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, firstObservation,
      ToEFG.Stage.Assignment.setOne, Assignment.resolve] at hnode ⊢

private theorem restrict_second_after_first (signal first : Bool) :
    Assignment.restrict diagram
        (ToEFG.Stage.Assignment.setOne
          (ToEFG.Stage.Assignment.setOne semantics.defaultValue
            ⟨.sponsorship, signal⟩)
          ⟨.starFirst, first⟩)
        (diagram.observedParents .starSecond) =
      secondObservation signal := by
  funext parent
  rcases parent with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, secondObservation,
      ToEFG.Stage.Assignment.setOne, Assignment.resolve] at hnode ⊢

private theorem restrict_robot_after_second
    (signal first second : Bool) :
    Assignment.restrict diagram
        (ToEFG.Stage.Assignment.setOne
          (ToEFG.Stage.Assignment.setOne
            (ToEFG.Stage.Assignment.setOne semantics.defaultValue
              ⟨.sponsorship, signal⟩)
            ⟨.starFirst, first⟩)
          ⟨.starSecond, second⟩)
        (diagram.observedParents .robotChoice) = robotObservation := by
  funext parent
  exact (Finset.notMem_empty parent.1 parent.2).elim

private theorem set_robot_after_second
    (signal first second robot : Bool) :
    ToEFG.Stage.Assignment.setOne
        (ToEFG.Stage.Assignment.setOne
          (ToEFG.Stage.Assignment.setOne
            (ToEFG.Stage.Assignment.setOne semantics.defaultValue
              ⟨.sponsorship, signal⟩)
            ⟨.starFirst, first⟩)
          ⟨.starSecond, second⟩)
        ⟨.robotChoice, robot⟩ =
      assignmentOf signal first second robot := by
  funext node
  cases node <;>
    simp [ToEFG.Stage.Assignment.setOne, Assignment.resolve, assignmentOf]

private theorem assignmentNodeLaw_sponsorship (policy : Policy diagram)
    (assignment : Assignment diagram) :
    assignmentNodeLaw semantics policy assignment .sponsorship = fairBool := by
  rfl

private theorem assignmentNodeLaw_first
    (signal : Bool) (policy : Policy diagram) :
    assignmentNodeLaw semantics policy
        (ToEFG.Stage.Assignment.setOne semantics.defaultValue
          ⟨.sponsorship, signal⟩) .starFirst =
      policy .star firstSite
        (firstObservation signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy .star firstSite)
    (restrict_first_after_signal signal)

private theorem assignmentNodeLaw_second
    (signal first : Bool) (policy : Policy diagram) :
    assignmentNodeLaw semantics policy
        (ToEFG.Stage.Assignment.setOne
          (ToEFG.Stage.Assignment.setOne semantics.defaultValue
            ⟨.sponsorship, signal⟩)
          ⟨.starFirst, first⟩) .starSecond =
      policy .star secondSite
        (secondObservation signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy .star secondSite)
    (restrict_second_after_first signal first)

private theorem assignmentNodeLaw_robot
    (signal first second : Bool) (policy : Policy diagram) :
    assignmentNodeLaw semantics policy
        (ToEFG.Stage.Assignment.setOne
          (ToEFG.Stage.Assignment.setOne
            (ToEFG.Stage.Assignment.setOne semantics.defaultValue
              ⟨.sponsorship, signal⟩)
            ⟨.starFirst, first⟩)
          ⟨.starSecond, second⟩) .robotChoice =
      policy .robot robotSite robotObservation := by
  unfold assignmentNodeLaw
  exact congrArg (policy .robot robotSite)
    (restrict_robot_after_second signal first second)

theorem native_play_eq (policy : Policy diagram) :
    (nativeBehavioralGameForm semantics).play policy =
      fairBool.bind fun signal =>
        (policy .star firstSite
          (firstObservation signal)).bind fun first =>
            (policy .star secondSite
              (secondObservation signal)).bind
                fun second =>
                  (policy .robot robotSite robotObservation).map
                    (assignmentOf signal first second) := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological semantics policy]
  show assignmentRun semantics policy
      [.sponsorship, .starFirst, .starSecond, .robotChoice]
        semantics.defaultValue = _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_sponsorship,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro signal _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_first,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro first _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_second,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro second _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_robot,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro robot _
  rw [assignmentRun]
  exact congrArg FinDist.pure
    (set_robot_after_second signal first second robot)

theorem star_expectedUtility (policy : Policy diagram) :
    expectedUtility
        (fun assignment player => semantics.utility player assignment)
        .star ((nativeBehavioralGameForm semantics).play policy) =
      fairBool.expect fun signal =>
        (policy .star firstSite
          (firstObservation signal)).expect fun first =>
            (policy .star secondSite
              (secondObservation signal)).expect
                fun second =>
                  (policy .robot robotSite robotObservation).expect fun robot =>
                    avoidScore first robot + consistencyScore first second := by
  unfold expectedUtility
  rw [native_play_eq, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _
  rw [FinDist.expect_bind]
  apply FinDist.expect_congr
  intro first _
  rw [FinDist.expect_bind]
  apply FinDist.expect_congr
  intro second _
  rw [FinDist.expect_map]
  rfl

def uniformReducedPolicy : pruning.ReducedPolicy :=
  fun _ _ _ => fairBool

def constantEqualReplacement : pruning.ReducedOwnerPolicy .star :=
  fun _ _ => FinDist.pure false

@[simp]
theorem expanded_uniform_star
    (site : DecisionSite diagram .star)
    (observed : Config diagram (diagram.observedParents site.1)) :
    pruning.expandPolicy uniformReducedPolicy .star site observed = fairBool := by
  rfl

@[simp]
theorem expanded_uniform_robot
    (observed : Config diagram (diagram.observedParents robotSite.1)) :
    pruning.expandPolicy uniformReducedPolicy .robot robotSite observed = fairBool := by
  rfl

@[simp]
theorem expanded_constant_star
    (site : DecisionSite diagram .star)
    (observed : Config diagram (diagram.observedParents site.1)) :
    pruning.expandPolicy
        (Profile.update (sig := pruning.reducedBehavioralSignature)
          uniformReducedPolicy .star constantEqualReplacement)
        .star site observed = FinDist.pure false := by
  simp [Pruning.expandPolicy, Pruning.expandOwnerPolicy,
    constantEqualReplacement]

@[simp]
theorem expanded_constant_robot
    (observed : Config diagram (diagram.observedParents robotSite.1)) :
    pruning.expandPolicy
        (Profile.update (sig := pruning.reducedBehavioralSignature)
          uniformReducedPolicy .star constantEqualReplacement)
        .robot robotSite observed = fairBool := by
  have hupdate :
      (Profile.update (sig := pruning.reducedBehavioralSignature)
        uniformReducedPolicy .star constantEqualReplacement) .robot =
      uniformReducedPolicy .robot := by
    apply Profile.update_of_ne
    decide
  unfold Pruning.expandPolicy
  rw [hupdate]
  rfl

theorem uniform_star_expectedUtility :
    expectedUtility
        (fun assignment player => semantics.utility player assignment)
        .star
        ((pruning.reducedNativeGameForm semantics).play
          uniformReducedPolicy) = 3 / 2 := by
  rw [star_expectedUtility]
  simp only [expanded_uniform_star, expanded_uniform_robot]
  simp_rw [fairBool_expect]
  norm_num [avoidScore, consistencyScore]

theorem constant_deviation_star_expectedUtility :
    expectedUtility
        (fun assignment player => semantics.utility player assignment)
        .star
        ((pruning.reducedNativeGameForm semantics).play
          (Profile.update (sig := pruning.reducedBehavioralSignature)
            uniformReducedPolicy .star constantEqualReplacement)) = 2 := by
  rw [star_expectedUtility]
  simp only [expanded_constant_star, expanded_constant_robot,
    FinDist.expect_pure]
  simp_rw [fairBool_expect]
  norm_num [avoidScore, consistencyScore]

theorem uniformReducedPolicy_not_isNash :
    ¬ IsNash (pruning.reducedNativeGameForm semantics)
      (euPreference fun assignment player =>
        semantics.utility player assignment)
      uniformReducedPolicy := by
  intro hnash
  rw [isNash_iff] at hnash
  have hdeviation := hnash .star constantEqualReplacement
  simp only [euPreference_apply] at hdeviation
  rw [uniform_star_expectedUtility,
    constant_deviation_star_expectedUtility] at hdeviation
  norm_num at hdeviation

end GameTheory.Experimental.PostArchitecture.MAIDForgetfulMovieStarAudit
