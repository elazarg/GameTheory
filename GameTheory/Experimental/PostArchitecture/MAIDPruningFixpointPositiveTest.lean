/-
# EXP-107: positive edge-addition-fixpoint consumer

A fair signal precedes two decisions of one owner.  The early decision sees
the signal; the late decision sees both the signal and the early action.  The
candidate removes the signal from both sites but keeps the early-to-late
observation.  Copying the early action at the late site attains the pointwise
maximum utility, so the semantic coverage certificate is proved directly from
canonical play rather than assumed from a future graphical theorem.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
import GameTheory.Experimental.PostArchitecture.MAIDPruningGlobalReduction
import GameTheory.Languages.MAID.ObservationPruning

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointPositiveTest

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Experimental.PostArchitecture
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

inductive Node
  | signal
  | early
  | late
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .signal => ∅
  | .early => {.signal}
  | .late => {.signal, .early}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .early, .late]
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
    · rcases Finset.mem_insert.mp hparent with hsignal | hearly
      · subst parent
        exact ⟨0, by decide, rfl⟩
      · have hearly : parent = .early := by
          simpa [parents] using hearly
        subst parent
        exact ⟨1, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit Node where
  kind
    | .signal => .chance
    | .early => .decision ()
    | .late => .decision ()
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

def fairSignal : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

@[reducible]
def semantics : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact fairSignal
    | early => simp at hchance
    | late => simp at hchance
  utility _ assignment :=
    if assignment .early = assignment .late then 1 else 0

def matchTerm : UtilityTerm diagram where
  parents := {.early, .late}
  payoff configuration :=
    if configuration ⟨.early, by simp⟩ =
        configuration ⟨.late, by simp⟩ then 1 else 0

def view : UtilityView (diagram := diagram) semantics where
  terms _ := [matchTerm]
  utility_eq_sum _ assignment := by
    simp [matchTerm, UtilityTerm.value, Assignment.restrict]

def termSite : view.UtilitySite () := ⟨0, by simp [view]⟩

def earlySite : DecisionSite diagram () := ⟨.early, rfl⟩

def lateSite : DecisionSite diagram () := ⟨.late, rfl⟩

/-- Remove the fair signal at both decisions while retaining the earlier
decision as an observation of the later decision. -/
def pruning : Pruning diagram where
  kept
    | .signal => ∅
    | .early => ∅
    | .late => {.early}
  kept_sub_observed node := by
    cases node <;> simp [parents]

theorem early_relevant : view.IsRelevantUtilityTerm earlySite termSite := by
  apply Relation.TransGen.single
  simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
    MAIDRequisiteObservation.UtilityView.graphParents,
    MAIDRequisiteObservation.UtilityView.term, view, termSite, matchTerm,
    earlySite]
  exact Finset.mem_insert_self _ _

theorem late_relevant : view.IsRelevantUtilityTerm lateSite termSite := by
  apply Relation.TransGen.single
  simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
    MAIDRequisiteObservation.UtilityView.graphParents,
    MAIDRequisiteObservation.UtilityView.term, view, termSite, matchTerm,
    lateSite]
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

/-- In the original graph the signal at the early decision is requisite:
the open route through the late decision reaches the shared utility leaf. -/
theorem original_signal_at_early_requisite :
    view.IsRequisiteObservation earlySite .signal := by
  refine ⟨by simp [diagram, parents, earlySite], termSite, early_relevant, ?_⟩
  let evidence := view.observationConditioning earlySite .signal
  let signal : view.GraphNode () := .base .signal
  let late : view.GraphNode () := .base .late
  let utility : view.GraphNode () := .utility termSite
  have signalLate :
      MAIDRequisiteObservation.UtilityView.DirectedEdge view signal late := by
    simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
      MAIDRequisiteObservation.UtilityView.graphParents, effectiveParents,
      signal, late, diagram, parents]
  have lateUtility :
      MAIDRequisiteObservation.UtilityView.DirectedEdge view late utility := by
    simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
      MAIDRequisiteObservation.UtilityView.graphParents,
      MAIDRequisiteObservation.UtilityView.term, late, utility,
      view, termSite, matchTerm]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
  have signalOpen : signal ∉ evidence := by
    simp [signal, evidence, earlySite, diagram, parents]
  have lateOpen : late ∉ evidence := by
    simp [late, evidence, earlySite, diagram, parents]
  have utilityOpen : utility ∉ evidence := by
    simp [utility, evidence]
  have signalAncestor :
      view.InAncestralClosure signal utility evidence signal := by
    refine ⟨signal, ?_, Relation.ReflTransGen.refl⟩
    simp
  have lateAncestor :
      view.InAncestralClosure signal utility evidence late := by
    refine ⟨utility, ?_, Relation.ReflTransGen.single lateUtility⟩
    simp
  have utilityAncestor :
      view.InAncestralClosure signal utility evidence utility := by
    refine ⟨utility, ?_, Relation.ReflTransGen.refl⟩
    simp
  have firstStep : view.MoralAdjacent signal utility evidence signal late :=
    ⟨by simp [signal, late], signalOpen, lateOpen,
      signalAncestor, lateAncestor, Or.inl signalLate⟩
  have secondStep : view.MoralAdjacent signal utility evidence late utility :=
    ⟨by simp [late, utility], lateOpen, utilityOpen,
      lateAncestor, utilityAncestor, Or.inl lateUtility⟩
  refine ⟨signalOpen, utilityOpen, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single firstStep) secondStep

/-! ## Edge-addition fixpoint -/

def earlyHybridParents : Node → Finset Node :=
  MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning earlySite

def earlyEvidence : Finset (view.GraphNode ()) :=
  MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
    earlyHybridParents earlySite
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning earlySite)

theorem signal_separated_at_early :
    ¬ MAIDPruningFixpointGraph.UtilityView.DConnectedUnder view
      earlyHybridParents (.base .signal) (.utility termSite) earlyEvidence := by
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
          earlyHybridParents)
        {(.base .signal)} {(.utility termSite)} earlyEvidence
        (.base .signal) next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | base node =>
          cases node <;>
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, earlyHybridParents,
              Pruning.restoreAllAt, pruning, diagram, parents, earlySite,
              earlyEvidence,
              MAIDPruningFixpointGraph.UtilityView.conditioningUnder]
              at hforward hnextOpen
      | utility term =>
          unfold DirectedEdge
            MAIDPruningFixpointGraph.UtilityView.graphParentsUnder at hforward
          rw [Finset.mem_image] at hforward
          obtain ⟨parent, hparent, equality⟩ := hforward
          fin_cases term
          have hparent : parent = .early ∨ parent = .late := by
            simpa [MAIDRequisiteObservation.UtilityView.term, view, matchTerm]
              using hparent
          have hsignal : parent = .signal :=
            UtilityView.GraphNode.base.inj equality
          rcases hparent with hearly | hlate
          · have : Node.signal = .early := hsignal.symm.trans hearly
            cases this
          · have : Node.signal = .late := hsignal.symm.trans hlate
            cases this
    · cases next with
      | base node =>
          cases node <;>
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, diagram, parents] at hbackward
      | utility term =>
          fin_cases term
          simp [DirectedEdge,
            MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
            effectiveParentsUnder, diagram, parents] at hbackward
    · obtain ⟨child, _, hsignalParent, hnextParent⟩ := hcoparents
      have hchild : child = .base .early := by
        cases child with
        | base childNode =>
            cases childNode <;>
              simp [DirectedEdge,
                MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
                effectiveParentsUnder, earlyHybridParents,
                Pruning.restoreAllAt, pruning, diagram, parents, earlySite]
                at hsignalParent ⊢
        | utility term =>
            unfold DirectedEdge
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder at hsignalParent
            rw [Finset.mem_image] at hsignalParent
            obtain ⟨parent, hparent, equality⟩ := hsignalParent
            fin_cases term
            have hparent : parent = .early ∨ parent = .late := by
              simpa [MAIDRequisiteObservation.UtilityView.term, view, matchTerm]
                using hparent
            have hsignal : parent = .signal :=
              UtilityView.GraphNode.base.inj equality
            rcases hparent with hearly | hlate
            · have : Node.signal = .early := hsignal.symm.trans hearly
              cases this
            · have : Node.signal = .late := hsignal.symm.trans hlate
              cases this
      subst child
      have hnext : next = .base .signal := by
        cases next with
        | base nextNode =>
            cases nextNode <;>
              simp [DirectedEdge,
                MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
                effectiveParentsUnder, earlyHybridParents,
                Pruning.restoreAllAt, diagram, parents, earlySite]
                at hnextParent ⊢
        | utility term =>
            fin_cases term
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, earlyHybridParents,
              Pruning.restoreAllAt, diagram, parents, earlySite]
              at hnextParent
      exact hne hnext.symm
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

def lateHybridParents : Node → Finset Node :=
  MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning lateSite

def lateEvidence : Finset (view.GraphNode ()) :=
  MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
    lateHybridParents lateSite
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning lateSite)

theorem signal_separated_at_late :
    ¬ MAIDPruningFixpointGraph.UtilityView.DConnectedUnder view
      lateHybridParents (.base .signal) (.utility termSite) lateEvidence := by
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
          lateHybridParents)
        {(.base .signal)} {(.utility termSite)} lateEvidence
        (.base .signal) next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | base node =>
          cases node <;>
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, lateHybridParents,
              Pruning.restoreAllAt, pruning, diagram, parents, lateSite,
              lateEvidence,
              MAIDPruningFixpointGraph.UtilityView.conditioningUnder]
              at hforward hnextOpen
      | utility term =>
          unfold DirectedEdge
            MAIDPruningFixpointGraph.UtilityView.graphParentsUnder at hforward
          rw [Finset.mem_image] at hforward
          obtain ⟨parent, hparent, equality⟩ := hforward
          fin_cases term
          have hparent : parent = .early ∨ parent = .late := by
            simpa [MAIDRequisiteObservation.UtilityView.term, view, matchTerm]
              using hparent
          have hsignal : parent = .signal :=
            UtilityView.GraphNode.base.inj equality
          rcases hparent with hearly | hlate
          · have : Node.signal = .early := hsignal.symm.trans hearly
            cases this
          · have : Node.signal = .late := hsignal.symm.trans hlate
            cases this
    · cases next with
      | base node =>
          cases node <;>
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, diagram, parents] at hbackward
      | utility term =>
          fin_cases term
          simp [DirectedEdge,
            MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
            effectiveParentsUnder, diagram, parents] at hbackward
    · obtain ⟨child, _, hsignalParent, hnextParent⟩ := hcoparents
      have hchild : child = .base .late := by
        cases child with
        | base childNode =>
            cases childNode <;>
              simp [DirectedEdge,
                MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
                effectiveParentsUnder, lateHybridParents,
                Pruning.restoreAllAt, pruning, diagram, parents, lateSite]
                at hsignalParent ⊢
        | utility term =>
            unfold DirectedEdge
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder at hsignalParent
            rw [Finset.mem_image] at hsignalParent
            obtain ⟨parent, hparent, equality⟩ := hsignalParent
            fin_cases term
            have hparent : parent = .early ∨ parent = .late := by
              simpa [MAIDRequisiteObservation.UtilityView.term, view, matchTerm]
                using hparent
            have hsignal : parent = .signal :=
              UtilityView.GraphNode.base.inj equality
            rcases hparent with hearly | hlate
            · have : Node.signal = .early := hsignal.symm.trans hearly
              cases this
            · have : Node.signal = .late := hsignal.symm.trans hlate
              cases this
      subst child
      have hnext : next = .base .signal ∨ next = .base .early := by
        cases next with
        | base nextNode =>
            cases nextNode <;>
              simp [DirectedEdge,
                MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
                effectiveParentsUnder, lateHybridParents,
                Pruning.restoreAllAt, diagram, parents, lateSite]
                at hnextParent ⊢
        | utility term =>
            fin_cases term
            simp [DirectedEdge,
              MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
              effectiveParentsUnder, lateHybridParents,
              Pruning.restoreAllAt, diagram, parents, lateSite]
              at hnextParent
      rcases hnext with hsignal | hearly
      · exact hne hsignal.symm
      · exact hnextOpen (by
          simp [hearly, lateEvidence,
            MAIDPruningFixpointGraph.UtilityView.conditioningUnder,
            lateHybridParents, Pruning.restoreAllAt, pruning, lateSite,
            Pruning.missingAt, diagram, parents])
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem edgeAdditionFixpoint :
    MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionFixpoint view
      pruning := by
  intro owner site
  cases owner
  rcases site with ⟨node, hkind⟩
  cases node with
  | signal => simp at hkind
  | early =>
      constructor
      · simp [Pruning.restoreAllAt, Pruning.missingAt, pruning, diagram]
      · intro term _ observation hobservation
        fin_cases term
        have hobservation : observation = .signal := by
          simpa [Pruning.missingAt, pruning, diagram, parents, earlySite]
            using hobservation
        subst observation
        exact signal_separated_at_early
  | late =>
      constructor
      · simp [Pruning.restoreAllAt, Pruning.missingAt, pruning, diagram]
      · intro term _ observation hobservation
        fin_cases term
        have hobservation : observation = .signal := by
          simpa [Pruning.missingAt, pruning, diagram, parents, lateSite]
            using hobservation
        subst observation
        exact signal_separated_at_late

/-! ## Oriented strategic relevance -/

theorem late_oriented_early :
    MAIDPruningFixpointGraph.UtilityView.OrientedRelevance view
      lateSite earlySite := by
  refine ⟨termSite, early_relevant, ?_⟩
  let graphParents :=
    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents view lateSite
  let evidence :=
    MAIDPruningFixpointGraph.UtilityView.sReachConditioning view earlySite
  let mechanismNode :
      MAIDPruningFixpointGraph.UtilityView.MechanismGraphNode view () :=
    .mechanism
  let late :
      MAIDPruningFixpointGraph.UtilityView.MechanismGraphNode view () :=
    .object (.base .late)
  let utility :
      MAIDPruningFixpointGraph.UtilityView.MechanismGraphNode view () :=
    .object (.utility termSite)
  have mechanismLate : DirectedEdge graphParents mechanismNode late := by
    simp [DirectedEdge, graphParents, mechanismNode, late,
      MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents, lateSite]
  have lateUtility : DirectedEdge graphParents late utility := by
    simp [DirectedEdge, graphParents, late, utility,
      MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
      MAIDRequisiteObservation.UtilityView.term, view, termSite, matchTerm]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
  have mechanismOpen : mechanismNode ∉ evidence := by
    simp [mechanismNode, evidence,
      MAIDPruningFixpointGraph.UtilityView.sReachConditioning]
  have lateOpen : late ∉ evidence := by
    simp [late, evidence,
      MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
      earlySite, diagram, parents]
  have utilityOpen : utility ∉ evidence := by
    simp [utility, evidence,
      MAIDPruningFixpointGraph.UtilityView.sReachConditioning]
  have mechanismAncestor :
      InAncestralClosure graphParents {mechanismNode} {utility} evidence
        mechanismNode := by
    refine ⟨mechanismNode, ?_, Relation.ReflTransGen.refl⟩
    simp [queryRoots]
  have lateAncestor :
      InAncestralClosure graphParents {mechanismNode} {utility} evidence
        late := by
    refine ⟨utility, ?_, Relation.ReflTransGen.single lateUtility⟩
    simp [queryRoots]
  have utilityAncestor :
      InAncestralClosure graphParents {mechanismNode} {utility} evidence
        utility := by
    refine ⟨utility, ?_, Relation.ReflTransGen.refl⟩
    simp [queryRoots]
  have firstStep : MoralAdjacent graphParents {mechanismNode} {utility}
      evidence mechanismNode late :=
    ⟨by simp [mechanismNode, late], mechanismOpen, lateOpen,
      mechanismAncestor, lateAncestor, Or.inl mechanismLate⟩
  have secondStep : MoralAdjacent graphParents {mechanismNode} {utility}
      evidence late utility :=
    ⟨by simp [late, utility], lateOpen, utilityOpen,
      lateAncestor, utilityAncestor, Or.inl lateUtility⟩
  refine ⟨mechanismOpen, utilityOpen, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single firstStep) secondStep

/-- The early mechanism is blocked for every possible target because the
early action, and its sole original parent, are in either target's evidence. -/
theorem early_not_oriented
    (target : DecisionSite diagram ()) :
    ¬ MAIDPruningFixpointGraph.UtilityView.OrientedRelevance view
      earlySite target := by
  rintro ⟨term, _, _, _, connection⟩
  fin_cases term
  let graphParents :=
    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents view earlySite
  let evidence :=
    MAIDPruningFixpointGraph.UtilityView.sReachConditioning view target
  let mechanismNode :
      MAIDPruningFixpointGraph.UtilityView.MechanismGraphNode view () :=
    .mechanism
  have isolated : ∀ next,
      ¬ MoralAdjacent graphParents {mechanismNode}
        {(.object (.utility termSite))} evidence mechanismNode next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | mechanism => exact hne rfl
      | object objectNode =>
          cases objectNode with
          | base node =>
              cases node with
              | signal =>
                  simp [DirectedEdge, graphParents, mechanismNode,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    earlySite, effectiveParents, diagram, parents]
                    at hforward
              | early =>
                  exact hnextOpen (by
                    rcases target with ⟨node, hkind⟩
                    cases node with
                    | signal => simp at hkind
                    | early =>
                        simp [evidence,
                          MAIDPruningFixpointGraph.UtilityView.sReachConditioning]
                    | late =>
                        simp [evidence,
                          MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
                          diagram, parents])
              | late =>
                  simp [DirectedEdge, graphParents, mechanismNode,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    earlySite, effectiveParents, diagram, parents]
                    at hforward
          | utility term =>
              fin_cases term
              simp [DirectedEdge, graphParents, mechanismNode,
                MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
                at hforward
    · cases next with
      | mechanism =>
          simp [DirectedEdge, graphParents, mechanismNode,
            MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
            at hbackward
      | object objectNode =>
          cases objectNode <;>
            simp [DirectedEdge, graphParents, mechanismNode,
              MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
              at hbackward
    · obtain ⟨child, _, hmechanismParent, hnextParent⟩ := hcoparents
      have hchild : child = .object (.base .early) := by
        cases child with
        | mechanism =>
            simp [DirectedEdge, graphParents, mechanismNode,
              MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
              at hmechanismParent
        | object objectNode =>
            cases objectNode with
            | base node =>
                cases node <;>
                  simp [DirectedEdge, graphParents, mechanismNode,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    earlySite, effectiveParents, diagram, parents]
                    at hmechanismParent ⊢
            | utility term =>
                fin_cases term
                simp [DirectedEdge, graphParents, mechanismNode,
                  MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
                  at hmechanismParent
      subst child
      have hnext : next = mechanismNode ∨
          next = .object (.base .signal) := by
        cases next with
        | mechanism => exact Or.inl rfl
        | object objectNode =>
            cases objectNode with
            | base node =>
                cases node <;>
                  simp [DirectedEdge, graphParents, mechanismNode,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    earlySite, effectiveParents, diagram, parents]
                    at hnextParent ⊢
            | utility term =>
                fin_cases term
                simp [DirectedEdge, graphParents,
                  MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                  earlySite, effectiveParents, diagram, parents]
                  at hnextParent
      rcases hnext with hmechanism | hsignal
      · exact hne hmechanism.symm
      · exact hnextOpen (by
          subst next
          rcases target with ⟨node, hkind⟩
          cases node with
          | signal => simp at hkind
          | early =>
              simp [evidence,
                MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
                diagram, parents]
          | late =>
              simp [evidence,
                MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
                diagram, parents])
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem late_not_oriented_late :
    ¬ MAIDPruningFixpointGraph.UtilityView.OrientedRelevance view
      lateSite lateSite := by
  rintro ⟨term, _, _, _, connection⟩
  fin_cases term
  let graphParents :=
    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents view lateSite
  let evidence :=
    MAIDPruningFixpointGraph.UtilityView.sReachConditioning view lateSite
  let mechanismNode :
      MAIDPruningFixpointGraph.UtilityView.MechanismGraphNode view () :=
    .mechanism
  have isolated : ∀ next,
      ¬ MoralAdjacent graphParents {mechanismNode}
        {(.object (.utility termSite))} evidence mechanismNode next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | mechanism => exact hne rfl
      | object objectNode =>
          cases objectNode with
          | base node =>
              cases node with
              | signal =>
                  simp [DirectedEdge, graphParents,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    lateSite, effectiveParents, diagram, parents] at hforward
              | early =>
                  simp [DirectedEdge, graphParents,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    lateSite, effectiveParents, diagram, parents] at hforward
              | late =>
                  exact hnextOpen (by
                    simp [evidence,
                      MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
                      lateSite])
          | utility term =>
              fin_cases term
              simp [DirectedEdge, graphParents,
                MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
                at hforward
    · cases next with
      | mechanism =>
          simp [DirectedEdge, graphParents, mechanismNode,
            MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
            at hbackward
      | object objectNode =>
          cases objectNode <;>
            simp [DirectedEdge, graphParents, mechanismNode,
              MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
              at hbackward
    · obtain ⟨child, _, hmechanismParent, hnextParent⟩ := hcoparents
      have hchild : child = .object (.base .late) := by
        cases child with
        | mechanism =>
            simp [DirectedEdge, graphParents,
              MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
              at hmechanismParent
        | object objectNode =>
            cases objectNode with
            | base node =>
                cases node <;>
                  simp [DirectedEdge, graphParents,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    lateSite, effectiveParents, diagram, parents]
                    at hmechanismParent ⊢
            | utility term =>
                fin_cases term
                simp [DirectedEdge, graphParents,
                  MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents]
                  at hmechanismParent
      subst child
      have hnext : next = mechanismNode ∨
          next = .object (.base .signal) ∨
          next = .object (.base .early) := by
        cases next with
        | mechanism => exact Or.inl rfl
        | object objectNode =>
            cases objectNode with
            | base node =>
                cases node <;>
                  simp [DirectedEdge, graphParents,
                    MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                    lateSite, effectiveParents, diagram, parents]
                    at hnextParent ⊢
            | utility term =>
                fin_cases term
                simp [DirectedEdge, graphParents,
                  MAIDPruningFixpointGraph.UtilityView.mechanismGraphParents,
                  lateSite, effectiveParents, diagram, parents]
                  at hnextParent
      rcases hnext with hmechanism | hsignal | hearly
      · exact hne hmechanism.symm
      · exact hnextOpen (by
          subst next
          simp [evidence,
            MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
            lateSite, diagram, parents])
      · exact hnextOpen (by
          subst next
          simp [evidence,
            MAIDPruningFixpointGraph.UtilityView.sReachConditioning,
            lateSite, diagram, parents])
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem oriented_only_late_early
    (source target : DecisionSite diagram ())
    (edge : MAIDPruningFixpointGraph.UtilityView.OrientedRelevance view
      source target) :
    source = lateSite ∧ target = earlySite := by
  rcases source with ⟨source, hsource⟩
  rcases target with ⟨target, htarget⟩
  cases source with
  | signal => simp at hsource
  | early =>
      exact (early_not_oriented ⟨target, htarget⟩ edge).elim
  | late =>
      cases target with
      | signal => simp at htarget
      | early => exact ⟨rfl, rfl⟩
      | late => exact (late_not_oriented_late edge).elim

theorem sReachAcyclic :
    MAIDPruningFixpointGraph.UtilityView.SReachAcyclic view := by
  intro owner vertex cycle
  cases owner
  obtain ⟨next, firstEdge, remaining⟩ :=
    Relation.TransGen.head'_iff.mp cycle
  have firstShape := oriented_only_late_early vertex next firstEdge
  rcases firstShape with ⟨hvertex, hnext⟩
  subst vertex
  subst next
  rcases Relation.ReflTransGen.cases_head remaining with
    equality | ⟨after, edge, _⟩
  · cases equality
  · exact early_not_oriented after edge

/-! ## Canonical semantic certificate -/

def reducedPolicy : pruning.ReducedPolicy :=
  fun _ site observed =>
    match hnode : site.1 with
    | .signal => by
        have hkind := site.2
        simp [diagram, hnode] at hkind
    | .early => FinDist.pure false
    | .late =>
        FinDist.pure (observed ⟨.early, by simp [pruning, hnode]⟩)

def assignmentOf (signal early late : Bool) : Assignment diagram
  | .signal => signal
  | .early => early
  | .late => late

def earlyConfig (signal : Bool) :
    Config diagram (diagram.observedParents .early) :=
  Assignment.restrict diagram (assignmentOf signal false false)
    (diagram.observedParents .early)

def lateConfig (signal early : Bool) :
    Config diagram (diagram.observedParents .late) :=
  Assignment.restrict diagram (assignmentOf signal early false)
    (diagram.observedParents .late)

theorem expanded_early_rule (signal : Bool) :
    pruning.expandPolicy reducedPolicy () earlySite (earlyConfig signal) =
      FinDist.pure false := by
  rfl

theorem expanded_late_rule (signal early : Bool) :
    pruning.expandPolicy reducedPolicy () lateSite
        (lateConfig signal early) =
      FinDist.pure early := by
  rfl

theorem restrict_at_early (signal : Bool) :
    Assignment.restrict diagram
        (Stage.Assignment.setOne semantics.defaultValue ⟨.signal, signal⟩)
        (diagram.observedParents .early) =
      earlyConfig signal := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, earlyConfig,
      Stage.Assignment.setOne, Assignment.resolve, assignmentOf] at hnode ⊢

theorem restrict_at_late (signal early : Bool) :
    Assignment.restrict diagram
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne semantics.defaultValue ⟨.signal, signal⟩)
          ⟨.early, early⟩)
        (diagram.observedParents .late) =
      lateConfig signal early := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, parents, Assignment.restrict, lateConfig,
      Stage.Assignment.setOne, Assignment.resolve, assignmentOf] at hnode ⊢

theorem set_late (signal early late : Bool) :
    Stage.Assignment.setOne
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne semantics.defaultValue ⟨.signal, signal⟩)
          ⟨.early, early⟩)
        ⟨.late, late⟩ =
      assignmentOf signal early late := by
  funext node
  cases node <;>
    simp [Stage.Assignment.setOne, Assignment.resolve, assignmentOf]

theorem assignmentNodeLaw_signal (policy : Policy diagram)
    (assignment : Assignment diagram) :
    assignmentNodeLaw semantics policy assignment .signal = fairSignal := by
  rfl

theorem assignmentNodeLaw_early (signal : Bool) (policy : Policy diagram) :
    assignmentNodeLaw semantics policy
        (Stage.Assignment.setOne semantics.defaultValue ⟨.signal, signal⟩)
        .early =
      policy () earlySite (earlyConfig signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy () earlySite) (restrict_at_early signal)

theorem assignmentNodeLaw_late (signal early : Bool)
    (policy : Policy diagram) :
    assignmentNodeLaw semantics policy
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne semantics.defaultValue ⟨.signal, signal⟩)
          ⟨.early, early⟩) .late =
      policy () lateSite (lateConfig signal early) := by
  unfold assignmentNodeLaw
  exact congrArg (policy () lateSite) (restrict_at_late signal early)

theorem expanded_play :
    (nativeBehavioralGameForm semantics).play
        (pruning.expandPolicy reducedPolicy) =
      fairSignal.map fun signal => assignmentOf signal false false := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological semantics
      (pruning.expandPolicy reducedPolicy)]
  show assignmentRun semantics (pruning.expandPolicy reducedPolicy)
      [.signal, .early, .late] semantics.defaultValue = _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_signal,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro signal _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_early,
    expanded_early_rule, FinDist.map_pure, FinDist.pure_bind]
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_late,
    expanded_late_rule, FinDist.map_pure, FinDist.pure_bind]
  rw [assignmentRun]
  exact congrArg FinDist.pure (set_late signal false false)

theorem expanded_expectedUtility :
    expectedUtility
        (fun assignment owner => semantics.utility owner assignment) ()
        ((nativeBehavioralGameForm semantics).play
          (pruning.expandPolicy reducedPolicy)) = 1 := by
  unfold expectedUtility
  rw [expanded_play, FinDist.expect_map]
  calc
    fairSignal.expect (fun signal =>
        (fun assignment owner => semantics.utility owner assignment)
          (assignmentOf signal false false) ()) =
        fairSignal.expect (fun _ => 1) := by
      apply FinDist.expect_congr
      intro signal _
      simp [assignmentOf]
    _ = 1 := FinDist.expect_const fairSignal 1

theorem expectedUtility_le_one (policy : Policy diagram) :
    expectedUtility
        (fun assignment owner => semantics.utility owner assignment) ()
        ((nativeBehavioralGameForm semantics).play policy) ≤ 1 := by
  unfold expectedUtility
  apply FinDist.expect_le_of_forall
  intro assignment _
  by_cases hmatch : assignment .early = assignment .late <;>
    simp [hmatch]

theorem coversFullDeviations :
    pruning.CoversFullDeviationsAt semantics reducedPolicy := by
  intro owner fullReplacement
  refine ⟨reducedPolicy owner, ?_⟩
  rw [euPreference_apply, Profile.update_eq_self,
    expanded_expectedUtility]
  exact expectedUtility_le_one _

theorem generic_coversFullDeviations :
    pruning.CoversFullDeviationsAt semantics reducedPolicy :=
  MAIDPruningGlobalReduction.coversFullDeviationsAt_of_edgeAdditionFixpoint
    pruning topological semantics reducedPolicy view sReachAcyclic
    edgeAdditionFixpoint

theorem reduced_isNash :
    IsNash (pruning.reducedNativeGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      reducedPolicy := by
  rw [isNash_iff]
  intro owner replacement
  rw [euPreference_apply, expanded_expectedUtility]
  exact expectedUtility_le_one _

theorem expanded_isNash :
    IsNash (nativeBehavioralGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      (pruning.expandPolicy reducedPolicy) :=
  pruning.isNash_expanded_of_isNash_reduced semantics reducedPolicy
    coversFullDeviations reduced_isNash

end GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointPositiveTest
