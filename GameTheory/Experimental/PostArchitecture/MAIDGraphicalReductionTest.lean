/-
# EXP-105: hostile consumer for graphical MAID reduction

Two distinct utility leaves separate coordination from a signal-only
background payoff.  When the rival ignores the signal, conditioning on the
owner's decision blocks the signal from the coordination leaf.  When the
rival relays the signal, the open route through the rival makes the same
observation requisite and enables a profitable full deviation.
-/

import GameTheory.Experimental.PostArchitecture.MAIDGraphicalReduction

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDGraphicalReductionTest

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Experimental.PostArchitecture.MAIDGraphicalReduction
open GameTheory.Experimental.PostArchitecture.MAIDLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

inductive Player
  | owner
  | rival
  deriving DecidableEq, Fintype

inductive Node
  | signal
  | ownerDecision
  | rivalDecision
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .signal => ∅
  | .ownerDecision => {.signal}
  | .rivalDecision => {.signal}

def observedParents (relay : Bool) : Node → Finset Node
  | .signal => ∅
  | .ownerDecision => {.signal}
  | .rivalDecision => if relay then {.signal} else ∅

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .ownerDecision, .rivalDecision]
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
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩

@[reducible]
def diagram (relay : Bool) : Structure Player Node where
  kind
    | .signal => .chance
    | .ownerDecision => .decision .owner
    | .rivalDecision => .decision .rival
  parents := parents
  observedParents := observedParents relay
  Value _ := Bool
  observed_sub node := by
    cases node <;> simp [parents, observedParents]
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents, observedParents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

def topological (relay : Bool) :
    GameTheory.Math.DAG.TopologicalOrder (diagram relay).parents :=
  topologicalParents

def fairSignal : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem fairSignal_expect (score : Bool → ℝ) :
    fairSignal.expect score = (score false + score true) / 2 := by
  rw [fairSignal, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure]
  ring

def bitScore (value : Bool) : ℝ := if value then 1 else 0

def coordinationScore (first second : Bool) : ℝ :=
  if first = second then 1 else 0

@[reducible]
def semantics (relay : Bool) : Semantics (diagram relay) where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact fairSignal
    | ownerDecision => simp at hchance
    | rivalDecision => simp at hchance
  utility player assignment :=
    match player with
    | .owner =>
        coordinationScore (assignment .ownerDecision)
          (assignment .rivalDecision) + bitScore (assignment .signal)
    | .rival => 0

def coordinationTerm (relay : Bool) : UtilityTerm (diagram relay) where
  parents := {.ownerDecision, .rivalDecision}
  payoff configuration :=
    coordinationScore
      (configuration ⟨.ownerDecision, by simp⟩)
      (configuration ⟨.rivalDecision, by simp⟩)

def backgroundTerm (relay : Bool) : UtilityTerm (diagram relay) where
  parents := {.signal}
  payoff configuration := bitScore (configuration ⟨.signal, by simp⟩)

def utilityView (relay : Bool) : UtilityView (semantics relay) where
  terms
    | .owner => [coordinationTerm relay, backgroundTerm relay]
    | .rival => []
  utility_eq_sum player assignment := by
    cases player
    · simp [coordinationTerm, backgroundTerm, UtilityTerm.value,
        Assignment.restrict]
    · simp

def coordinationSite (relay : Bool) :
    (utilityView relay).UtilitySite .owner :=
  ⟨0, by simp [utilityView]⟩

def backgroundSite (relay : Bool) :
    (utilityView relay).UtilitySite .owner :=
  ⟨1, by simp [utilityView]⟩

private theorem utilitySite_cases (relay : Bool)
    (site : (utilityView relay).UtilitySite .owner) :
    site = coordinationSite relay ∨ site = backgroundSite relay := by
  fin_cases site
  · exact Or.inl (Fin.ext rfl)
  · exact Or.inr (Fin.ext rfl)

def ownerSite (relay : Bool) : DecisionSite (diagram relay) .owner :=
  ⟨.ownerDecision, rfl⟩

def rivalSite (relay : Bool) : DecisionSite (diagram relay) .rival :=
  ⟨.rivalDecision, rfl⟩

/-- Remove the signal only from the owner's decision. -/
def pruning (relay : Bool) : Pruning (diagram relay) where
  kept
    | .signal => ∅
    | .ownerDecision => ∅
    | .rivalDecision => observedParents relay .rivalDecision
  kept_sub_observed node := by
    cases node <;> simp [observedParents]

theorem pruning_kept_owner (relay : Bool) :
    (pruning relay).kept (ownerSite relay).1 = ∅ := by
  rfl

theorem singleSiteShape (relay : Bool) :
    IsSingleSitePruningAt (pruning relay) .owner (ownerSite relay) := by
  refine ⟨?_, ?_⟩
  · intro site
    apply Subtype.ext
    rcases site with ⟨node, hnode⟩
    cases node <;> simp [diagram, ownerSite] at hnode ⊢
  · intro other hother site
    cases other with
    | owner => exact (hother rfl).elim
    | rival =>
        rcases site with ⟨node, hnode⟩
        cases node <;>
          simp [diagram, pruning, observedParents] at hnode ⊢

theorem coordination_relevant (relay : Bool) :
    (utilityView relay).IsRelevantUtilityTerm (ownerSite relay)
      (coordinationSite relay) := by
  apply Relation.TransGen.single
  show (.base .ownerDecision :
      UtilityView.GraphNode (utilityView relay) .owner) ∈
    ((utilityView relay).term (coordinationSite relay)).parents.image
      UtilityView.GraphNode.base
  apply Finset.mem_image.mpr
  exact ⟨.ownerDecision, by simp [UtilityView.term, utilityView,
    coordinationSite, coordinationTerm], rfl⟩

theorem background_not_relevant (relay : Bool) :
    ¬ (utilityView relay).IsRelevantUtilityTerm (ownerSite relay)
      (backgroundSite relay) := by
  intro relevant
  have relevant' : Relation.TransGen (utilityView relay).DirectedEdge
      (.base (ownerSite relay).1) (.utility (backgroundSite relay)) :=
    relevant
  rw [Relation.TransGen.tail'_iff] at relevant'
  obtain ⟨before, path, lastEdge⟩ := relevant'
  have lastEdge' : before ∈
      ((utilityView relay).term (backgroundSite relay)).parents.image
        UtilityView.GraphNode.base := lastEdge
  have hbefore : before = .base .signal := by
    obtain ⟨node, hnode, equality⟩ := Finset.mem_image.mp lastEdge'
    have hsignal : node = .signal := by
      simpa [UtilityView.term, utilityView, backgroundSite, backgroundTerm]
        using hnode
    subst node
    exact equality.symm
  subst before
  rcases Relation.ReflTransGen.cases_tail path with equality | ⟨_, _, edge⟩
  · have impossible : Node.signal = .ownerDecision :=
      UtilityView.GraphNode.base.inj equality
    cases impossible
  · simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, diagram, parents] at edge

private theorem safe_background_not_in_coordination_closure :
    ¬ (utilityView false).InAncestralClosure
      (.base .signal) (.utility (coordinationSite false))
      ((utilityView false).observationConditioningSet
        (ownerSite false) {.signal})
      (.utility (backgroundSite false)) := by
  have noOutgoing : ∀ next,
      ¬ (utilityView false).DirectedEdge
        (.utility (backgroundSite false)) next := by
    intro next edge
    cases next with
    | base node =>
        obtain ⟨_, _, equality⟩ := Finset.mem_image.mp edge
        cases equality
    | utility site =>
        obtain ⟨_, _, equality⟩ := Finset.mem_image.mp edge
        cases equality
  rintro ⟨root, hroot, path⟩
  rcases Relation.ReflTransGen.cases_head path with equality | ⟨next, edge, _⟩
  · subst root
    simp [UtilityView.observationConditioningSet, ownerSite,
      coordinationSite, backgroundSite] at hroot
  · exact noOutgoing next edge

private theorem safe_signal_not_connected :
    ¬ (utilityView false).DConnected
      (.base .signal) (.utility (coordinationSite false))
      ((utilityView false).observationConditioningSet
        (ownerSite false) {.signal}) := by
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ (utilityView false).MoralAdjacent
        (.base .signal) (.utility (coordinationSite false))
        ((utilityView false).observationConditioningSet
          (ownerSite false) {.signal})
        (.base .signal) next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, hnextClosure,
        hforward | hbackward | hcoparents⟩
    · cases next with
      | base node =>
          cases node with
          | signal => exact hne rfl
          | ownerDecision =>
              apply hnextOpen
              simp [UtilityView.observationConditioningSet, ownerSite]
          | rivalDecision =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, diagram, observedParents] at hforward
      | utility site =>
          rcases utilitySite_cases false site with hsite | hsite
          · subst site
            have hterm : (utilityView false).term
                (coordinationSite false) = coordinationTerm false := rfl
            have hforward' :
                (.base .signal : UtilityView.GraphNode
                    (utilityView false) .owner) ∈
                  ((utilityView false).term
                    (coordinationSite false)).parents.image
                    UtilityView.GraphNode.base := by
              simpa only [UtilityView.DirectedEdge,
                UtilityView.graphParents] using hforward
            rw [hterm] at hforward'
            simp [coordinationTerm] at hforward'
          · subst site
            exact safe_background_not_in_coordination_closure hnextClosure
    · simp [UtilityView.DirectedEdge, UtilityView.graphParents,
        effectiveParents, diagram, parents] at hbackward
    · obtain ⟨child, _, hsignalParent, hnextParent⟩ := hcoparents
      cases child with
      | base node =>
          cases node with
          | signal =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, diagram, parents] at hsignalParent
          | ownerDecision =>
              have hnext : next = .base .signal := by
                have hnextParent' : next ∈
                    ((effectiveParents (diagram false) .ownerDecision).image
                      UtilityView.GraphNode.base) := hnextParent
                obtain ⟨node, hnode, equality⟩ :=
                  Finset.mem_image.mp hnextParent'
                have hsignal : node = .signal := by
                  simpa [effectiveParents, diagram, observedParents]
                    using hnode
                subst node
                exact equality.symm
              exact hne hnext.symm
          | rivalDecision =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, diagram, observedParents] at hsignalParent
      | utility site =>
          rcases utilitySite_cases false site with hsite | hsite
          · subst site
            have hterm : (utilityView false).term
                (coordinationSite false) = coordinationTerm false := rfl
            have hsignalParent' :
                (.base .signal : UtilityView.GraphNode
                    (utilityView false) .owner) ∈
                  ((utilityView false).term
                    (coordinationSite false)).parents.image
                    UtilityView.GraphNode.base := by
              simpa only [UtilityView.DirectedEdge,
                UtilityView.graphParents] using hsignalParent
            rw [hterm] at hsignalParent'
            simp [coordinationTerm] at hsignalParent'
          · subst site
            have hnext : next = .base .signal := by
              have hnextParent' : next ∈
                  ((utilityView false).term (backgroundSite false)).parents.image
                    UtilityView.GraphNode.base := hnextParent
              obtain ⟨node, hnode, equality⟩ :=
                Finset.mem_image.mp hnextParent'
              have hsignal : node = .signal := by
                simpa [UtilityView.term, utilityView, backgroundSite,
                  backgroundTerm] using hnode
              subst node
              exact equality.symm
            exact hne hnext.symm
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

/-- With a signal-blind rival, the removed set is graphically ignorable. -/
theorem safe_graphicallyIgnorable :
    (utilityView false).AreGraphicallyIgnorable (ownerSite false)
      ((diagram false).observedParents (ownerSite false).1 \
        (pruning false).kept (ownerSite false).1) := by
  refine ⟨by simp [diagram, observedParents, pruning, ownerSite], ?_⟩
  intro term relevant observation hobservation
  have hsignal : observation = .signal := by
    simpa [diagram, observedParents, pruning, ownerSite] using hobservation
  subst observation
  have hterm : term = coordinationSite false ∨
      term = backgroundSite false := by
    fin_cases term
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Fin.ext rfl)
  rcases hterm with hterm | hterm
  · subst term
    exact safe_signal_not_connected
  · subst term
    exact (background_not_relevant false relevant).elim

def constantReducedPolicy (relay : Bool) : (pruning relay).ReducedPolicy :=
  fun _ _ _ => FinDist.pure false

/-- The positive fixture consumes the complete graphical-to-semantic bridge. -/
theorem safe_coversFullDeviations :
    (pruning false).CoversFullDeviationsAt (semantics false)
      (constantReducedPolicy false) :=
  coversFullDeviationsAt_of_graphicallyIgnorable (pruning false)
    (topological false) (semantics false) (constantReducedPolicy false)
    .owner (ownerSite false) (singleSiteShape false) (utilityView false)
    safe_graphicallyIgnorable

/-- At the graphically certified profile, reduced and expanded Nash questions
coincide through the canonical safe-reduction theorem. -/
theorem safe_nash_transfer :
    IsNash (nativeBehavioralGameForm (semantics false))
        (euPreference fun assignment player =>
          (semantics false).utility player assignment)
        ((pruning false).expandPolicy (constantReducedPolicy false)) ↔
      IsNash ((pruning false).reducedNativeGameForm (semantics false))
        (euPreference fun assignment player =>
          (semantics false).utility player assignment)
        (constantReducedPolicy false) :=
  (pruning false).isNash_expanded_iff_reducedNative_of_covers
    (semantics false) (constantReducedPolicy false)
    safe_coversFullDeviations

/-! ## Relay control: the removed observation is graphically live -/

theorem relay_signal_requisite :
    (utilityView true).IsRequisiteObservation (ownerSite true) .signal := by
  have signalRival : (utilityView true).DirectedEdge
      (owner := .owner) (.base .signal) (.base .rivalDecision) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, diagram, observedParents]
  have rivalCoordination : (utilityView true).DirectedEdge
      (.base .rivalDecision) (.utility (coordinationSite true)) := by
    show (.base .rivalDecision :
        UtilityView.GraphNode (utilityView true) .owner) ∈
      ((utilityView true).term (coordinationSite true)).parents.image
        UtilityView.GraphNode.base
    apply Finset.mem_image.mpr
    exact ⟨.rivalDecision, by simp [UtilityView.term, utilityView,
      coordinationSite, coordinationTerm], rfl⟩
  have sourceClosure : (utilityView true).InAncestralClosure
      (.base .signal) (.utility (coordinationSite true))
      ((utilityView true).observationConditioning
        (ownerSite true) .signal)
      (.base .signal) :=
    ⟨.base .signal, by simp, Relation.ReflTransGen.refl⟩
  have rivalClosure : (utilityView true).InAncestralClosure
      (.base .signal) (.utility (coordinationSite true))
      ((utilityView true).observationConditioning
        (ownerSite true) .signal)
      (.base .rivalDecision) :=
    ⟨.utility (coordinationSite true), by simp,
      Relation.ReflTransGen.single rivalCoordination⟩
  have utilityClosure : (utilityView true).InAncestralClosure
      (.base .signal) (.utility (coordinationSite true))
      ((utilityView true).observationConditioning
        (ownerSite true) .signal)
      (.utility (coordinationSite true)) :=
    ⟨.utility (coordinationSite true), by simp,
      Relation.ReflTransGen.refl⟩
  have signalRivalMoral : (utilityView true).MoralAdjacent
      (.base .signal) (.utility (coordinationSite true))
      ((utilityView true).observationConditioning
        (ownerSite true) .signal)
      (.base .signal) (.base .rivalDecision) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, ownerSite, diagram,
        observedParents],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, ownerSite, diagram,
        observedParents],
      sourceClosure, rivalClosure, Or.inl signalRival⟩
  have rivalUtilityMoral : (utilityView true).MoralAdjacent
      (.base .signal) (.utility (coordinationSite true))
      ((utilityView true).observationConditioning
        (ownerSite true) .signal)
      (.base .rivalDecision) (.utility (coordinationSite true)) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, ownerSite, diagram,
        observedParents],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, ownerSite, diagram,
        observedParents],
      rivalClosure, utilityClosure, Or.inl rivalCoordination⟩
  refine ⟨by simp [diagram, observedParents, ownerSite],
    coordinationSite true, coordination_relevant true, ?_⟩
  refine ⟨by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, ownerSite],
    by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, ownerSite], ?_⟩
  exact Relation.ReflTransGen.head signalRivalMoral
    (Relation.ReflTransGen.single rivalUtilityMoral)

/-- Relaying the signal gives the active coordination route, so graphical
ignorability correctly rejects the unsafe pruning. -/
theorem relay_not_graphicallyIgnorable :
    ¬ (utilityView true).AreGraphicallyIgnorable (ownerSite true)
      ((diagram true).observedParents (ownerSite true).1 \
        (pruning true).kept (ownerSite true).1) := by
  have hnot :=
    ((utilityView true).isRequisiteObservation_iff_not_areGraphicallyIgnorable
      (ownerSite true) .signal
      (by simp [diagram, observedParents, ownerSite])).mp
      relay_signal_requisite
  simpa [diagram, observedParents, pruning, ownerSite] using hnot

/-! ## Canonical semantic counterexample -/

def ownerObservation (signal : Bool) :
    Config (diagram true)
      ((diagram true).observedParents (ownerSite true).1) :=
  fun _ => signal

def rivalObservation (signal : Bool) :
    Config (diagram true)
      ((diagram true).observedParents (rivalSite true).1) :=
  fun _ => signal

def assignmentOf (signal ownerAction rivalAction : Bool) :
    Assignment (diagram true)
  | .signal => signal
  | .ownerDecision => ownerAction
  | .rivalDecision => rivalAction

theorem restrict_owner_after_signal (signal : Bool) :
    Assignment.restrict (diagram true)
        (Stage.Assignment.setOne (semantics true).defaultValue
          ⟨.signal, signal⟩)
        ((diagram true).observedParents .ownerDecision) =
      ownerObservation signal := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, observedParents, Assignment.restrict, ownerObservation,
      Stage.Assignment.setOne, Assignment.resolve] at hnode ⊢

theorem restrict_rival_after_owner (signal ownerAction : Bool) :
    Assignment.restrict (diagram true)
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne (semantics true).defaultValue
            ⟨.signal, signal⟩)
          ⟨.ownerDecision, ownerAction⟩)
        ((diagram true).observedParents .rivalDecision) =
      rivalObservation signal := by
  funext node
  rcases node with ⟨node, hnode⟩
  cases node <;>
    simp [diagram, observedParents, Assignment.restrict, rivalObservation,
      Stage.Assignment.setOne, Assignment.resolve] at hnode ⊢

theorem set_rival_after_owner (signal ownerAction rivalAction : Bool) :
    Stage.Assignment.setOne
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne (semantics true).defaultValue
            ⟨.signal, signal⟩)
          ⟨.ownerDecision, ownerAction⟩)
        ⟨.rivalDecision, rivalAction⟩ =
      assignmentOf signal ownerAction rivalAction := by
  funext node
  cases node <;>
    simp [Stage.Assignment.setOne, Assignment.resolve, assignmentOf]

theorem assignmentNodeLaw_signal (policy : Policy (diagram true))
    (assignment : Assignment (diagram true)) :
    assignmentNodeLaw (semantics true) policy assignment .signal =
      fairSignal := by
  rfl

theorem assignmentNodeLaw_owner_after_signal
    (signal : Bool) (policy : Policy (diagram true)) :
    assignmentNodeLaw (semantics true) policy
        (Stage.Assignment.setOne (semantics true).defaultValue
          ⟨.signal, signal⟩) .ownerDecision =
      policy .owner (ownerSite true) (ownerObservation signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy .owner (ownerSite true))
    (restrict_owner_after_signal signal)

theorem assignmentNodeLaw_rival_after_owner
    (signal ownerAction : Bool) (policy : Policy (diagram true)) :
    assignmentNodeLaw (semantics true) policy
        (Stage.Assignment.setOne
          (Stage.Assignment.setOne (semantics true).defaultValue
            ⟨.signal, signal⟩)
          ⟨.ownerDecision, ownerAction⟩) .rivalDecision =
      policy .rival (rivalSite true) (rivalObservation signal) := by
  unfold assignmentNodeLaw
  exact congrArg (policy .rival (rivalSite true))
    (restrict_rival_after_owner signal ownerAction)

/-- The canonical native evaluator specializes to the three-stage fair
signal experiment; this is a theorem about `assignmentRun`, not a new
evaluator. -/
theorem relay_native_play_eq (policy : Policy (diagram true)) :
    (nativeBehavioralGameForm (semantics true)).play policy =
      fairSignal.bind fun signal =>
        (policy .owner (ownerSite true) (ownerObservation signal)).bind
          fun ownerAction =>
            (policy .rival (rivalSite true) (rivalObservation signal)).map
              (assignmentOf signal ownerAction) := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun (topological true)
      (semantics true) policy]
  show assignmentRun (semantics true) policy
      [.signal, .ownerDecision, .rivalDecision]
        (semantics true).defaultValue = _
  rw [assignmentRun, assignmentStep, assignmentNodeLaw_signal,
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro signal _
  rw [assignmentRun, assignmentStep,
    assignmentNodeLaw_owner_after_signal, FinDist.bind_map]
  apply FinDist.bind_congr
  intro ownerAction _
  rw [assignmentRun, assignmentStep,
    assignmentNodeLaw_rival_after_owner, FinDist.bind_map]
  apply FinDist.bind_congr
  intro rivalAction _
  rw [assignmentRun]
  exact congrArg FinDist.pure
    (set_rival_after_owner signal ownerAction rivalAction)

theorem relay_owner_expectedUtility (policy : Policy (diagram true)) :
    expectedUtility
        (fun assignment player => (semantics true).utility player assignment)
        .owner ((nativeBehavioralGameForm (semantics true)).play policy) =
      fairSignal.expect fun signal =>
        (policy .owner (ownerSite true) (ownerObservation signal)).expect
          fun ownerAction =>
            (policy .rival (rivalSite true) (rivalObservation signal)).expect
              fun rivalAction =>
                coordinationScore ownerAction rivalAction + bitScore signal := by
  unfold expectedUtility
  rw [relay_native_play_eq, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _
  rw [FinDist.expect_bind]
  apply FinDist.expect_congr
  intro ownerAction _
  rw [FinDist.expect_map]
  rfl

def relayReducedPolicy : (pruning true).ReducedPolicy := by
  intro player site observed
  cases player with
  | owner => exact FinDist.pure false
  | rival =>
      have hsite : site = rivalSite true := by
        apply Subtype.ext
        rcases site with ⟨node, hnode⟩
        cases node <;> simp [diagram, rivalSite] at hnode ⊢
      subst site
      exact FinDist.pure
        (observed ⟨.signal, by simp [pruning, observedParents, rivalSite]⟩)

def ownerCopiesSignal : OwnerPolicy (diagram true) .owner := by
  intro site observed
  have hsite : site = ownerSite true := by
    apply Subtype.ext
    rcases site with ⟨node, hnode⟩
    cases node <;> simp [diagram, ownerSite] at hnode ⊢
  subst site
  exact FinDist.pure
    (observed ⟨.signal, by simp [diagram, observedParents, ownerSite]⟩)

@[simp]
theorem ownerCopiesSignal_apply (signal : Bool) :
    ownerCopiesSignal (ownerSite true) (ownerObservation signal) =
      FinDist.pure signal := by
  rfl

@[simp]
theorem relayReducedPolicy_rival (signal : Bool) :
    (pruning true).expandPolicy relayReducedPolicy .rival
        (rivalSite true) (rivalObservation signal) =
      FinDist.pure signal := by
  apply congrArg FinDist.pure
  rfl

@[simp]
theorem updated_full_owner_copy (signal : Bool) :
    (Profile.update (sig := nativeBehavioralSignature (diagram true))
        ((pruning true).expandPolicy relayReducedPolicy)
        Player.owner ownerCopiesSignal) Player.owner (ownerSite true)
        (ownerObservation signal) =
      FinDist.pure signal := by
  simp

@[simp]
theorem updated_full_rival_relay (signal : Bool) :
    (Profile.update (sig := nativeBehavioralSignature (diagram true))
        ((pruning true).expandPolicy relayReducedPolicy)
        Player.owner ownerCopiesSignal) Player.rival (rivalSite true)
        (rivalObservation signal) =
      FinDist.pure signal := by
  have hupdate :
      (Profile.update (sig := nativeBehavioralSignature (diagram true))
        ((pruning true).expandPolicy relayReducedPolicy)
        Player.owner ownerCopiesSignal) Player.rival =
      (pruning true).expandPolicy relayReducedPolicy Player.rival :=
    by
      apply Profile.update_of_ne
      exact (by decide : Player.rival ≠ Player.owner)
  rw [hupdate]
  exact relayReducedPolicy_rival signal

theorem relay_copy_expectedUtility :
    expectedUtility
        (fun assignment player => (semantics true).utility player assignment)
        .owner
        ((nativeBehavioralGameForm (semantics true)).play
          (Profile.update (sig := nativeBehavioralSignature (diagram true))
            ((pruning true).expandPolicy relayReducedPolicy)
            Player.owner ownerCopiesSignal)) =
      3 / 2 := by
  rw [relay_owner_expectedUtility, fairSignal_expect]
  simp [coordinationScore, bitScore]
  norm_num

theorem expanded_reduced_owner_blind
    (replacement : (pruning true).ReducedOwnerPolicy Player.owner)
    (first second : Bool) :
    (pruning true).expandPolicy
        (Profile.update (sig := (pruning true).reducedBehavioralSignature)
          relayReducedPolicy Player.owner replacement)
        Player.owner
        (ownerSite true) (ownerObservation first) =
      (pruning true).expandPolicy
        (Profile.update (sig := (pruning true).reducedBehavioralSignature)
          relayReducedPolicy Player.owner replacement)
        Player.owner
        (ownerSite true) (ownerObservation second) := by
  unfold Pruning.expandPolicy Pruning.expandOwnerPolicy
  apply congrArg (replacement (ownerSite true))
  funext node
  have hzero : ((pruning true).kept (ownerSite true).1).card = 0 :=
    congrArg Finset.card (pruning_kept_owner true)
  have hpositive : 0 < ((pruning true).kept (ownerSite true).1).card :=
    Finset.card_pos.mpr ⟨node.1, node.2⟩
  omega

@[simp]
theorem expanded_updated_reduced_rival
    (replacement : (pruning true).ReducedOwnerPolicy Player.owner)
    (signal : Bool) :
    (pruning true).expandPolicy
        (Profile.update (sig := (pruning true).reducedBehavioralSignature)
          relayReducedPolicy Player.owner replacement)
        Player.rival (rivalSite true) (rivalObservation signal) =
      FinDist.pure signal := by
  have hupdate :
      (Profile.update (sig := (pruning true).reducedBehavioralSignature)
        relayReducedPolicy Player.owner replacement) Player.rival =
      relayReducedPolicy Player.rival :=
    by
      apply Profile.update_of_ne
      exact (by decide : Player.rival ≠ Player.owner)
  unfold Pruning.expandPolicy
  rw [hupdate]
  exact relayReducedPolicy_rival signal

theorem expect_coordination_false_add_true (law : FinDist Bool) :
    law.expect (fun action => coordinationScore action false) +
        law.expect (fun action => coordinationScore action true) =
      1 := by
  rw [← FinDist.expect_add]
  calc
    law.expect (fun action =>
        coordinationScore action false + coordinationScore action true) =
        law.expect (fun _ => 1) := by
      apply FinDist.expect_congr
      intro action _
      cases action <;> norm_num [coordinationScore]
    _ = 1 := FinDist.expect_const law 1

theorem reduced_owner_replacement_expectedUtility
    (replacement : (pruning true).ReducedOwnerPolicy Player.owner) :
    expectedUtility
        (fun assignment player => (semantics true).utility player assignment)
        .owner
        (((pruning true).reducedNativeGameForm (semantics true)).play
          (Profile.update (sig := (pruning true).reducedBehavioralSignature)
            relayReducedPolicy Player.owner replacement)) =
      1 := by
  rw [relay_owner_expectedUtility, fairSignal_expect]
  rw [expanded_reduced_owner_blind replacement false true]
  simp only [expanded_updated_reduced_rival, FinDist.expect_pure]
  let law := (pruning true).expandPolicy
    (Profile.update (sig := (pruning true).reducedBehavioralSignature)
      relayReducedPolicy Player.owner replacement) Player.owner
      (ownerSite true) (ownerObservation true)
  show (law.expect (fun action =>
      coordinationScore action false + bitScore false) +
    law.expect (fun action =>
      coordinationScore action true + bitScore true)) / 2 = 1
  have hfalse : law.expect (fun action =>
      coordinationScore action false + bitScore false) =
      law.expect (fun action => coordinationScore action false) := by
    apply FinDist.expect_congr
    intro action _
    simp [bitScore]
  have htrue : law.expect (fun action =>
      coordinationScore action true + bitScore true) =
      law.expect (fun action => coordinationScore action true) + 1 := by
    rw [← FinDist.expect_const law 1, ← FinDist.expect_add]
    apply FinDist.expect_congr
    intro action _
    simp [bitScore]
  rw [hfalse, htrue, ← add_assoc,
    expect_coordination_false_add_true]
  norm_num

/-- The signal-copying full deviation earns `3/2`, whereas every blind
reduced owner replacement earns `1`; hence the exact semantic coverage
certificate fails. -/
theorem relay_not_coversFullDeviations :
    ¬ (pruning true).CoversFullDeviationsAt (semantics true)
      relayReducedPolicy := by
  intro hcover
  obtain ⟨replacement, hcovered⟩ := hcover .owner ownerCopiesSignal
  rw [euPreference_apply, relay_copy_expectedUtility,
    reduced_owner_replacement_expectedUtility replacement] at hcovered
  norm_num at hcovered

end GameTheory.Experimental.PostArchitecture.MAIDGraphicalReductionTest
