/-
# EXP-105: fixed-policy utility continuation from graphical CI

This file recodes the augmented graph-coordinate conditional independence
theorem into the full-context, target-action, and utility-configuration
observables needed by the canonical finite conditional continuation.  The
result remains about one fixed policy law and makes no replacement-uniformity
claim.
-/

import GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
import GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence
import GameTheory.Languages.MAID.ObservationPruning

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

universe uΩ uX uY uZ uX' uY' uZ'
universe uPlayer uNode

private theorem conditionallyIndependent_map_equiv
    {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    {law : GameTheory.Math.Probability.FinDist Ω}
    {first : Ω → X} {second : Ω → Y} {evidence : Ω → Z}
    (hindependent :
      IsConditionallyIndependent law first second evidence)
    (firstEquiv : X ≃ X') (secondEquiv : Y ≃ Y')
    (evidenceEquiv : Z ≃ Z') :
    IsConditionallyIndependent law
      (firstEquiv ∘ first) (secondEquiv ∘ second)
      (evidenceEquiv ∘ evidence) := by
  intro firstValue secondValue evidenceValue
  have htriple :
      tripleAtom (firstEquiv ∘ first) (secondEquiv ∘ second)
          (evidenceEquiv ∘ evidence) firstValue secondValue evidenceValue =
        tripleAtom first second evidence (firstEquiv.symm firstValue)
          (secondEquiv.symm secondValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [tripleAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hfirst, hsecond, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv.symm hfirst,
        by simpa using congrArg secondEquiv.symm hsecond,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hfirst, hsecond, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv hfirst,
        by simpa using congrArg secondEquiv hsecond,
        by simpa using congrArg evidenceEquiv hevidence⟩
  have hatom :
      atom (evidenceEquiv ∘ evidence) evidenceValue =
        atom evidence (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [atom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · exact fun heq => by simpa using congrArg evidenceEquiv.symm heq
    · exact fun heq => by simpa using congrArg evidenceEquiv heq
  have hfirstPair :
      pairAtom (firstEquiv ∘ first) (evidenceEquiv ∘ evidence)
          firstValue evidenceValue =
        pairAtom first evidence (firstEquiv.symm firstValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [pairAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hfirst, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv.symm hfirst,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hfirst, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv hfirst,
        by simpa using congrArg evidenceEquiv hevidence⟩
  have hsecondPair :
      pairAtom (secondEquiv ∘ second) (evidenceEquiv ∘ evidence)
          secondValue evidenceValue =
        pairAtom second evidence (secondEquiv.symm secondValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [pairAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hsecond, hevidence⟩
      exact ⟨by simpa using congrArg secondEquiv.symm hsecond,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hsecond, hevidence⟩
      exact ⟨by simpa using congrArg secondEquiv hsecond,
        by simpa using congrArg evidenceEquiv hevidence⟩
  rw [htriple, hatom, hfirstPair, hsecondPair]
  exact hindependent (firstEquiv.symm firstValue)
    (secondEquiv.symm secondValue) (evidenceEquiv.symm evidenceValue)

private theorem conditionallyIndependent_adjoin_evidence
    {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {law : GameTheory.Math.Probability.FinDist Ω}
    {first : Ω → X} {second : Ω → Y} {evidence : Ω → Z}
    (hindependent :
      IsConditionallyIndependent law first second evidence) :
    IsConditionallyIndependent law
      (fun omega => (first omega, evidence omega)) second evidence := by
  rintro ⟨firstValue, carriedEvidence⟩ secondValue evidenceValue
  classical
  by_cases hevidence : carriedEvidence = evidenceValue
  · subst carriedEvidence
    have htriple :
        tripleAtom (fun omega => (first omega, evidence omega)) second evidence
            (firstValue, evidenceValue) secondValue evidenceValue =
          tripleAtom first second evidence firstValue secondValue
            evidenceValue := by
      ext omega
      simp only [tripleAtom, Set.mem_setOf_eq, Prod.mk.injEq]
      tauto
    have hpair :
        pairAtom (fun omega => (first omega, evidence omega)) evidence
            (firstValue, evidenceValue) evidenceValue =
          pairAtom first evidence firstValue evidenceValue := by
      ext omega
      simp only [pairAtom, Set.mem_setOf_eq, Prod.mk.injEq]
      tauto
    rw [htriple, hpair]
    exact hindependent firstValue secondValue evidenceValue
  · have htriple :
        tripleAtom (fun omega => (first omega, evidence omega)) second evidence
            (firstValue, carriedEvidence) secondValue evidenceValue = ∅ := by
      ext omega
      simp only [tripleAtom, Set.mem_setOf_eq, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hcarried⟩, _, hactual⟩
      exact hevidence (hcarried.symm.trans hactual)
    have hpair :
        pairAtom (fun omega => (first omega, evidence omega)) evidence
            (firstValue, carriedEvidence) evidenceValue = ∅ := by
      ext omega
      simp only [pairAtom, Set.mem_setOf_eq, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hcarried⟩, hactual⟩
      exact hevidence (hcarried.symm.trans hactual)
    have hempty : law.probOf (∅ : Set Ω) = 0 := by
      rw [← GameTheory.Math.Probability.FinDist.expect_indicator_eq_probOf]
      simp
    rw [htriple, hpair, hempty]
    simp

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

abbrev KeptNodes [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) :=
  diagram.observedParents site.1 \ removed

abbrev FullAction {owner : Player} (site : DecisionSite diagram owner) :=
  Config diagram (diagram.observedParents site.1) × diagram.Value site.1

abbrev KeptAction [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) :=
  Config diagram (KeptNodes site removed) × diagram.Value site.1

abbrev TermConfig (view : UtilityView semantics) {owner : Player}
    (term : view.UtilitySite owner) :=
  Config diagram (view.term term).parents

def fullAction (view : UtilityView semantics) {owner : Player}
    (site : DecisionSite diagram owner)
    (assignment : AugmentedAssignment view owner) : FullAction site :=
  (Assignment.restrict diagram (projectBase view assignment)
    (diagram.observedParents site.1),
    projectBase view assignment site.1)

def termConfig (view : UtilityView semantics) {owner : Player}
    (term : view.UtilitySite owner)
    (assignment : AugmentedAssignment view owner) : TermConfig view term :=
  assignment (.utility term)

def keepFullAction [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) : FullAction site → KeptAction site removed :=
  fun full =>
    (Config.restrict (diagram := diagram) (Finset.sdiff_subset) full.1,
      full.2)

private def removedConfigurationEquiv
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (removed : Finset Node) :
    Config (utilityGraphStructure topological view owner)
        (removedGraphNodes view owner removed) ≃
      Config diagram removed where
  toFun configuration node :=
    configuration ⟨.base node.1, by
      simp [removedGraphNodes, node.2]⟩
  invFun configuration graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | base node =>
        exact configuration ⟨node, by
          simpa [removedGraphNodes] using hgraphNode⟩
    | utility term =>
        simp [removedGraphNodes] at hgraphNode
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | base node => rfl
    | utility term =>
        simp [removedGraphNodes] at hgraphNode
  right_inv configuration := by
    funext node
    rfl

private def utilityConfigurationEquiv
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) :
    Config (utilityGraphStructure topological view owner) {.utility term} ≃
      TermConfig view term where
  toFun configuration :=
    configuration ⟨.utility term, Finset.mem_singleton_self _⟩
  invFun configuration graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    have heq : graphNode = .utility term := by simpa using hgraphNode
    subst graphNode
    exact configuration
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    have heq : graphNode = .utility term := by simpa using hgraphNode
    subst graphNode
    rfl
  right_inv _ := rfl

private theorem site_not_observed [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner) :
    site.1 ∉ diagram.observedParents site.1 := by
  intro hsite
  apply diagram.acyclic site.1
  apply Relation.TransGen.single
  exact diagram.observed_sub site.1 hsite

private def conditioningConfigurationEquiv
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (site : DecisionSite diagram owner) (removed : Finset Node) :
    Config (utilityGraphStructure topological view owner)
        (view.observationConditioningSet site removed) ≃
      KeptAction site removed where
  toFun configuration :=
    (fun node => configuration ⟨.base node.1, by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨node.1, node.2, rfl⟩⟩,
    configuration ⟨.base site.1, by
      simp [UtilityView.observationConditioningSet]⟩)
  invFun keptAction graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | utility term =>
        simp [UtilityView.observationConditioningSet] at hgraphNode
    | base node =>
        by_cases hsite : node = site.1
        · subst node
          exact keptAction.2
        · have hkept : node ∈ KeptNodes site removed := by
            have hmembership :
                node ∈ diagram.observedParents site.1 \ removed := by
              simpa [UtilityView.observationConditioningSet, hsite] using
                hgraphNode
            exact hmembership
          exact keptAction.1 ⟨node, hkept⟩
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | utility term =>
        simp [UtilityView.observationConditioningSet] at hgraphNode
    | base node =>
        by_cases hsite : node = site.1
        · subst node
          simp
        · simp [hsite]
  right_inv keptAction := by
    apply Prod.ext
    · funext node
      have hne : node.1 ≠ site.1 := by
        intro heq
        have hobserved := (Finset.mem_sdiff.mp node.2).1
        exact site_not_observed site (heq ▸ hobserved)
      simp [hne]
    · simp

private def fullActionSplitEquiv
    [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node)
    (hremoved : removed ⊆ diagram.observedParents site.1) :
    FullAction site ≃
      Config diagram removed × KeptAction site removed where
  toFun full :=
    (Config.restrict hremoved full.1, keepFullAction site removed full)
  invFun parts :=
    ((fun node => if hnode : node.1 ∈ removed
      then parts.1 ⟨node.1, hnode⟩
      else parts.2.1 ⟨node.1,
        Finset.mem_sdiff.mpr ⟨node.2, hnode⟩⟩),
      parts.2.2)
  left_inv full := by
    apply Prod.ext
    · funext node
      by_cases hnode : node.1 ∈ removed <;>
        simp [hnode, Config.restrict, keepFullAction]
    · rfl
  right_inv parts := by
    apply Prod.ext
    · funext node
      simp [Config.restrict, node.2]
    · apply Prod.ext
      · funext node
        have hnot : node.1 ∉ removed := (Finset.mem_sdiff.mp node.2).2
        simp [keepFullAction, Config.restrict, hnot]
      · rfl

private theorem removedConfigurationEquiv_restrict
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hremoved : removed ⊆ diagram.observedParents site.1)
    (assignment : AugmentedAssignment view owner) :
    removedConfigurationEquiv topological view owner removed
        (Assignment.restrict (utilityGraphStructure topological view owner)
          assignment (removedGraphNodes view owner removed)) =
      Config.restrict hremoved (fullAction view site assignment).1 := by
  funext node
  rfl

private theorem utilityConfigurationEquiv_restrict
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner)
    (assignment : AugmentedAssignment view owner) :
    utilityConfigurationEquiv topological view owner term
        (Assignment.restrict (utilityGraphStructure topological view owner)
          assignment {.utility term}) =
      termConfig view term assignment := by
  rfl

private theorem conditioningConfigurationEquiv_restrict
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (assignment : AugmentedAssignment view owner) :
    conditioningConfigurationEquiv topological view owner site removed
        (Assignment.restrict (utilityGraphStructure topological view owner)
          assignment (view.observationConditioningSet site removed)) =
      keepFullAction site removed (fullAction view site assignment) := by
  apply Prod.ext <;> rfl

private theorem fullActionSplitEquiv_symm_parts
    [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node)
    (hremoved : removed ⊆ diagram.observedParents site.1)
    (full : FullAction site) :
    (fullActionSplitEquiv site removed hremoved).symm
        (Config.restrict hremoved full.1,
          keepFullAction site removed full) = full :=
  (fullActionSplitEquiv site removed hremoved).symm_apply_apply full

/-- The set-valued graph criterion recodes to conditional independence of the
complete observed context and target action from the utility leaf, given the
kept observed context and the same action. -/
theorem fullAction_conditionallyIndependent_of_graphicallyIgnorable
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore : view.AreGraphicallyIgnorable site removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm site term) :
    IsConditionallyIndependent (augmentedLaw view owner policy)
      (fullAction view site) (termConfig view term)
      (keepFullAction site removed ∘ fullAction view site) := by
  have hcoordinates :=
    removed_conditionallyIndependent_of_graphicallyIgnorable topological
      view owner policy site removed hignore term hrelevant
  have hrecoded := conditionallyIndependent_map_equiv hcoordinates
    (removedConfigurationEquiv topological view owner removed)
    (utilityConfigurationEquiv topological view owner term)
    (conditioningConfigurationEquiv topological view owner site removed)
  have hremovedEq :
      (removedConfigurationEquiv topological view owner removed :
          Config (utilityGraphStructure topological view owner)
              (removedGraphNodes view owner removed) → Config diagram removed) ∘
          (fun assignment =>
            Assignment.restrict
              (utilityGraphStructure topological view owner) assignment
              (removedGraphNodes view owner removed)) =
        fun assignment =>
          Config.restrict hignore.1 (fullAction view site assignment).1 := by
    funext assignment
    exact removedConfigurationEquiv_restrict topological view owner site
      removed hignore.1 assignment
  have htermEq :
      (utilityConfigurationEquiv topological view owner term :
          Config (utilityGraphStructure topological view owner)
              {.utility term} → TermConfig view term) ∘
          (fun assignment =>
            Assignment.restrict
              (utilityGraphStructure topological view owner) assignment
              {.utility term}) =
        termConfig view term := by
    funext assignment
    exact utilityConfigurationEquiv_restrict topological view owner term
      assignment
  have hconditioningEq :
      (conditioningConfigurationEquiv topological view owner site removed :
          Config (utilityGraphStructure topological view owner)
              (view.observationConditioningSet site removed) →
            KeptAction site removed) ∘
          (fun assignment =>
            Assignment.restrict
              (utilityGraphStructure topological view owner) assignment
              (view.observationConditioningSet site removed)) =
        keepFullAction site removed ∘ fullAction view site := by
    funext assignment
    exact conditioningConfigurationEquiv_restrict topological view owner site
      removed assignment
  rw [hremovedEq, htermEq, hconditioningEq] at hrecoded
  have hparts :
      IsConditionallyIndependent (augmentedLaw view owner policy)
        (fun assignment =>
          Config.restrict hignore.1 (fullAction view site assignment).1)
        (termConfig view term)
        (keepFullAction site removed ∘ fullAction view site) := by
    exact hrecoded
  have hadjoined := conditionallyIndependent_adjoin_evidence hparts
  have hfull := conditionallyIndependent_map_equiv hadjoined
    (fullActionSplitEquiv site removed hignore.1).symm
    (Equiv.refl (TermConfig view term))
    (Equiv.refl (KeptAction site removed))
  have hfullEq :
      (fullActionSplitEquiv site removed hignore.1).symm ∘
          (fun assignment =>
            (Config.restrict hignore.1 (fullAction view site assignment).1,
              (keepFullAction site removed ∘ fullAction view site)
                assignment)) =
        fullAction view site := by
    funext assignment
    exact fullActionSplitEquiv_symm_parts site removed hignore.1
      (fullAction view site assignment)
  have htermRefl :
      (Equiv.refl (TermConfig view term) : TermConfig view term →
        TermConfig view term) ∘ termConfig view term = termConfig view term :=
    rfl
  have hkeptRefl :
      (Equiv.refl (KeptAction site removed) : KeptAction site removed →
        KeptAction site removed) ∘
          (keepFullAction site removed ∘ fullAction view site) =
        keepFullAction site removed ∘ fullAction view site :=
    rfl
  rw [hfullEq, htermRefl, hkeptRefl] at hfull
  exact hfull

/-- For one fixed native policy, graphical ignorability therefore gives the
exact joint-law bind through the canonical continuation indexed by retained
context and target action.  This is not uniform over owner replacements. -/
theorem fixedPolicy_jointLaw_eq_bind_continuation
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore : view.AreGraphicallyIgnorable site removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm site term) :
    (augmentedLaw view owner policy).map
        (fun assignment =>
          (fullAction view site assignment, termConfig view term assignment)) =
      ((augmentedLaw view owner policy).map (fullAction view site)).bind
        fun full =>
          (continuation (augmentedLaw view owner policy)
              (fullAction view site) (termConfig view term)
              (keepFullAction site removed)
              (keepFullAction site removed full)).map
            fun termValue => (full, termValue) := by
  exact contextTermLaw_eq_bind_continuation
    (augmentedLaw view owner policy) (fullAction view site)
    (termConfig view term) (keepFullAction site removed)
    (fullAction_conditionallyIndependent_of_graphicallyIgnorable topological
      view owner policy site removed hignore term hrelevant)

end GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
