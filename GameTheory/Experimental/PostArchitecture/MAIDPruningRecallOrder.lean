/-
# EXP-107: recall-order data for a pruned MAID

This experiment supplies the local dependent-policy and owner-ordering data
needed by a later recall argument.  It makes no semantic coverage claim.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
import GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
import GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
import GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningRecallOrder

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-! ## Reduced-owner site surgery -/

/-- Replace one site rule in a reduced owner policy. -/
def replaceReducedSiteRule (pruning : Pruning diagram)
    {owner : Player} (policy : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      FinDist (diagram.Value target.1)) :
    pruning.ReducedOwnerPolicy owner :=
  fun site => by
    by_cases hsite : site = target
    · subst site
      exact rule
    · exact policy site

@[simp]
theorem replaceReducedSiteRule_same (pruning : Pruning diagram)
    {owner : Player} (policy : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      FinDist (diagram.Value target.1)) :
    replaceReducedSiteRule pruning policy target rule target = rule := by
  simp [replaceReducedSiteRule]

theorem replaceReducedSiteRule_of_ne (pruning : Pruning diagram)
    {owner : Player} (policy : pruning.ReducedOwnerPolicy owner)
    (target site : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      FinDist (diagram.Value target.1)) (hne : site ≠ target) :
    replaceReducedSiteRule pruning policy target rule site = policy site := by
  simp [replaceReducedSiteRule, hne]

@[simp]
theorem replaceReducedSiteRule_self (pruning : Pruning diagram)
    {owner : Player} (policy : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) :
    replaceReducedSiteRule pruning policy target (policy target) = policy := by
  funext site
  by_cases hsite : site = target
  · subst site
    exact replaceReducedSiteRule_same pruning policy target (policy target)
  · exact replaceReducedSiteRule_of_ne pruning policy target site
      (policy target) hsite

/-- Expanding reduced surgery is exactly full-context site surgery. -/
theorem expandOwnerPolicy_replaceReducedSiteRule
    [DecidableEq Node] (pruning : Pruning diagram)
    {owner : Player} (policy : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      FinDist (diagram.Value target.1)) :
    pruning.expandOwnerPolicy owner
        (replaceReducedSiteRule pruning policy target rule) =
      replaceSiteRule (pruning.expandOwnerPolicy owner policy) target
        (expandKeptSiteRule pruning target rule) := by
  funext site observed
  by_cases hsite : site = target
  · subst site
    simp [Pruning.expandOwnerPolicy, replaceReducedSiteRule,
      replaceSiteRule, expandKeptSiteRule]
  · simp [Pruning.expandOwnerPolicy, replaceReducedSiteRule,
      replaceSiteRule, hsite]

/-! ## Oriented owner orders -/

@[reducible] private noncomputable def decisionSiteFintype [Fintype Node]
    (owner : Player) : Fintype (DecisionSite diagram owner) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun node =>
      diagram.kind node = .decision owner)) (by simp)

/-- The sites strategically relevant to a target, oriented as predecessors. -/
noncomputable def orientedPredecessors
    (view : UtilityView semantics) (owner : Player)
    [Fintype Node] [DecidableEq Node] :
    DecisionSite diagram owner → Finset (DecisionSite diagram owner) := by
  classical
  letI := decisionSiteFintype (diagram := diagram) owner
  exact fun target => Finset.univ.filter
    (fun source => UtilityView.OrientedRelevance view source target)

theorem mem_orientedPredecessors_iff
    (view : UtilityView semantics) (owner : Player)
    [Fintype Node] [DecidableEq Node]
    (source target : DecisionSite diagram owner) :
    source ∈ orientedPredecessors view owner target ↔
      UtilityView.OrientedRelevance view source target := by
  classical
  letI := decisionSiteFintype (diagram := diagram) owner
  simp [orientedPredecessors]

/-- `SReachAcyclic` is acyclicity of the predecessor-set presentation. -/
theorem orientedPredecessors_acyclic
    (view : UtilityView semantics) [Fintype Node] [DecidableEq Node]
    (owner : Player)
    (hacyclic : UtilityView.SReachAcyclic view) :
    GameTheory.Math.DAG.Acyclic
      (fun source target : DecisionSite diagram owner =>
        source ∈ orientedPredecessors view owner target) := by
  classical
  letI := decisionSiteFintype (diagram := diagram) owner
  intro vertex hcycle
  have hconvert : ∀ {first second : DecisionSite diagram owner},
      Relation.TransGen
          (fun source target =>
            source ∈ orientedPredecessors view owner target) first second →
        Relation.TransGen
          (fun source target => UtilityView.OrientedRelevance view source target)
          first second := by
    intro first second path
    induction path with
    | single hedge =>
        exact Relation.TransGen.single
          ((mem_orientedPredecessors_iff view owner _ _).mp hedge)
    | tail firstMiddle middleSecond ih =>
        exact Relation.TransGen.tail ih
          ((mem_orientedPredecessors_iff view owner _ _).mp middleSecond)
  exact hacyclic owner vertex (hconvert hcycle)

/-- A finite source-first order for one owner's oriented relevance graph. -/
noncomputable def orientedTopologicalOrder
    (view : UtilityView semantics) [Fintype Node] [DecidableEq Node]
    (owner : Player) (hacyclic : UtilityView.SReachAcyclic view) :
    GameTheory.Math.DAG.TopologicalOrder
      (orientedPredecessors view owner) :=
  by
    classical
    letI := decisionSiteFintype (diagram := diagram) owner
    exact (GameTheory.Math.DAG.topologicalOrder_of_acyclic
      (orientedPredecessors_acyclic view owner hacyclic)).some

/-- A later source in the owner order cannot be relevant to an earlier target. -/
theorem later_not_oriented_source
    (view : UtilityView semantics) [Fintype Node] [DecidableEq Node]
    (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (orientedPredecessors view owner))
    {earlier later : Fin topological.order.length}
    (hindex : earlier.val < later.val) :
    ¬ UtilityView.OrientedRelevance view
      (topological.order.get later) (topological.order.get earlier) := by
  classical
  letI := decisionSiteFintype (diagram := diagram) owner
  let earlierSite : DecisionSite diagram owner := topological.order.get earlier
  let laterSite : DecisionSite diagram owner := topological.order.get later
  have hnot : ¬ UtilityView.OrientedRelevance view laterSite earlierSite := by
    intro hsource
    have hmember : laterSite ∈ orientedPredecessors view owner earlierSite :=
      (mem_orientedPredecessors_iff view owner _ _).mpr hsource
    have hpath : Relation.TransGen
        (fun source target =>
          source ∈ orientedPredecessors view owner target)
        laterSite earlierSite :=
      Relation.TransGen.single hmember
    have hlt := topological.ancestor_lt hpath (hancestor := rfl)
      (hdescendant := rfl)
    omega
  simpa [earlierSite, laterSite] using hnot

/-! ## A finite fully mixed reduced owner policy -/

/-- Uniform law on an arbitrary nonempty finite carrier. -/
noncomputable def uniformFinite [Fintype α] [Nonempty α] : FinDist α :=
  FinDist.ofWeights (fun _ => (Fintype.card α : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)))

theorem uniformFinite_mem_support [Fintype α] [Nonempty α] (action : α) :
    action ∈ (uniformFinite : FinDist α).support := by
  rw [← FinDist.prob_pos_iff, uniformFinite, FinDist.prob_ofWeights]
  exact inv_pos.mpr (by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α)))

/-- Uniformly randomize every site in a reduced owner policy. -/
noncomputable def uniformReducedOwnerPolicy (pruning : Pruning diagram)
    (owner : Player) [∀ node, Fintype (diagram.Value node)]
    [∀ node, Nonempty (diagram.Value node)] :
  pruning.ReducedOwnerPolicy owner :=
  fun _ _ => uniformFinite

/-- Its expansion is fully mixed at every site of that owner. -/
theorem expand_uniformReducedOwnerPolicy_fullyMixedAt
    (pruning : Pruning diagram) (owner : Player)
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, Nonempty (diagram.Value node)]
    (target : DecisionSite diagram owner) :
    FullyMixedAt
      (pruning.expandOwnerPolicy owner
        (uniformReducedOwnerPolicy pruning owner)) target := by
  intro context action
  exact uniformFinite_mem_support action

theorem expand_uniformReducedOwnerPolicy_fullyMixedAt_all
    (pruning : Pruning diagram) (owner : Player)
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, Nonempty (diagram.Value node)] :
    ∀ target : DecisionSite diagram owner,
      FullyMixedAt
        (pruning.expandOwnerPolicy owner
          (uniformReducedOwnerPolicy pruning owner)) target := by
  intro target
  exact expand_uniformReducedOwnerPolicy_fullyMixedAt pruning owner target

/-- Canonical MAID semantics make every node-value carrier nonempty. -/
theorem nonemptyValue_of_semantics (semantics : Semantics diagram) :
    ∀ node, Nonempty (diagram.Value node) :=
  fun node => ⟨semantics.defaultValue node⟩

/-- Uniform reduced owner policy without an extra public nonemptiness premise. -/
noncomputable def uniformReducedOwnerPolicyOfSemantics
    (pruning : Pruning diagram) (semantics : Semantics diagram)
    (owner : Player) [∀ node, Fintype (diagram.Value node)] :
    pruning.ReducedOwnerPolicy owner := by
  letI : ∀ node, Nonempty (diagram.Value node) :=
    nonemptyValue_of_semantics semantics
  exact uniformReducedOwnerPolicy pruning owner

/-- The semantics-backed uniform policy is fully mixed at every owner site. -/
theorem expand_uniformReducedOwnerPolicyOfSemantics_fullyMixedAt_all
    (pruning : Pruning diagram) (semantics : Semantics diagram)
    (owner : Player) [∀ node, Fintype (diagram.Value node)] :
    ∀ target : DecisionSite diagram owner,
      FullyMixedAt
        (pruning.expandOwnerPolicy owner
          (uniformReducedOwnerPolicyOfSemantics pruning semantics owner))
        target := by
  letI : ∀ node, Nonempty (diagram.Value node) :=
    nonemptyValue_of_semantics semantics
  simpa [uniformReducedOwnerPolicyOfSemantics] using
    expand_uniformReducedOwnerPolicy_fullyMixedAt_all pruning owner

end GameTheory.Experimental.PostArchitecture.MAIDPruningRecallOrder
