/-
# Dependent assignment enumeration

This file reindexes complete dependent assignments that agree with a fixed
witness on selected coordinates by configurations on the complementary
coordinates.  Construction branches on membership and never exposes equality
transport or a non-dependent update operation.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration

open scoped BigOperators
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

universe uNode uValue uResult

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- Values assigned only to coordinates outside `nodes`. -/
abbrev ComplementConfiguration (nodes : Finset Node) :=
  (node : {node // node ∉ nodes}) → Value node.1

/-- Two dependent assignments coincide on the selected coordinates. -/
def AgreeOn (nodes : Finset Node)
    (first second : Assignment Value) : Prop :=
  ∀ node ∈ nodes, first node = second node

instance [DecidableEq Node] [∀ node, DecidableEq (Value node)]
    (nodes : Finset Node) (first second : Assignment Value) :
    Decidable (AgreeOn Value nodes first second) := by
  unfold AgreeOn
  infer_instance

/-- Complete assignments constrained to coincide with `witness` on `nodes`. -/
abbrev AgreeingAssignments (nodes : Finset Node)
    (witness : Assignment Value) :=
  {assignment : Assignment Value // AgreeOn Value nodes assignment witness}

/-- Complete a complementary configuration by reading the fixed witness on
`nodes`.  Both branches retain the original node index. -/
def fillComplement [DecidableEq Node] (nodes : Finset Node)
    (witness : Assignment Value) (configuration : ComplementConfiguration Value nodes) :
    Assignment Value :=
  fun node => if hnode : node ∈ nodes then witness node
    else configuration ⟨node, hnode⟩

@[simp]
theorem fillComplement_of_mem [DecidableEq Node] (nodes : Finset Node)
    (witness : Assignment Value) (configuration : ComplementConfiguration Value nodes)
    {node : Node} (hnode : node ∈ nodes) :
    fillComplement Value nodes witness configuration node = witness node := by
  simp [fillComplement, hnode]

@[simp]
theorem fillComplement_of_notMem [DecidableEq Node] (nodes : Finset Node)
    (witness : Assignment Value) (configuration : ComplementConfiguration Value nodes)
    {node : Node} (hnode : node ∉ nodes) :
    fillComplement Value nodes witness configuration node =
      configuration ⟨node, hnode⟩ := by
  simp [fillComplement, hnode]

/-- Restriction to complementary coordinates is inverse to completing with a
fixed witness on `nodes`. -/
def agreeingAssignmentsEquivComplement [DecidableEq Node]
    (nodes : Finset Node) (witness : Assignment Value) :
    AgreeingAssignments Value nodes witness ≃ ComplementConfiguration Value nodes where
  toFun assignment node := assignment.1 node.1
  invFun configuration :=
    ⟨fillComplement Value nodes witness configuration,
      fun node hnode => fillComplement_of_mem Value nodes witness configuration hnode⟩
  left_inv assignment := by
    apply Subtype.ext
    funext node
    by_cases hnode : node ∈ nodes
    · show fillComplement Value nodes witness
          (fun complement => assignment.1 complement.1) node = assignment.1 node
      rw [fillComplement_of_mem Value nodes witness _ hnode]
      exact (assignment.2 node hnode).symm
    · show fillComplement Value nodes witness
          (fun complement => assignment.1 complement.1) node = assignment.1 node
      rw [fillComplement_of_notMem Value nodes witness _ hnode]
  right_inv configuration := by
    funext node
    exact fillComplement_of_notMem Value nodes witness configuration node.2

@[simp]
theorem agreeingAssignmentsEquivComplement_apply [DecidableEq Node]
    (nodes : Finset Node) (witness : Assignment Value)
    (assignment : AgreeingAssignments Value nodes witness)
    (node : {node // node ∉ nodes}) :
    agreeingAssignmentsEquivComplement Value nodes witness assignment node =
      assignment.1 node.1 :=
  rfl

@[simp]
theorem agreeingAssignmentsEquivComplement_symm_apply [DecidableEq Node]
    (nodes : Finset Node) (witness : Assignment Value)
    (configuration : ComplementConfiguration Value nodes) :
    (agreeingAssignmentsEquivComplement Value nodes witness).symm configuration =
      ⟨fillComplement Value nodes witness configuration,
        fun node hnode =>
          fillComplement_of_mem Value nodes witness configuration
            (node := node) hnode⟩ :=
  rfl

/-- Reindex a filtered sum over complete assignments by freely chosen values
on the complementary coordinates. -/
theorem sum_ite_agrees_eq_sum_complement
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    {Result : Type uResult} [AddCommMonoid Result]
    (nodes : Finset Node) (witness : Assignment Value)
    (score : Assignment Value → Result) :
    (∑ assignment : Assignment Value,
        if AgreeOn Value nodes assignment witness
        then score assignment else 0) =
      ∑ configuration : ComplementConfiguration Value nodes,
        score (fillComplement Value nodes witness configuration) := by
  classical
  let equivalence := agreeingAssignmentsEquivComplement Value nodes witness
  calc
    (∑ assignment : Assignment Value,
        if AgreeOn Value nodes assignment witness
        then score assignment else 0) =
        ∑ assignment : AgreeingAssignments Value nodes witness,
          score assignment.1 := by
      calc
        _ = ∑ assignment ∈ Finset.univ.filter
              (fun candidate => AgreeOn Value nodes candidate witness),
              score assignment := by
          rw [Finset.sum_filter]
        _ = _ := by
          rw [← Finset.sum_subtype_eq_sum_filter score]
          simp
    _ = ∑ configuration : ComplementConfiguration Value nodes,
          score (fillComplement Value nodes witness configuration) := by
      apply Fintype.sum_equiv equivalence
      intro assignment
      have hinverse := congrArg Subtype.val
        (equivalence.symm_apply_apply assignment)
      exact congrArg score hinverse.symm

theorem agreeOn_insert_setOne_iff [DecidableEq Node]
    (nodes : Finset Node) {pivot : Node} (hpivot : pivot ∉ nodes)
    (witness assignment : Assignment Value) (value : Value pivot) :
    AgreeOn Value (insert pivot nodes) assignment
        (GameTheory.Math.Probability.FinDist.DependentAssignment.setOne witness
          ⟨pivot, value⟩) ↔
      AgreeOn Value nodes assignment witness ∧ assignment pivot = value := by
  constructor
  · intro hagrees
    constructor
    · intro node hnode
      have hne : node ≠ pivot := by
        intro heq
        subst node
        exact hpivot hnode
      simpa [GameTheory.Math.Probability.FinDist.DependentAssignment.setOne,
        GameTheory.Math.Probability.FinDist.DependentAssignment.resolve, hne] using
          hagrees node (Finset.mem_insert_of_mem hnode)
    · simpa [GameTheory.Math.Probability.FinDist.DependentAssignment.setOne,
        GameTheory.Math.Probability.FinDist.DependentAssignment.resolve] using
          hagrees pivot (Finset.mem_insert_self pivot nodes)
  · rintro ⟨hfixed, hpivotValue⟩ node hnode
    rcases Finset.mem_insert.mp hnode with rfl | hnode
    · simpa [GameTheory.Math.Probability.FinDist.DependentAssignment.setOne,
        GameTheory.Math.Probability.FinDist.DependentAssignment.resolve] using hpivotValue
    · have hne : node ≠ pivot := by
        intro heq
        subst node
        exact hpivot hnode
      simpa [GameTheory.Math.Probability.FinDist.DependentAssignment.setOne,
        GameTheory.Math.Probability.FinDist.DependentAssignment.resolve, hne] using
          hfixed node hnode

/-- Fubini step for one newly fixed coordinate.  Each assignment agreeing on
`nodes` occurs in exactly the branch indexed by its value at `pivot`. -/
theorem sum_ite_agrees_eq_sum_insert
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    {Result : Type uResult} [AddCommMonoid Result]
    (nodes : Finset Node) {pivot : Node} (hpivot : pivot ∉ nodes)
    (witness : Assignment Value) (score : Assignment Value → Result) :
    (∑ assignment : Assignment Value,
        if AgreeOn Value nodes assignment witness
        then score assignment else 0) =
      ∑ value : Value pivot,
        ∑ assignment : Assignment Value,
          if AgreeOn Value (insert pivot nodes) assignment
              (GameTheory.Math.Probability.FinDist.DependentAssignment.setOne witness
                ⟨pivot, value⟩)
          then score assignment else 0 := by
  classical
  simp_rw [agreeOn_insert_setOne_iff Value nodes hpivot]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hagrees : AgreeOn Value nodes assignment witness
  · simp [hagrees]
  · simp [hagrees]

namespace BoolControl

abbrev value (_ : Bool) := Bool

def fixed : Finset Bool := {false}

def witness : Assignment value := fun _ => false

def freeConfiguration (free : Bool) :
    ComplementConfiguration value fixed :=
  fun _ => free

/-- The complement of the fixed `false` node really is one freely chosen Bool
coordinate. -/
def freeConfigurationEquiv :
    Bool ≃ ComplementConfiguration value fixed where
  toFun := freeConfiguration
  invFun configuration := configuration ⟨true, by simp [fixed]⟩
  left_inv _ := rfl
  right_inv configuration := by
    funext node
    rcases node with ⟨node, hnode⟩
    cases node
    · simp [fixed] at hnode
    · rfl

/-- The filtered assignment sum has one contribution, from the assignment
whose free `true` coordinate is true. -/
theorem filtered_sum_eq_one :
    (∑ assignment : Assignment value,
      if AgreeOn value fixed assignment witness then
        (if assignment true then 1 else 0 : ℕ)
      else 0) = 1 := by
  rw [sum_ite_agrees_eq_sum_complement value fixed witness
    (fun assignment => if assignment true then 1 else 0)]
  calc
    (∑ configuration : ComplementConfiguration value fixed,
        if fillComplement value fixed witness configuration true then 1 else 0) =
        ∑ free : Bool, if free then 1 else 0 := by
      symm
      apply Fintype.sum_equiv freeConfigurationEquiv
      intro free
      show (if free then 1 else 0) =
        if fillComplement value fixed witness (freeConfiguration free) true
        then 1 else 0
      rw [fillComplement_of_notMem value fixed witness _ (by simp [fixed])]
      show (if free then 1 else 0) = if free then 1 else 0
      rfl
    _ = 1 := by decide

end BoolControl

end GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
