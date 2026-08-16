/-
# EXP-104: finite Bayesian-network factor scopes

This module isolates the graph-independent seam needed after a moral graph has
partitioned factor scopes.  The graph layer need only show that every factor
assigned to a side has its node and all of its parents in that side's declared
coordinate set.  Coordinate sets may overlap, as they do on conditioning
variables; only the factor-index partition is required to be disjoint.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- The coordinates read by one local factor: its own value and its parent
configuration. -/
def factorScope [DecidableEq Node]
    (parents : Node → Finset Node) (node : Node) : Finset Node :=
  insert node (parents node)

theorem self_mem_factorScope [DecidableEq Node]
    (parents : Node → Finset Node) (node : Node) :
    node ∈ factorScope parents node := by
  simp [factorScope]

theorem parents_subset_factorScope [DecidableEq Node]
    (parents : Node → Finset Node) (node : Node) :
    parents node ⊆ factorScope parents node := by
  intro parent hparent
  simp [factorScope, hparent]

/-- One local factor is unchanged when two assignments agree on a coordinate
set containing that factor's complete scope. -/
theorem localFactor_eq_of_scope_subset [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents) (coordinates : Finset Node)
    {first second : Assignment Value} {node : Node}
    (hscope : factorScope parents node ⊆ coordinates)
    (hagree : ∀ coordinate ∈ coordinates,
      first coordinate = second coordinate) :
    localFactor Value parents kernels first node =
      localFactor Value parents kernels second node := by
  have hnode : node ∈ coordinates :=
    hscope (self_mem_factorScope parents node)
  have hparents :
      parentConfiguration Value parents first node =
        parentConfiguration Value parents second node := by
    funext parent
    exact hagree parent.1
      (hscope (parents_subset_factorScope parents node parent.2))
  unfold localFactor
  rw [hparents, hagree node hnode]

/-- A product of local factors reads only `coordinates` when every included
factor's complete scope lies there. -/
theorem factorProduct_dependsOnlyOn_of_scopes_subset [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (factors coordinates : Finset Node)
    (hscopes : ∀ node ∈ factors,
      factorScope parents node ⊆ coordinates) :
    DependsOnlyOn Value coordinates
      (factorProduct Value parents kernels factors) := by
  intro first second hagree
  unfold factorProduct
  apply Finset.prod_congr rfl
  intro node hnode
  exact localFactor_eq_of_scope_subset Value parents kernels coordinates
    (hscopes node hnode) hagree

/-- A disjoint partition of factor indices splits the product and gives each
side its declared coordinate dependence.  The coordinate sets themselves need
not be disjoint. -/
theorem disjoint_factor_partition
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (leftFactors rightFactors leftCoordinates rightCoordinates : Finset Node)
    (hdisjoint : Disjoint leftFactors rightFactors)
    (hleftScopes : ∀ node ∈ leftFactors,
      factorScope parents node ⊆ leftCoordinates)
    (hrightScopes : ∀ node ∈ rightFactors,
      factorScope parents node ⊆ rightCoordinates) :
    (∀ assignment : Assignment Value,
      factorProduct Value parents kernels (leftFactors ∪ rightFactors) assignment =
        factorProduct Value parents kernels leftFactors assignment *
          factorProduct Value parents kernels rightFactors assignment) ∧
      DependsOnlyOn Value leftCoordinates
        (factorProduct Value parents kernels leftFactors) ∧
      DependsOnlyOn Value rightCoordinates
        (factorProduct Value parents kernels rightFactors) := by
  refine ⟨factorProduct_union Value parents kernels hdisjoint, ?_, ?_⟩
  · exact factorProduct_dependsOnlyOn_of_scopes_subset Value parents kernels
      leftFactors leftCoordinates hleftScopes
  · exact factorProduct_dependsOnlyOn_of_scopes_subset Value parents kernels
      rightFactors rightCoordinates hrightScopes

/-- Existential score form of `disjoint_factor_partition`.  This is the exact
interface consumed by a later rank-one marginalization proof. -/
theorem exists_partition_scores
    [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (leftFactors rightFactors leftCoordinates rightCoordinates : Finset Node)
    (hdisjoint : Disjoint leftFactors rightFactors)
    (hleftScopes : ∀ node ∈ leftFactors,
      factorScope parents node ⊆ leftCoordinates)
    (hrightScopes : ∀ node ∈ rightFactors,
      factorScope parents node ⊆ rightCoordinates) :
    ∃ leftScore rightScore : Assignment Value → ℝ,
      (∀ assignment,
        factorProduct Value parents kernels (leftFactors ∪ rightFactors) assignment =
          leftScore assignment * rightScore assignment) ∧
        DependsOnlyOn Value leftCoordinates leftScore ∧
        DependsOnlyOn Value rightCoordinates rightScore := by
  refine ⟨factorProduct Value parents kernels leftFactors,
    factorProduct Value parents kernels rightFactors, ?_⟩
  exact disjoint_factor_partition Value parents kernels leftFactors rightFactors
    leftCoordinates rightCoordinates hdisjoint hleftScopes hrightScopes

/-! ## Scope control -/

namespace Control

inductive ControlNode where
  | left
  | evidence
  | right
  deriving DecidableEq, Fintype

abbrev ControlValue (_ : ControlNode) := Bool

def parents : ControlNode → Finset ControlNode
  | .left => {.evidence}
  | .evidence => ∅
  | .right => {.evidence}

def kernels : LocalKernels ControlValue parents :=
  fun _ _ => FinDist.pure false

def leftFactors : Finset ControlNode := {.left}

def rightFactors : Finset ControlNode := {.evidence, .right}

def leftCoordinates : Finset ControlNode := {.left, .evidence}

def rightCoordinates : Finset ControlNode := {.evidence, .right}

theorem factorScopes_split :
    (∀ node ∈ leftFactors,
      factorScope parents node ⊆ leftCoordinates) ∧
    (∀ node ∈ rightFactors,
      factorScope parents node ⊆ rightCoordinates) := by
  constructor
  · intro node hnode coordinate hcoordinate
    cases node
    all_goals
      simp [leftFactors, leftCoordinates, factorScope, parents] at hnode hcoordinate ⊢
    all_goals tauto
  · intro node hnode coordinate hcoordinate
    cases node
    all_goals
      simp [rightFactors, rightCoordinates, factorScope, parents] at hnode hcoordinate ⊢
    all_goals tauto

/-- The control has disjoint factor indices while both scores may read the
shared evidence coordinate. -/
theorem partition_control :
    (∀ assignment : Assignment ControlValue,
      factorProduct ControlValue parents kernels (leftFactors ∪ rightFactors) assignment =
        factorProduct ControlValue parents kernels leftFactors assignment *
          factorProduct ControlValue parents kernels rightFactors assignment) ∧
      DependsOnlyOn ControlValue leftCoordinates
        (factorProduct ControlValue parents kernels leftFactors) ∧
      DependsOnlyOn ControlValue rightCoordinates
        (factorProduct ControlValue parents kernels rightFactors) := by
  exact disjoint_factor_partition ControlValue parents kernels
    leftFactors rightFactors leftCoordinates rightCoordinates
      (by simp [leftFactors, rightFactors])
      factorScopes_split.1 factorScopes_split.2

end Control

end GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes
