/-
# Finite Bayesian-network factor partitions

This experiment starts below any particular Bayesian-network evaluator.  It
records the local mass contributed by typed node kernels and proves the first
algebraic step used by global-Markov arguments: factors over disconnected,
parent-closed components split multiplicatively and each component factor
depends only on that component's coordinates.

There is deliberately no joint-law definition and no conditional-independence
predicate here.  A later semantic bridge must prove that the canonical MAID
assignment law has the factor product below as its point mass before graphical
separation can imply a probabilistic statement.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

open GameTheory.Math.Probability

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- A complete assignment for a dependent family of node domains. -/
abbrev Assignment := (node : Node) → Value node

/-- The typed configuration of one node's declared parents. -/
abbrev ParentConfiguration (parents : Node → Finset Node) (node : Node) :=
  (parent : {parent // parent ∈ parents node}) → Value parent.1

/-- One normalized finite-support kernel at every node. -/
abbrev LocalKernels (parents : Node → Finset Node) :=
  (node : Node) → ParentConfiguration Value parents node →
    FinDist (Value node)

/-- Read the parent configuration of a node from a complete assignment. -/
def parentConfiguration (parents : Node → Finset Node)
    (assignment : Assignment Value) (node : Node) :
    ParentConfiguration Value parents node :=
  fun parent => assignment parent.1

/-- The point-mass contribution of one local kernel at one assignment. -/
def localFactor (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (assignment : Assignment Value) (node : Node) : ℝ :=
  (kernels node (parentConfiguration Value parents assignment node)).prob
    (assignment node)

/-- Product of the local factor masses indexed by a finite node set. -/
def factorProduct (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents) (nodes : Finset Node)
    (assignment : Assignment Value) : ℝ :=
  ∏ node ∈ nodes, localFactor Value parents kernels assignment node

/-- A node set contains every declared parent of each node it contains. -/
def ParentClosed (parents : Node → Finset Node) (nodes : Finset Node) : Prop :=
  ∀ node ∈ nodes, parents node ⊆ nodes

/-- An assignment score reads only the coordinates in `nodes`. -/
def DependsOnlyOn (nodes : Finset Node)
    (score : Assignment Value → ℝ) : Prop :=
  ∀ first second,
    (∀ node ∈ nodes, first node = second node) →
      score first = score second

theorem parentConfiguration_eq_of_agreeOn
    (parents : Node → Finset Node) (nodes : Finset Node)
    (hclosed : ParentClosed parents nodes)
    {first second : Assignment Value}
    (hagree : ∀ node ∈ nodes, first node = second node)
    {node : Node} (hnode : node ∈ nodes) :
    parentConfiguration Value parents first node =
      parentConfiguration Value parents second node := by
  funext parent
  exact hagree parent.1 (hclosed node hnode parent.2)

theorem localFactor_eq_of_agreeOn
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents) (nodes : Finset Node)
    (hclosed : ParentClosed parents nodes)
    {first second : Assignment Value}
    (hagree : ∀ node ∈ nodes, first node = second node)
    {node : Node} (hnode : node ∈ nodes) :
    localFactor Value parents kernels first node =
      localFactor Value parents kernels second node := by
  unfold localFactor
  rw [parentConfiguration_eq_of_agreeOn Value parents nodes hclosed
    hagree hnode, hagree node hnode]

/-- A product of factors in a parent-closed component cannot inspect an
assignment coordinate outside that component. -/
theorem parentClosed_factorProduct_dependsOnlyOn
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents) (nodes : Finset Node)
    (hclosed : ParentClosed parents nodes) :
    DependsOnlyOn Value nodes (factorProduct Value parents kernels nodes) := by
  intro first second hagree
  unfold factorProduct
  apply Finset.prod_congr rfl
  intro node hnode
  exact localFactor_eq_of_agreeOn Value parents kernels nodes hclosed
    hagree hnode

theorem factorProduct_union [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    {left right : Finset Node} (hdisjoint : Disjoint left right)
    (assignment : Assignment Value) :
    factorProduct Value parents kernels (left ∪ right) assignment =
      factorProduct Value parents kernels left assignment *
        factorProduct Value parents kernels right assignment := by
  unfold factorProduct
  rw [Finset.prod_union hdisjoint]

/-- Disconnected parent-closed components give a genuine factor partition:
the full local mass product splits into two scores, and each score is
extensionally confined to its own component.

This is a factorization theorem, not a conditional-independence assumption or
conclusion. -/
theorem disconnected_partition_factorization
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (left right : Finset Node)
    (hdisjoint : Disjoint left right)
    (hcover : left ∪ right = Finset.univ)
    (hleft : ParentClosed parents left)
    (hright : ParentClosed parents right) :
    (∀ assignment : Assignment Value,
      factorProduct Value parents kernels Finset.univ assignment =
        factorProduct Value parents kernels left assignment *
          factorProduct Value parents kernels right assignment) ∧
      DependsOnlyOn Value left
        (factorProduct Value parents kernels left) ∧
      DependsOnlyOn Value right
        (factorProduct Value parents kernels right) := by
  refine ⟨?_,
    parentClosed_factorProduct_dependsOnlyOn Value parents kernels left hleft,
    parentClosed_factorProduct_dependsOnlyOn Value parents kernels right hright⟩
  intro assignment
  rw [← hcover]
  exact factorProduct_union Value parents kernels hdisjoint assignment

end GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
