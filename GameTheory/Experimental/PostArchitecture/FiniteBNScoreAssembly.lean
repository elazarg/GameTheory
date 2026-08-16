/-
# EXP-104: dependent score assembly and rank-one marginalization

This module assembles arbitrary typed query configurations using an explicit
default assignment, completes them with two latent configurations, and turns a
factor-score split into a rank-one finite table.  It assumes no positivity or
normalization and defines no joint evaluator.

The retained carrier is explicit in every assembly operation.  It can be the
ancestral set inside the original node type, so nonretained coordinates are
left at the supplied default and are never included in a latent sum.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes
import GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
import GameTheory.Experimental.PostArchitecture.FiniteBNRankOne
import GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNRankOne
open GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

def fixedCoordinates [DecidableEq Node]
    (first second evidence : Finset Node) : Finset Node :=
  (first ∪ second) ∪ evidence

/-- The five coordinate blocks needed by the score adapter inside an explicit
retained carrier. -/
structure ScorePartition [DecidableEq Node]
    (first second evidence retained latentLeft latentRight : Finset Node) : Prop where
  first_second : Disjoint first second
  first_evidence : Disjoint first evidence
  second_evidence : Disjoint second evidence
  fixed_subset : fixedCoordinates first second evidence ⊆ retained
  latent : LatentPartition (fixedCoordinates first second evidence) retained
    latentLeft latentRight

/-- Restrict a complete assignment to a selected dependent configuration. -/
def configurationOf (assignment : Assignment Value) (nodes : Finset Node) :
    Configuration Value nodes :=
  fun node => assignment node.1

/-- Assemble three pairwise-disjoint query configurations.  Coordinates not in
the query blocks retain the explicit default value. -/
def queryWitness [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence) : Assignment Value :=
  fun node =>
    if hfirst : node ∈ first then firstConfiguration ⟨node, hfirst⟩
    else if hsecond : node ∈ second then secondConfiguration ⟨node, hsecond⟩
    else if hevidence : node ∈ evidence then
      evidenceConfiguration ⟨node, hevidence⟩
    else default node

@[simp]
theorem queryWitness_of_first [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    {node : Node} (hnode : node ∈ first) :
    queryWitness Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration node =
        firstConfiguration ⟨node, hnode⟩ := by
  simp [queryWitness, hnode]

@[simp]
theorem queryWitness_of_second [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    {node : Node} (hnode : node ∈ second) :
    queryWitness Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration node =
        secondConfiguration ⟨node, hnode⟩ := by
  have hnotFirst : node ∉ first := by
    intro hfirst
    exact (Finset.disjoint_left.mp partition.first_second) hfirst hnode
  simp [queryWitness, hnotFirst, hnode]

@[simp]
theorem queryWitness_of_evidence [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    {node : Node} (hnode : node ∈ evidence) :
    queryWitness Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration node =
        evidenceConfiguration ⟨node, hnode⟩ := by
  have hnotFirst : node ∉ first := by
    intro hfirst
    exact (Finset.disjoint_left.mp partition.first_evidence) hfirst hnode
  have hnotSecond : node ∉ second := by
    intro hsecond
    exact (Finset.disjoint_left.mp partition.second_evidence) hsecond hnode
  simp [queryWitness, hnotFirst, hnotSecond, hnode]

/-- Complete assembled query values with one configuration on each latent
side. -/
def completedAssignment [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight) : Assignment Value :=
  fillRetained Value (fixedCoordinates first second evidence) retained
    (queryWitness Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration)
    ((retainedDifferenceEquivLatents Value (fixedCoordinates first second evidence)
      retained latentLeft latentRight partition.latent).symm
        (leftConfiguration, rightConfiguration))

theorem completedAssignment_of_fixed [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ fixedCoordinates first second evidence) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      queryWitness Value default first second evidence firstConfiguration
        secondConfiguration evidenceConfiguration node := by
  apply fillRetained_of_notMem
  simp [hnode]

@[simp]
theorem completedAssignment_of_first [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ first) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      firstConfiguration ⟨node, hnode⟩ := by
  rw [completedAssignment_of_fixed Value default first second evidence retained
    latentLeft latentRight
    partition firstConfiguration secondConfiguration evidenceConfiguration
      leftConfiguration rightConfiguration]
  · exact queryWitness_of_first Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration hnode
  · simp [fixedCoordinates, hnode]

@[simp]
theorem completedAssignment_of_second [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ second) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      secondConfiguration ⟨node, hnode⟩ := by
  rw [completedAssignment_of_fixed Value default first second evidence retained
    latentLeft latentRight
    partition firstConfiguration secondConfiguration evidenceConfiguration
      leftConfiguration rightConfiguration]
  · exact queryWitness_of_second Value default first second evidence retained latentLeft
      latentRight partition
      firstConfiguration secondConfiguration evidenceConfiguration hnode
  · simp [fixedCoordinates, hnode]

@[simp]
theorem completedAssignment_of_evidence [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ evidence) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      evidenceConfiguration ⟨node, hnode⟩ := by
  rw [completedAssignment_of_fixed Value default first second evidence retained
    latentLeft latentRight
    partition firstConfiguration secondConfiguration evidenceConfiguration
      leftConfiguration rightConfiguration]
  · exact queryWitness_of_evidence Value default first second evidence retained latentLeft
      latentRight partition
      firstConfiguration secondConfiguration evidenceConfiguration hnode
  · simp [fixedCoordinates, hnode]

@[simp]
theorem completedAssignment_of_latentLeft [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ latentLeft) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      leftConfiguration ⟨node, hnode⟩ := by
  have hretained : node ∈ retained \ fixedCoordinates first second evidence := by
    rw [partition.latent.latent_cover]
    exact Finset.mem_union_left latentRight hnode
  rw [completedAssignment, fillRetained_of_mem Value _ _ _ _ hretained]
  simp [retainedDifferenceEquivLatents, hnode]

@[simp]
theorem completedAssignment_of_latentRight [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight)
    {node : Node} (hnode : node ∈ latentRight) :
    completedAssignment Value default first second evidence retained latentLeft latentRight
        partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration node =
      rightConfiguration ⟨node, hnode⟩ := by
  have hretained : node ∈ retained \ fixedCoordinates first second evidence := by
    rw [partition.latent.latent_cover]
    exact Finset.mem_union_right latentLeft hnode
  have hnotLeft : node ∉ latentLeft := by
    intro hleft
    exact (Finset.disjoint_left.mp partition.latent.left_right) hleft hnode
  rw [completedAssignment, fillRetained_of_mem Value _ _ _ _ hretained]
  simp [retainedDifferenceEquivLatents, hnotLeft]

def leftCoordinates [DecidableEq Node]
    (first evidence latentLeft : Finset Node) : Finset Node :=
  (first ∪ evidence) ∪ latentLeft

def rightCoordinates [DecidableEq Node]
    (second evidence latentRight : Finset Node) : Finset Node :=
  (second ∪ evidence) ∪ latentRight

/-- A left score cannot distinguish the completed assignment from one using
default configurations on the right query and latent blocks. -/
theorem leftScore_completed_eq_canonical [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (leftScore : Assignment Value → ℝ)
    (hleft : DependsOnlyOn Value (leftCoordinates first evidence latentLeft) leftScore)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight) :
    leftScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration) =
    leftScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition firstConfiguration (configurationOf Value default second)
        evidenceConfiguration leftConfiguration
          (configurationOf Value default latentRight)) := by
  apply hleft
  intro node hnode
  simp only [leftCoordinates, Finset.mem_union] at hnode
  rcases hnode with (hfirst | hevidence) | hlatent
  · rw [completedAssignment_of_first Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hfirst,
      completedAssignment_of_first Value default first second evidence retained latentLeft
        latentRight partition firstConfiguration (configurationOf Value default second)
          evidenceConfiguration leftConfiguration
            (configurationOf Value default latentRight) hfirst]
  · rw [completedAssignment_of_evidence Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hevidence,
      completedAssignment_of_evidence Value default first second evidence retained latentLeft
        latentRight partition firstConfiguration (configurationOf Value default second)
          evidenceConfiguration leftConfiguration
            (configurationOf Value default latentRight) hevidence]
  · rw [completedAssignment_of_latentLeft Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hlatent,
      completedAssignment_of_latentLeft Value default first second evidence retained latentLeft
        latentRight partition firstConfiguration (configurationOf Value default second)
          evidenceConfiguration leftConfiguration
            (configurationOf Value default latentRight) hlatent]

/-- Symmetrically, a right score cannot distinguish values supplied on the
left query and latent blocks. -/
theorem rightScore_completed_eq_canonical [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (rightScore : Assignment Value → ℝ)
    (hright : DependsOnlyOn Value (rightCoordinates second evidence latentRight) rightScore)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence)
    (leftConfiguration : Configuration Value latentLeft)
    (rightConfiguration : Configuration Value latentRight) :
    rightScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration) =
    rightScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition (configurationOf Value default first) secondConfiguration
        evidenceConfiguration (configurationOf Value default latentLeft)
          rightConfiguration) := by
  apply hright
  intro node hnode
  simp only [rightCoordinates, Finset.mem_union] at hnode
  rcases hnode with (hsecond | hevidence) | hlatent
  · rw [completedAssignment_of_second Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hsecond,
      completedAssignment_of_second Value default first second evidence retained latentLeft
        latentRight partition (configurationOf Value default first) secondConfiguration
          evidenceConfiguration (configurationOf Value default latentLeft)
            rightConfiguration hsecond]
  · rw [completedAssignment_of_evidence Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hevidence,
      completedAssignment_of_evidence Value default first second evidence retained latentLeft
        latentRight partition (configurationOf Value default first) secondConfiguration
          evidenceConfiguration (configurationOf Value default latentLeft)
            rightConfiguration hevidence]
  · rw [completedAssignment_of_latentRight Value default first second evidence retained latentLeft
      latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
        leftConfiguration rightConfiguration hlatent,
      completedAssignment_of_latentRight Value default first second evidence retained latentLeft
        latentRight partition (configurationOf Value default first) secondConfiguration
          evidenceConfiguration (configurationOf Value default latentLeft)
            rightConfiguration hlatent]

/-- Sum a full score over both latent blocks at fixed query configurations. -/
def jointTable [DecidableEq Node] [∀ node, Fintype (Value node)]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (fullScore : Assignment Value → ℝ)
    (evidenceConfiguration : Configuration Value evidence)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second) : ℝ :=
  ∑ leftConfiguration : Configuration Value latentLeft,
    ∑ rightConfiguration : Configuration Value latentRight,
      fullScore (completedAssignment Value default first second evidence retained latentLeft
        latentRight partition firstConfiguration secondConfiguration evidenceConfiguration
          leftConfiguration rightConfiguration)

/-- The left latent marginal, evaluated with canonical defaults on the right
blocks which the left score cannot read. -/
def leftTable [DecidableEq Node] [∀ node, Fintype (Value node)]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (leftScore : Assignment Value → ℝ)
    (evidenceConfiguration : Configuration Value evidence)
    (firstConfiguration : Configuration Value first) : ℝ :=
  ∑ leftConfiguration : Configuration Value latentLeft,
    leftScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition firstConfiguration (configurationOf Value default second)
        evidenceConfiguration leftConfiguration
          (configurationOf Value default latentRight))

/-- The right latent marginal, with canonical defaults on the unread left
blocks. -/
def rightTable [DecidableEq Node] [∀ node, Fintype (Value node)]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (rightScore : Assignment Value → ℝ)
    (evidenceConfiguration : Configuration Value evidence)
    (secondConfiguration : Configuration Value second) : ℝ :=
  ∑ rightConfiguration : Configuration Value latentRight,
    rightScore (completedAssignment Value default first second evidence retained
      latentLeft latentRight
      partition (configurationOf Value default first) secondConfiguration
        evidenceConfiguration (configurationOf Value default latentLeft)
          rightConfiguration)

/-- A split full score becomes a rank-one table after the two latent blocks are
summed out. -/
theorem jointTable_eq_mul [DecidableEq Node]
    [∀ node, Fintype (Value node)]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (fullScore leftScore rightScore : Assignment Value → ℝ)
    (hsplit : ∀ assignment, fullScore assignment =
      leftScore assignment * rightScore assignment)
    (hleft : DependsOnlyOn Value (leftCoordinates first evidence latentLeft) leftScore)
    (hright : DependsOnlyOn Value (rightCoordinates second evidence latentRight) rightScore) :
    ∀ evidenceConfiguration firstConfiguration secondConfiguration,
      jointTable Value default first second evidence retained latentLeft latentRight partition
          fullScore evidenceConfiguration firstConfiguration secondConfiguration =
        leftTable Value default first second evidence retained latentLeft latentRight partition
            leftScore evidenceConfiguration firstConfiguration *
          rightTable Value default first second evidence retained latentLeft latentRight partition
            rightScore evidenceConfiguration secondConfiguration := by
  intro evidenceConfiguration firstConfiguration secondConfiguration
  unfold jointTable leftTable rightTable
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro leftConfiguration _
  apply Finset.sum_congr rfl
  intro rightConfiguration _
  rw [hsplit,
    leftScore_completed_eq_canonical Value default first second evidence retained latentLeft
      latentRight partition leftScore hleft firstConfiguration secondConfiguration
        evidenceConfiguration leftConfiguration rightConfiguration,
    rightScore_completed_eq_canonical Value default first second evidence retained latentLeft
      latentRight partition rightScore hright firstConfiguration secondConfiguration
        evidenceConfiguration leftConfiguration rightConfiguration]

/-- The latent marginal therefore satisfies the division-free cross-product
identity, with no positivity or normalization assumptions. -/
theorem jointTable_crossMul [DecidableEq Node]
    [∀ node, Fintype (Value node)]
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition : ScorePartition first second evidence retained latentLeft latentRight)
    (fullScore leftScore rightScore : Assignment Value → ℝ)
    (hsplit : ∀ assignment, fullScore assignment =
      leftScore assignment * rightScore assignment)
    (hleft : DependsOnlyOn Value (leftCoordinates first evidence latentLeft) leftScore)
    (hright : DependsOnlyOn Value (rightCoordinates second evidence latentRight) rightScore) :
    ∀ evidenceConfiguration firstConfiguration secondConfiguration,
      jointTable Value default first second evidence retained latentLeft latentRight partition
          fullScore evidenceConfiguration firstConfiguration secondConfiguration *
        (∑ firstConfiguration', ∑ secondConfiguration',
          jointTable Value default first second evidence retained latentLeft latentRight partition
            fullScore evidenceConfiguration firstConfiguration' secondConfiguration') =
      (∑ secondConfiguration',
          jointTable Value default first second evidence retained latentLeft latentRight partition
            fullScore evidenceConfiguration firstConfiguration secondConfiguration') *
        ∑ firstConfiguration',
          jointTable Value default first second evidence retained latentLeft latentRight partition
            fullScore evidenceConfiguration firstConfiguration' secondConfiguration := by
  exact crossMul_of_rankOne
    (jointTable Value default first second evidence retained latentLeft latentRight
      partition fullScore)
    (leftTable Value default first second evidence retained latentLeft latentRight
      partition leftScore)
    (rightTable Value default first second evidence retained latentLeft latentRight
      partition rightScore)
    (jointTable_eq_mul Value default first second evidence retained latentLeft latentRight partition
      fullScore leftScore rightScore hsplit hleft hright)

/-! ## Hostile finite controls -/

namespace Control

inductive ControlNode where
  | first
  | second
  | evidence
  | latentLeft
  | latentRight
  deriving DecidableEq, Fintype

abbrev ControlValue (_ : ControlNode) := Bool

def firstCoordinates : Finset ControlNode := {.first}

def secondCoordinates : Finset ControlNode := {.second}

def evidenceCoordinates : Finset ControlNode := {.evidence}

def retainedCoordinates : Finset ControlNode := Finset.univ

def latentLeftCoordinates : Finset ControlNode := {.latentLeft}

def latentRightCoordinates : Finset ControlNode := {.latentRight}

theorem partition : ScorePartition firstCoordinates secondCoordinates evidenceCoordinates
    retainedCoordinates latentLeftCoordinates latentRightCoordinates := by
  refine
    { first_second := by simp [firstCoordinates, secondCoordinates]
      first_evidence := by simp [firstCoordinates, evidenceCoordinates]
      second_evidence := by simp [secondCoordinates, evidenceCoordinates]
      fixed_subset := by simp [retainedCoordinates]
      latent :=
        { left_right := by
            simp [latentLeftCoordinates, latentRightCoordinates]
          latent_cover := by
            ext node
            cases node <;>
              simp [retainedCoordinates, fixedCoordinates, firstCoordinates,
                secondCoordinates, evidenceCoordinates, latentLeftCoordinates,
                latentRightCoordinates] } }

def default : Assignment ControlValue := fun _ => false

def leftScore (assignment : Assignment ControlValue) : ℝ :=
  if assignment .first then 2 else 1

def rightScore (assignment : Assignment ControlValue) : ℝ :=
  if assignment .second then 3 else 1

def productScore (assignment : Assignment ControlValue) : ℝ :=
  leftScore assignment * rightScore assignment

theorem productScore_split (assignment : Assignment ControlValue) :
    productScore assignment = leftScore assignment * rightScore assignment :=
  rfl

theorem leftScore_dependsOnlyOn :
    DependsOnlyOn ControlValue
      (leftCoordinates firstCoordinates evidenceCoordinates latentLeftCoordinates)
      leftScore := by
  intro firstAssignment secondAssignment hagree
  unfold leftScore
  rw [hagree .first (by
    simp [leftCoordinates, firstCoordinates])]

theorem rightScore_dependsOnlyOn :
    DependsOnlyOn ControlValue
      (rightCoordinates secondCoordinates evidenceCoordinates latentRightCoordinates)
      rightScore := by
  intro firstAssignment secondAssignment hagree
  unfold rightScore
  rw [hagree .second (by
    simp [rightCoordinates, secondCoordinates])]

abbrev productJoint :=
  jointTable ControlValue default firstCoordinates secondCoordinates evidenceCoordinates
    retainedCoordinates latentLeftCoordinates latentRightCoordinates partition productScore

/-- A genuinely nonconstant product score passes the complete dependent
assembly, latent-sum, and cross-product path. -/
theorem productScore_crossMul :
    ∀ evidenceConfiguration firstConfiguration secondConfiguration,
      productJoint evidenceConfiguration firstConfiguration secondConfiguration *
        (∑ firstConfiguration', ∑ secondConfiguration',
          productJoint evidenceConfiguration firstConfiguration' secondConfiguration') =
      (∑ secondConfiguration',
          productJoint evidenceConfiguration firstConfiguration secondConfiguration') *
        ∑ firstConfiguration',
          productJoint evidenceConfiguration firstConfiguration' secondConfiguration := by
  exact jointTable_crossMul ControlValue default firstCoordinates secondCoordinates
    evidenceCoordinates retainedCoordinates latentLeftCoordinates latentRightCoordinates partition
      productScore leftScore rightScore productScore_split
        leftScore_dependsOnlyOn rightScore_dependsOnlyOn

/-- The nearby diagonal table cannot provide the adapter's rank-one input;
otherwise `crossMul_of_rankOne` would contradict its explicit bad minor. -/
theorem diagonal_has_no_rankOne_factorization :
    ¬ ∃ (left : Unit → Fin 2 → ℕ) (right : Unit → Fin 2 → ℕ),
      ∀ z x y,
        FiniteBNRankOne.Controls.diagonal z x y = left z x * right z y := by
  rintro ⟨left, right, hfactor⟩
  apply FiniteBNRankOne.Controls.diagonal_rejects_crossMul
  exact crossMul_of_rankOne FiniteBNRankOne.Controls.diagonal left right hfactor ()

end Control

end GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly
