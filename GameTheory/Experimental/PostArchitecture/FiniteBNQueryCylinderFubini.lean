/-
# EXP-104: query-cylinder finite Fubini identities

For three pairwise-disjoint typed query blocks, summing exact joint cylinders
over one query configuration gives the corresponding smaller cylinder.  The
proof is probability-only: it reuses retained-cylinder decomposition and a
transport-free equivalence between a newly retained block and `retained \ fixed`.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
import GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNQueryCylinderFubini

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
open GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- One newly retained block is exactly the difference between the retained
and fixed coordinate sets. -/
structure ExtensionPartition [DecidableEq Node]
    (fixed retained new : Finset Node) : Prop where
  fixed_subset : fixed ⊆ retained
  remaining_iff : ∀ node, node ∈ retained \ fixed ↔ node ∈ new

/-- Reindex configurations on a named new block as configurations on the
corresponding retained-set difference. -/
def configurationEquivRemaining [DecidableEq Node]
    (fixed retained new : Finset Node)
    (partition : ExtensionPartition fixed retained new) :
    Configuration Value new ≃ Configuration Value (retained \ fixed) where
  toFun configuration node :=
    configuration ⟨node.1, (partition.remaining_iff node.1).mp node.2⟩
  invFun configuration node :=
    configuration ⟨node.1, (partition.remaining_iff node.1).mpr node.2⟩
  left_inv configuration := by
    funext node
    rfl
  right_inv configuration := by
    funext node
    rfl

/-- Extend a fixed-coordinate witness by a configuration on the named new
block. -/
def extendWitness [DecidableEq Node]
    (fixed retained new : Finset Node)
    (partition : ExtensionPartition fixed retained new)
    (witness : Assignment Value) (configuration : Configuration Value new) :
    Assignment Value :=
  fillRetained Value fixed retained witness
    (configurationEquivRemaining Value fixed retained new partition configuration)

/-- Finite Fubini for adjoining one named coordinate block. -/
theorem sum_cylinderMass_extensions
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (fixed retained new : Finset Node)
    (partition : ExtensionPartition fixed retained new)
    (witness : Assignment Value) :
    (∑ configuration : Configuration Value new,
      cylinderMass Value law retained
        (extendWitness Value fixed retained new partition witness configuration)) =
      cylinderMass Value law fixed witness := by
  let equivalence := configurationEquivRemaining Value fixed retained new partition
  calc
    (∑ configuration : Configuration Value new,
        cylinderMass Value law retained
          (extendWitness Value fixed retained new partition witness configuration)) =
        ∑ remaining : Configuration Value (retained \ fixed),
          cylinderMass Value law retained
            (fillRetained Value fixed retained witness remaining) := by
      apply Fintype.sum_equiv equivalence
      intro configuration
      rfl
    _ = cylinderMass Value law fixed witness :=
      (cylinderMass_eq_sum_retained Value law fixed retained
        partition.fixed_subset witness).symm

/-- Cylinder mass depends only on the witness coordinates inside the cylinder. -/
theorem cylinderMass_eq_of_witnesses_agree
    (law : FinDist (Assignment Value)) (nodes : Finset Node)
    {firstWitness secondWitness : Assignment Value}
    (hagrees : AgreeOn Value nodes firstWitness secondWitness) :
    cylinderMass Value law nodes firstWitness =
      cylinderMass Value law nodes secondWitness := by
  unfold cylinderMass
  apply congrArg (FinDist.probOf law)
  ext assignment
  constructor
  · intro hfirst node hnode
    exact (hfirst node hnode).trans (hagrees node hnode)
  · intro hsecond node hnode
    exact (hsecond node hnode).trans (hagrees node hnode).symm

def firstEvidence [DecidableEq Node]
    (first evidence : Finset Node) : Finset Node :=
  first ∪ evidence

def secondEvidence [DecidableEq Node]
    (second evidence : Finset Node) : Finset Node :=
  second ∪ evidence

theorem second_extension_partition [DecidableEq Node]
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hsecondEvidence : Disjoint second evidence) :
    ExtensionPartition (firstEvidence first evidence)
      (fixedCoordinates first second evidence) second := by
  refine ⟨?_, ?_⟩
  · intro node hnode
    simp only [firstEvidence, fixedCoordinates, Finset.mem_union] at hnode ⊢
    tauto
  · intro node
    have hnotFirstSecond : ¬ (node ∈ first ∧ node ∈ second) :=
      fun hboth => (Finset.disjoint_left.mp hfirstSecond) hboth.1 hboth.2
    have hnotSecondEvidence : ¬ (node ∈ second ∧ node ∈ evidence) :=
      fun hboth => (Finset.disjoint_left.mp hsecondEvidence) hboth.1 hboth.2
    simp only [Finset.mem_sdiff, firstEvidence, fixedCoordinates, Finset.mem_union]
    tauto

theorem first_extension_partition [DecidableEq Node]
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence) :
    ExtensionPartition (secondEvidence second evidence)
      (fixedCoordinates first second evidence) first := by
  refine ⟨?_, ?_⟩
  · intro node hnode
    simp only [secondEvidence, fixedCoordinates, Finset.mem_union] at hnode ⊢
    tauto
  · intro node
    have hnotFirstSecond : ¬ (node ∈ first ∧ node ∈ second) :=
      fun hboth => (Finset.disjoint_left.mp hfirstSecond) hboth.1 hboth.2
    have hnotFirstEvidence : ¬ (node ∈ first ∧ node ∈ evidence) :=
      fun hboth => (Finset.disjoint_left.mp hfirstEvidence) hboth.1 hboth.2
    simp only [Finset.mem_sdiff, secondEvidence, fixedCoordinates, Finset.mem_union]
    tauto

theorem first_evidence_extension_partition [DecidableEq Node]
    (first evidence : Finset Node) (hfirstEvidence : Disjoint first evidence) :
    ExtensionPartition evidence (firstEvidence first evidence) first := by
  refine ⟨?_, ?_⟩
  · intro node hnode
    exact Finset.mem_union_right first hnode
  · intro node
    have hnotFirstEvidence : ¬ (node ∈ first ∧ node ∈ evidence) :=
      fun hboth => (Finset.disjoint_left.mp hfirstEvidence) hboth.1 hboth.2
    simp only [Finset.mem_sdiff, firstEvidence, Finset.mem_union]
    tauto

theorem queryWitness_agrees_second_extension [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hsecondEvidence : Disjoint second evidence)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence) :
    AgreeOn Value (fixedCoordinates first second evidence)
      (queryWitness Value default first second evidence firstConfiguration
        secondConfiguration evidenceConfiguration)
      (extendWitness Value (firstEvidence first evidence)
        (fixedCoordinates first second evidence) second
        (second_extension_partition first second evidence hfirstSecond hsecondEvidence)
        (queryWitness Value default first second evidence firstConfiguration
          (configurationOf Value default second) evidenceConfiguration)
        secondConfiguration) := by
  intro node hnode
  by_cases hsecond : node ∈ second
  · have hnotFirst : node ∉ first := by
      intro hfirst
      exact (Finset.disjoint_left.mp hfirstSecond) hfirst hsecond
    have hremaining :
        node ∈ fixedCoordinates first second evidence \ firstEvidence first evidence :=
      (ExtensionPartition.remaining_iff
        (second_extension_partition first second evidence hfirstSecond hsecondEvidence)
          node).mpr hsecond
    rw [extendWitness, fillRetained_of_mem Value _ _ _ _ hremaining]
    simp [configurationEquivRemaining, queryWitness, hnotFirst, hsecond]
  · have hnotRemaining :
        node ∉ fixedCoordinates first second evidence \ firstEvidence first evidence := by
      intro hremaining
      exact hsecond
        ((ExtensionPartition.remaining_iff
          (second_extension_partition first second evidence hfirstSecond hsecondEvidence)
            node).mp hremaining)
    rw [extendWitness, fillRetained_of_notMem Value _ _ _ _ hnotRemaining]
    simp [queryWitness, hsecond]

theorem queryWitness_agrees_first_extension [DecidableEq Node]
    (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence) :
    AgreeOn Value (fixedCoordinates first second evidence)
      (queryWitness Value default first second evidence firstConfiguration
        secondConfiguration evidenceConfiguration)
      (extendWitness Value (secondEvidence second evidence)
        (fixedCoordinates first second evidence) first
        (first_extension_partition first second evidence hfirstSecond hfirstEvidence)
        (queryWitness Value default first second evidence
          (configurationOf Value default first) secondConfiguration evidenceConfiguration)
        firstConfiguration) := by
  intro node hnode
  by_cases hfirst : node ∈ first
  · have hremaining :
        node ∈ fixedCoordinates first second evidence \ secondEvidence second evidence :=
      (ExtensionPartition.remaining_iff
        (first_extension_partition first second evidence hfirstSecond hfirstEvidence)
          node).mpr hfirst
    rw [extendWitness, fillRetained_of_mem Value _ _ _ _ hremaining]
    simp [configurationEquivRemaining, queryWitness, hfirst]
  · have hnotRemaining :
        node ∉ fixedCoordinates first second evidence \ secondEvidence second evidence := by
      intro hremaining
      exact hfirst
        ((ExtensionPartition.remaining_iff
          (first_extension_partition first second evidence hfirstSecond hfirstEvidence)
            node).mp hremaining)
    rw [extendWitness, fillRetained_of_notMem Value _ _ _ _ hnotRemaining]
    simp [queryWitness, hfirst]

/-- Summing the `XYZ` cylinder over `Y` gives the `XZ` cylinder. -/
theorem sum_second_queryCylinders
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value)) (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hsecondEvidence : Disjoint second evidence)
    (firstConfiguration : Configuration Value first)
    (evidenceConfiguration : Configuration Value evidence) :
    (∑ secondConfiguration : Configuration Value second,
      cylinderMass Value law (fixedCoordinates first second evidence)
        (queryWitness Value default first second evidence firstConfiguration
          secondConfiguration evidenceConfiguration)) =
      cylinderMass Value law (firstEvidence first evidence)
        (queryWitness Value default first second evidence firstConfiguration
          (configurationOf Value default second) evidenceConfiguration) := by
  let partition :=
    second_extension_partition first second evidence hfirstSecond hsecondEvidence
  calc
    _ = ∑ secondConfiguration : Configuration Value second,
        cylinderMass Value law (fixedCoordinates first second evidence)
          (extendWitness Value (firstEvidence first evidence)
            (fixedCoordinates first second evidence) second partition
            (queryWitness Value default first second evidence firstConfiguration
              (configurationOf Value default second) evidenceConfiguration)
            secondConfiguration) := by
      apply Finset.sum_congr rfl
      intro secondConfiguration _
      apply cylinderMass_eq_of_witnesses_agree
      exact queryWitness_agrees_second_extension Value default first second evidence
        hfirstSecond hsecondEvidence firstConfiguration secondConfiguration
          evidenceConfiguration
    _ = _ := sum_cylinderMass_extensions Value law (firstEvidence first evidence)
      (fixedCoordinates first second evidence) second partition _

/-- Summing the `XYZ` cylinder over `X` gives the `YZ` cylinder. -/
theorem sum_first_queryCylinders
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value)) (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence) :
    (∑ firstConfiguration : Configuration Value first,
      cylinderMass Value law (fixedCoordinates first second evidence)
        (queryWitness Value default first second evidence firstConfiguration
          secondConfiguration evidenceConfiguration)) =
      cylinderMass Value law (secondEvidence second evidence)
        (queryWitness Value default first second evidence
          (configurationOf Value default first) secondConfiguration
            evidenceConfiguration) := by
  let partition :=
    first_extension_partition first second evidence hfirstSecond hfirstEvidence
  calc
    _ = ∑ firstConfiguration : Configuration Value first,
        cylinderMass Value law (fixedCoordinates first second evidence)
          (extendWitness Value (secondEvidence second evidence)
            (fixedCoordinates first second evidence) first partition
            (queryWitness Value default first second evidence
              (configurationOf Value default first) secondConfiguration
                evidenceConfiguration) firstConfiguration) := by
      apply Finset.sum_congr rfl
      intro firstConfiguration _
      apply cylinderMass_eq_of_witnesses_agree
      exact queryWitness_agrees_first_extension Value default first second evidence
        hfirstSecond hfirstEvidence firstConfiguration secondConfiguration
          evidenceConfiguration
    _ = _ := sum_cylinderMass_extensions Value law (secondEvidence second evidence)
      (fixedCoordinates first second evidence) first partition _

theorem sum_firstEvidence_queryCylinders
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value)) (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstEvidence : Disjoint first evidence)
    (evidenceConfiguration : Configuration Value evidence) :
    (∑ firstConfiguration : Configuration Value first,
      cylinderMass Value law (firstEvidence first evidence)
        (queryWitness Value default first second evidence firstConfiguration
          (configurationOf Value default second) evidenceConfiguration)) =
      cylinderMass Value law evidence
        (queryWitness Value default first second evidence
          (configurationOf Value default first) (configurationOf Value default second)
            evidenceConfiguration) := by
  let partition := first_evidence_extension_partition first evidence hfirstEvidence
  let witness := queryWitness Value default first second evidence
    (configurationOf Value default first) (configurationOf Value default second)
      evidenceConfiguration
  calc
    _ = ∑ firstConfiguration : Configuration Value first,
        cylinderMass Value law (firstEvidence first evidence)
          (extendWitness Value evidence (firstEvidence first evidence) first partition
            witness firstConfiguration) := by
      apply Finset.sum_congr rfl
      intro firstConfiguration _
      apply cylinderMass_eq_of_witnesses_agree
      intro node hnode
      by_cases hfirst : node ∈ first
      · have hremaining : node ∈ firstEvidence first evidence \ evidence :=
          partition.remaining_iff node |>.mpr hfirst
        rw [extendWitness, fillRetained_of_mem Value _ _ _ _ hremaining]
        simp [configurationEquivRemaining, queryWitness, hfirst]
      · have hnotRemaining : node ∉ firstEvidence first evidence \ evidence := by
          intro hremaining
          exact hfirst (partition.remaining_iff node |>.mp hremaining)
        rw [extendWitness, fillRetained_of_notMem Value _ _ _ _ hnotRemaining]
        simp [witness, queryWitness, hfirst]
    _ = _ := sum_cylinderMass_extensions Value law evidence
      (firstEvidence first evidence) first partition witness

/-- Summing over both query blocks gives the evidence cylinder. -/
theorem sum_first_second_queryCylinders
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value)) (default : Assignment Value)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (hsecondEvidence : Disjoint second evidence)
    (evidenceConfiguration : Configuration Value evidence) :
    (∑ firstConfiguration : Configuration Value first,
      ∑ secondConfiguration : Configuration Value second,
        cylinderMass Value law (fixedCoordinates first second evidence)
          (queryWitness Value default first second evidence firstConfiguration
            secondConfiguration evidenceConfiguration)) =
      cylinderMass Value law evidence
        (queryWitness Value default first second evidence
          (configurationOf Value default first) (configurationOf Value default second)
            evidenceConfiguration) := by
  calc
    _ = ∑ firstConfiguration : Configuration Value first,
        cylinderMass Value law (firstEvidence first evidence)
          (queryWitness Value default first second evidence firstConfiguration
            (configurationOf Value default second) evidenceConfiguration) := by
      apply Finset.sum_congr rfl
      intro firstConfiguration _
      exact sum_second_queryCylinders Value law default first second evidence
        hfirstSecond hsecondEvidence firstConfiguration
          evidenceConfiguration
    _ = _ := sum_firstEvidence_queryCylinders Value law default first second evidence
      hfirstEvidence evidenceConfiguration

/-! ## Empty-block and singleton-domain sentinel -/

namespace Sentinel

abbrev SentinelValue (_ : Unit) := Unit

def default : Assignment SentinelValue := fun _ => ()

def law : FinDist (Assignment SentinelValue) := FinDist.pure default

def first : Finset Unit := ∅

def second : Finset Unit := {()}

def evidence : Finset Unit := ∅

theorem empty_singleton_sum :
    (∑ secondConfiguration : Configuration SentinelValue second,
      cylinderMass SentinelValue law (fixedCoordinates first second evidence)
        (queryWitness SentinelValue default first second evidence
          (configurationOf SentinelValue default first) secondConfiguration
            (configurationOf SentinelValue default evidence))) =
      cylinderMass SentinelValue law (firstEvidence first evidence)
        (queryWitness SentinelValue default first second evidence
          (configurationOf SentinelValue default first)
          (configurationOf SentinelValue default second)
          (configurationOf SentinelValue default evidence)) := by
  simpa [first, second, evidence, queryWitness, configurationOf] using
    sum_second_queryCylinders SentinelValue law default first second evidence
      (by simp [first, second]) (by simp [second, evidence])
      (configurationOf SentinelValue default first)
        (configurationOf SentinelValue default evidence)

end Sentinel

end GameTheory.Experimental.PostArchitecture.FiniteBNQueryCylinderFubini
