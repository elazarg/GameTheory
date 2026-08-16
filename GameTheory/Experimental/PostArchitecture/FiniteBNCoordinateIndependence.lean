/-
# EXP-104: dependent coordinate cylinders

This file specializes the experiment's single finite-law conditional-
independence predicate to typed MAID assignments.  Coordinates are observed by
`Assignment.restrict`; no second conditional-independence notion is introduced.

Cylinder statements retain complete dependent `Config` values.  In particular,
the same-witness theorem never combines configurations with casts.  A future
graph theorem can impose pairwise-disjoint coordinate sets at its own boundary;
the probability identity itself does not need that assumption.
-/

import GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
import GameTheory.Languages.MAID.Basic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- The cylinder cut out by one typed local configuration. -/
def cylinder (nodes : Finset Node) (configuration : Config diagram nodes) :
    Set (Assignment diagram) :=
  {assignment | Assignment.restrict diagram assignment nodes = configuration}

/-- A two-set cylinder, kept in separated form so no configuration transport is
needed. -/
def pairCylinder (first second : Finset Node)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second) :
    Set (Assignment diagram) :=
  {assignment |
    Assignment.restrict diagram assignment first = firstConfiguration ∧
      Assignment.restrict diagram assignment second = secondConfiguration}

/-- A three-set cylinder, again represented by its three typed restrictions. -/
def tripleCylinder (first second evidence : Finset Node)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    Set (Assignment diagram) :=
  {assignment |
    Assignment.restrict diagram assignment first = firstConfiguration ∧
      Assignment.restrict diagram assignment second = secondConfiguration ∧
        Assignment.restrict diagram assignment evidence = evidenceConfiguration}

/-- Coordinate conditional independence is the existing observable predicate
specialized transparently to three dependent restriction maps. -/
abbrev CoordinatesConditionallyIndependent
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node) : Prop :=
  IsConditionallyIndependent law
    (fun assignment => Assignment.restrict diagram assignment first)
    (fun assignment => Assignment.restrict diagram assignment second)
    (fun assignment => Assignment.restrict diagram assignment evidence)

/-- The coordinate API is definitionally the observable API, not a parallel
notion requiring a bridge theorem. -/
theorem coordinatesConditionallyIndependent_iff
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node) :
    CoordinatesConditionallyIndependent law first second evidence ↔
      IsConditionallyIndependent law
        (fun assignment => Assignment.restrict diagram assignment first)
        (fun assignment => Assignment.restrict diagram assignment second)
        (fun assignment => Assignment.restrict diagram assignment evidence) :=
  Iff.rfl

theorem restriction_atom_eq_cylinder
    (nodes : Finset Node) (configuration : Config diagram nodes) :
    atom (fun assignment => Assignment.restrict diagram assignment nodes)
        configuration =
      cylinder nodes configuration :=
  rfl

theorem restriction_pairAtom_eq_pairCylinder
    (first second : Finset Node)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second) :
    pairAtom
        (fun assignment => Assignment.restrict diagram assignment first)
        (fun assignment => Assignment.restrict diagram assignment second)
        firstConfiguration secondConfiguration =
      pairCylinder first second firstConfiguration secondConfiguration :=
  rfl

theorem restriction_tripleAtom_eq_tripleCylinder
    (first second evidence : Finset Node)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    tripleAtom
        (fun assignment => Assignment.restrict diagram assignment first)
        (fun assignment => Assignment.restrict diagram assignment second)
        (fun assignment => Assignment.restrict diagram assignment evidence)
        firstConfiguration secondConfiguration evidenceConfiguration =
      tripleCylinder first second evidence firstConfiguration
        secondConfiguration evidenceConfiguration :=
  rfl

/-- Unfolding coordinate conditional independence gives exactly the four
cylinder masses in the division-free cross-product identity. -/
theorem coordinatesConditionallyIndependent_iff_cylinders
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node) :
    CoordinatesConditionallyIndependent law first second evidence ↔
      ∀ (firstConfiguration : Config diagram first)
        (secondConfiguration : Config diagram second)
        (evidenceConfiguration : Config diagram evidence),
        law.probOf
              (tripleCylinder first second evidence firstConfiguration
                secondConfiguration evidenceConfiguration) *
            law.probOf (cylinder evidence evidenceConfiguration) =
          law.probOf
              (pairCylinder first evidence firstConfiguration
                evidenceConfiguration) *
            law.probOf
              (pairCylinder second evidence secondConfiguration
                evidenceConfiguration) :=
  Iff.rfl

/-- One complete assignment gives compatible local configurations and hence
the expected same-witness cylinder identity.  No gluing operation, transport,
or disjointness premise is needed. -/
theorem sameWitness_cross_product
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node)
    (hindependent :
      CoordinatesConditionallyIndependent law first second evidence)
    (witness : Assignment diagram) :
    law.probOf
          (tripleCylinder first second evidence
            (Assignment.restrict diagram witness first)
            (Assignment.restrict diagram witness second)
            (Assignment.restrict diagram witness evidence)) *
        law.probOf
          (cylinder evidence (Assignment.restrict diagram witness evidence)) =
      law.probOf
          (pairCylinder first evidence
            (Assignment.restrict diagram witness first)
            (Assignment.restrict diagram witness evidence)) *
        law.probOf
          (pairCylinder second evidence
            (Assignment.restrict diagram witness second)
            (Assignment.restrict diagram witness evidence)) :=
  (coordinatesConditionallyIndependent_iff_cylinders law
    first second evidence).mp hindependent _ _ _

/-! ## A dependent zero-evidence coordinate control -/

inductive ControlNode
  | first
  | second
  | evidence
  deriving DecidableEq, Fintype

def controlParents (_ : ControlNode) : Finset ControlNode := ∅

def controlTopological :
    GameTheory.Math.DAG.TopologicalOrder controlParents where
  order := [.first, .second, .evidence]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro _ parent hparent
    simp [controlParents] at hparent

@[reducible]
def controlDiagram : Structure Unit ControlNode where
  kind _ := .chance
  parents := controlParents
  observedParents _ := ∅
  Value _ := Bool
  observed_sub _ := by simp [controlParents]
  observed_eq_of_chance _ _ := by simp [controlParents]
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    controlTopological

def controlAssignment : Assignment controlDiagram := fun _ => false

def controlLaw : FinDist (Assignment controlDiagram) :=
  FinDist.pure controlAssignment

def firstCoordinates : Finset ControlNode := {.first}

def secondCoordinates : Finset ControlNode := {.second}

def evidenceCoordinates : Finset ControlNode := {.evidence}

/-- The point-mass dependent assignment satisfies the coordinate predicate. -/
theorem control_coordinatesConditionallyIndependent :
    CoordinatesConditionallyIndependent controlLaw
      firstCoordinates secondCoordinates evidenceCoordinates :=
  pure_conditionallyIndependent controlAssignment _ _ _

def impossibleEvidenceConfiguration :
    Config controlDiagram evidenceCoordinates :=
  fun _ => true

/-- The evidence cylinder requiring `true` has zero mass, demonstrating that
the coordinate specialization preserves the base predicate's zero-evidence
behavior. -/
theorem impossibleEvidenceCylinder_mass_zero :
    controlLaw.probOf
      (cylinder evidenceCoordinates impossibleEvidenceConfiguration) = 0 := by
  have hnot : controlAssignment ∉
      cylinder evidenceCoordinates impossibleEvidenceConfiguration := by
    intro equality
    have hvalue := congrFun equality
      (⟨.evidence, by simp [evidenceCoordinates]⟩ :
        {node // node ∈ evidenceCoordinates})
    simp [Assignment.restrict, controlAssignment,
      impossibleEvidenceConfiguration] at hvalue
  show (FinDist.pure controlAssignment).probOf
    (cylinder evidenceCoordinates impossibleEvidenceConfiguration) = 0
  classical
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
  simp [hnot]

end GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
