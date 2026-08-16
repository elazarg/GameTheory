/-
# EXP-104: MAID cylinder bridge

This file identifies the generic dependent-assignment cylinders used by finite
Bayesian-network marginalization with the typed restriction cylinders used by
the MAID coordinate specialization.  It introduces no third event or
conditional-independence notion.

All equalities use one complete witness.  Agreement on a union is equivalent
to agreement of its typed restrictions, without disjointness assumptions or
equality transport in the API.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
import GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDCylinderBridge

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- A typed restriction cylinder at the witness is exactly generic agreement
on the same node set. -/
theorem cylinder_eq_agreeOn (nodes : Finset Node)
    (witness : Assignment diagram) :
    cylinder nodes (Assignment.restrict diagram witness nodes) =
      {assignment | AgreeOn diagram.Value nodes assignment witness} := by
  ext assignment
  constructor
  · intro restrictionEquality node hnode
    exact congrFun restrictionEquality ⟨node, hnode⟩
  · intro hagrees
    funext node
    exact hagrees node.1 node.2

/-- Two typed restriction cylinders at one witness are agreement on the union
of their coordinate sets. -/
theorem pairCylinder_eq_agreeOn (first second : Finset Node)
    [DecidableEq Node]
    (witness : Assignment diagram) :
    pairCylinder first second
        (Assignment.restrict diagram witness first)
        (Assignment.restrict diagram witness second) =
      {assignment | AgreeOn diagram.Value (first ∪ second) assignment witness} := by
  ext assignment
  constructor
  · rintro ⟨firstEquality, secondEquality⟩ node hnode
    rcases Finset.mem_union.mp hnode with hfirst | hsecond
    · exact congrFun firstEquality ⟨node, hfirst⟩
    · exact congrFun secondEquality ⟨node, hsecond⟩
  · intro hagrees
    constructor
    · funext node
      exact hagrees node.1 (Finset.mem_union_left second node.2)
    · funext node
      exact hagrees node.1 (Finset.mem_union_right first node.2)

/-- Three typed restriction cylinders at one witness are agreement on the
three-way union. -/
theorem tripleCylinder_eq_agreeOn
    (first second evidence : Finset Node)
    [DecidableEq Node]
    (witness : Assignment diagram) :
    tripleCylinder first second evidence
        (Assignment.restrict diagram witness first)
        (Assignment.restrict diagram witness second)
        (Assignment.restrict diagram witness evidence) =
      {assignment |
        AgreeOn diagram.Value (first ∪ second ∪ evidence)
          assignment witness} := by
  ext assignment
  constructor
  · rintro ⟨firstEquality, secondEquality, evidenceEquality⟩ node hnode
    rcases Finset.mem_union.mp hnode with hfirstSecond | hevidence
    · rcases Finset.mem_union.mp hfirstSecond with hfirst | hsecond
      · exact congrFun firstEquality ⟨node, hfirst⟩
      · exact congrFun secondEquality ⟨node, hsecond⟩
    · exact congrFun evidenceEquality ⟨node, hevidence⟩
  · intro hagrees
    refine ⟨?_, ?_, ?_⟩
    · funext node
      exact hagrees node.1
        (Finset.mem_union_left evidence
          (Finset.mem_union_left second node.2))
    · funext node
      exact hagrees node.1
        (Finset.mem_union_left evidence
          (Finset.mem_union_right first node.2))
    · funext node
      exact hagrees node.1
        (Finset.mem_union_right (first ∪ second) node.2)

/-- The one-set typed cylinder mass is the generic cylinder mass. -/
theorem cylinder_probOf_eq_cylinderMass
    (law : FinDist (Assignment diagram)) (nodes : Finset Node)
    (witness : Assignment diagram) :
    law.probOf
        (cylinder nodes (Assignment.restrict diagram witness nodes)) =
      cylinderMass diagram.Value law nodes witness := by
  rw [cylinderMass, cylinder_eq_agreeOn]
  rfl

/-- The same-witness pair-cylinder mass is the generic mass on the union. -/
theorem pairCylinder_probOf_eq_cylinderMass
    (law : FinDist (Assignment diagram)) (first second : Finset Node)
    [DecidableEq Node]
    (witness : Assignment diagram) :
    law.probOf
        (pairCylinder first second
          (Assignment.restrict diagram witness first)
          (Assignment.restrict diagram witness second)) =
      cylinderMass diagram.Value law (first ∪ second) witness := by
  rw [cylinderMass, pairCylinder_eq_agreeOn]
  rfl

/-- The same-witness triple-cylinder mass is the generic mass on the
three-way union. -/
theorem tripleCylinder_probOf_eq_cylinderMass
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node)
    [DecidableEq Node]
    (witness : Assignment diagram) :
    law.probOf
        (tripleCylinder first second evidence
          (Assignment.restrict diagram witness first)
          (Assignment.restrict diagram witness second)
          (Assignment.restrict diagram witness evidence)) =
      cylinderMass diagram.Value law (first ∪ second ∪ evidence) witness := by
  rw [cylinderMass, tripleCylinder_eq_agreeOn]
  rfl

/-- The coordinate cross-product theorem reads directly as the four generic
union-cylinder masses used by marginalization. -/
theorem sameWitness_cylinderMass_cross_product
    (law : FinDist (Assignment diagram))
    (first second evidence : Finset Node)
    [DecidableEq Node]
    (hindependent :
      CoordinatesConditionallyIndependent law first second evidence)
    (witness : Assignment diagram) :
    cylinderMass diagram.Value law (first ∪ second ∪ evidence) witness *
        cylinderMass diagram.Value law evidence witness =
      cylinderMass diagram.Value law (first ∪ evidence) witness *
        cylinderMass diagram.Value law (second ∪ evidence) witness := by
  have hcross := sameWitness_cross_product law first second evidence
    hindependent witness
  rw [tripleCylinder_probOf_eq_cylinderMass,
    cylinder_probOf_eq_cylinderMass,
    pairCylinder_probOf_eq_cylinderMass,
    pairCylinder_probOf_eq_cylinderMass] at hcross
  exact hcross

/-! ## Dependent Boolean control -/

namespace BoolControl

open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence

def allCoordinates : Finset ControlNode :=
  firstCoordinates ∪ secondCoordinates ∪ evidenceCoordinates

/-- The generic cylinder fixing every Boolean coordinate to the point-law
witness has mass one. -/
theorem all_cylinderMass :
    cylinderMass controlDiagram.Value controlLaw allCoordinates
      controlAssignment = 1 := by
  unfold cylinderMass controlLaw
  apply FinDist.probOf_pure_self
  intro _ _
  rfl

/-- The typed three-restriction cylinder computes the same unit mass through
the bridge. -/
theorem tripleCylinder_mass :
    controlLaw.probOf
        (tripleCylinder firstCoordinates secondCoordinates evidenceCoordinates
          (Assignment.restrict controlDiagram controlAssignment firstCoordinates)
          (Assignment.restrict controlDiagram controlAssignment secondCoordinates)
          (Assignment.restrict controlDiagram controlAssignment evidenceCoordinates)) =
      1 := by
  rw [tripleCylinder_probOf_eq_cylinderMass]
  exact all_cylinderMass

end BoolControl

end GameTheory.Experimental.PostArchitecture.MAIDCylinderBridge
