/-
# EXP-104: finite global-Markov soundness

This module composes canonical point-mass factorization, parent-closed
marginalization, ancestral-moral factor separation, dependent rank-one score
assembly, and cylinder Fubini.  The conclusion is division-free conditional
independence for arbitrary typed query configurations, including impossible
evidence values.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMoralScoreBridge
import GameTheory.Experimental.PostArchitecture.FiniteBNQueryCylinderFubini
import GameTheory.Experimental.PostArchitecture.FiniteBNScoreCylinderBridge
import GameTheory.Experimental.PostArchitecture.MAIDCylinderBridge

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralScoreBridge
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.FiniteBNQueryCylinderFubini
open GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly
open GameTheory.Experimental.PostArchitecture.FiniteBNScoreCylinderBridge
open GameTheory.Experimental.PostArchitecture.MAIDCylinderBridge

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

private theorem queryWitness_restrict_first
    [DecidableEq Node]
    (default : Assignment diagram)
    (first second evidence : Finset Node)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    Assignment.restrict diagram
        (queryWitness diagram.Value default first second evidence
          firstConfiguration secondConfiguration evidenceConfiguration) first =
      firstConfiguration := by
  funext node
  exact queryWitness_of_first diagram.Value default first second evidence
    firstConfiguration secondConfiguration evidenceConfiguration node.2

private theorem queryWitness_restrict_second
    [DecidableEq Node]
    (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    Assignment.restrict diagram
        (queryWitness diagram.Value default first second evidence
          firstConfiguration secondConfiguration evidenceConfiguration) second =
      secondConfiguration := by
  funext node
  exact queryWitness_of_second diagram.Value default first second evidence
    retained latentLeft latentRight partition firstConfiguration
      secondConfiguration evidenceConfiguration node.2

private theorem queryWitness_restrict_evidence
    [DecidableEq Node]
    (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    Assignment.restrict diagram
        (queryWitness diagram.Value default first second evidence
          firstConfiguration secondConfiguration evidenceConfiguration) evidence =
      evidenceConfiguration := by
  funext node
  exact queryWitness_of_evidence diagram.Value default first second evidence
    retained latentLeft latentRight partition firstConfiguration
      secondConfiguration evidenceConfiguration node.2

private theorem tripleCylinder_probOf_eq_queryCylinderMass
    [DecidableEq Node]
    (law : FinDist (Assignment diagram)) (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    law.probOf
        (tripleCylinder first second evidence firstConfiguration
          secondConfiguration evidenceConfiguration) =
      cylinderMass diagram.Value law (fixedCoordinates first second evidence)
        (queryWitness diagram.Value default first second evidence
          firstConfiguration secondConfiguration evidenceConfiguration) := by
  let witness := queryWitness diagram.Value default first second evidence
    firstConfiguration secondConfiguration evidenceConfiguration
  have hmass := tripleCylinder_probOf_eq_cylinderMass law first second evidence witness
  rw [queryWitness_restrict_first (diagram := diagram) default
      first second evidence,
    queryWitness_restrict_second (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition,
    queryWitness_restrict_evidence (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition] at hmass
  simpa [witness, fixedCoordinates] using hmass

private theorem firstEvidence_probOf_eq_queryCylinderMass
    [DecidableEq Node]
    (law : FinDist (Assignment diagram)) (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (firstConfiguration : Config diagram first)
    (evidenceConfiguration : Config diagram evidence) :
    law.probOf (pairCylinder first evidence firstConfiguration evidenceConfiguration) =
      cylinderMass diagram.Value law (firstEvidence first evidence)
        (queryWitness diagram.Value default first second evidence
          firstConfiguration (configurationOf diagram.Value default second)
            evidenceConfiguration) := by
  let witness := queryWitness diagram.Value default first second evidence
    firstConfiguration (configurationOf diagram.Value default second)
      evidenceConfiguration
  have hmass := pairCylinder_probOf_eq_cylinderMass law first evidence witness
  rw [queryWitness_restrict_first (diagram := diagram) default
      first second evidence,
    queryWitness_restrict_evidence (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition] at hmass
  simpa [witness, firstEvidence] using hmass

private theorem secondEvidence_probOf_eq_queryCylinderMass
    [DecidableEq Node]
    (law : FinDist (Assignment diagram)) (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (secondConfiguration : Config diagram second)
    (evidenceConfiguration : Config diagram evidence) :
    law.probOf (pairCylinder second evidence secondConfiguration evidenceConfiguration) =
      cylinderMass diagram.Value law (secondEvidence second evidence)
        (queryWitness diagram.Value default first second evidence
          (configurationOf diagram.Value default first) secondConfiguration
            evidenceConfiguration) := by
  let witness := queryWitness diagram.Value default first second evidence
    (configurationOf diagram.Value default first) secondConfiguration
      evidenceConfiguration
  have hmass := pairCylinder_probOf_eq_cylinderMass law second evidence witness
  rw [queryWitness_restrict_second (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition,
    queryWitness_restrict_evidence (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition] at hmass
  simpa [witness, secondEvidence] using hmass

private theorem evidence_probOf_eq_queryCylinderMass
    [DecidableEq Node]
    (law : FinDist (Assignment diagram)) (default : Assignment diagram)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (evidenceConfiguration : Config diagram evidence) :
    law.probOf (cylinder evidence evidenceConfiguration) =
      cylinderMass diagram.Value law evidence
        (queryWitness diagram.Value default first second evidence
          (configurationOf diagram.Value default first)
          (configurationOf diagram.Value default second)
          evidenceConfiguration) := by
  let witness := queryWitness diagram.Value default first second evidence
    (configurationOf diagram.Value default first)
    (configurationOf diagram.Value default second) evidenceConfiguration
  have hmass := cylinder_probOf_eq_cylinderMass law evidence witness
  rw [queryWitness_restrict_evidence (diagram := diagram) default first second evidence
      retained latentLeft latentRight partition] at hmass
  simpa [witness] using hmass

/-- Ancestral-moral separation implies division-free conditional independence
for every law factorizing over normalized local kernels. -/
theorem coordinatesConditionallyIndependent_of_factorizes_of_separates
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (law : FinDist (Assignment diagram))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels diagram.Value parents)
    (hfactor : Factorizes diagram.Value law parents kernels)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (hsecondEvidence : Disjoint second evidence)
    (hseparates : Separates parents first second evidence) :
    CoordinatesConditionallyIndependent law first second evidence := by
  rw [coordinatesConditionallyIndependent_iff_cylinders]
  intro firstConfiguration secondConfiguration evidenceConfiguration
  obtain ⟨default, _⟩ := law.support_nonempty
  let retained := ancestralFactors parents first second evidence
  let latentLeft := FiniteBNMoralScoreBridge.latentLeft
    parents first second evidence
  let latentRight := FiniteBNMoralScoreBridge.latentRight
    parents first second evidence
  let partition := scorePartition parents first second evidence
    hfirstSecond hfirstEvidence hsecondEvidence
  obtain ⟨leftScore, rightScore, hsplit, hleft, hright⟩ :=
    exists_moral_scores_of_separates diagram.Value parents kernels
      first second evidence hseparates
  have hcross := jointTable_crossMul diagram.Value default
    first second evidence retained latentLeft latentRight partition
    (factorProduct diagram.Value parents kernels retained)
    leftScore rightScore hsplit hleft hright
    evidenceConfiguration firstConfiguration secondConfiguration
  have hpoint : ∀ evidenceValue firstValue secondValue,
      jointTable diagram.Value default first second evidence retained
          latentLeft latentRight partition
          (factorProduct diagram.Value parents kernels retained)
          evidenceValue firstValue secondValue =
        cylinderMass diagram.Value law (fixedCoordinates first second evidence)
          (queryWitness diagram.Value default first second evidence
            firstValue secondValue evidenceValue) := by
    intro evidenceValue firstValue secondValue
    exact (cylinderMass_eq_jointTable_factorProduct diagram.Value law parents
      topological kernels hfactor default first second evidence retained
      latentLeft latentRight partition
      (ancestralFactors_parentClosed parents first second evidence)
      firstValue secondValue evidenceValue).symm
  simp_rw [hpoint] at hcross
  rw [sum_first_second_queryCylinders diagram.Value law default
      first second evidence hfirstSecond hfirstEvidence hsecondEvidence,
    sum_second_queryCylinders diagram.Value law default first second evidence
      hfirstSecond hsecondEvidence,
    sum_first_queryCylinders diagram.Value law default first second evidence
      hfirstSecond hfirstEvidence] at hcross
  rw [tripleCylinder_probOf_eq_queryCylinderMass (diagram := diagram) law default
      first second evidence retained latentLeft latentRight partition,
    evidence_probOf_eq_queryCylinderMass (diagram := diagram) law default
      first second evidence retained latentLeft latentRight partition,
    firstEvidence_probOf_eq_queryCylinderMass (diagram := diagram) law default
      first second evidence retained latentLeft latentRight partition,
    secondEvidence_probOf_eq_queryCylinderMass (diagram := diagram) law default
      first second evidence retained latentLeft latentRight partition]
  exact hcross

end GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
