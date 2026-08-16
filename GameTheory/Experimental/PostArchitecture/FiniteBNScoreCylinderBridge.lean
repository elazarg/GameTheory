/-
# EXP-104: retained factor scores as cylinder masses

This module identifies the dependent score table used by rank-one assembly
with the actual cylinder mass of a factorizing finite law.  Parent-closed
marginalization has already removed every nonretained factor, so the table sums
only the two genuine latent coordinate blocks.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNScoreCylinderBridge

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
open GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- The retained local-factor table is exactly the mass of the query cylinder
at arbitrary typed query configurations. -/
theorem cylinderMass_eq_jointTable_factorProduct
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels)
    (default : Assignment Value)
    (first second evidence retained latentLeft latentRight : Finset Node)
    (partition :
      ScorePartition first second evidence retained latentLeft latentRight)
    (hclosed : ParentClosed parents retained)
    (firstConfiguration : Configuration Value first)
    (secondConfiguration : Configuration Value second)
    (evidenceConfiguration : Configuration Value evidence) :
    cylinderMass Value law (fixedCoordinates first second evidence)
        (queryWitness Value default first second evidence firstConfiguration
          secondConfiguration evidenceConfiguration) =
      jointTable Value default first second evidence retained latentLeft
        latentRight partition
          (factorProduct Value parents kernels retained)
          evidenceConfiguration firstConfiguration secondConfiguration := by
  unfold jointTable completedAssignment
  exact cylinderMass_eq_sum_latentFactorProducts_of_parentClosed Value law
    parents topological kernels hfactor
    (fixedCoordinates first second evidence) retained latentLeft latentRight
    partition.fixed_subset hclosed partition.latent
    (queryWitness Value default first second evidence firstConfiguration
      secondConfiguration evidenceConfiguration)

end GameTheory.Experimental.PostArchitecture.FiniteBNScoreCylinderBridge
