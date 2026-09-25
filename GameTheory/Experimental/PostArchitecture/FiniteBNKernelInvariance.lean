/-
# EXP-105: parent-closed kernel invariance

This file proves that changing local kernels outside a parent-closed retained
set cannot change the law of the retained coordinates.  It compares two
already-factorizing finite laws and does not construct another evaluator.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
import GameTheory.Languages.MAID.Basic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- Extend a retained configuration to a total assignment with an arbitrary
fallback outside the retained set.  This is the empty-fixed-set specialization
of the canonical retained-cylinder filler. -/
def fillConfiguration [DecidableEq Node] (nodes : Finset Node)
    (fallback : Assignment diagram) (configuration : Config diagram nodes) :
    Assignment diagram :=
  fillRetained diagram.Value ∅ nodes fallback fun node =>
    configuration ⟨node.1, (Finset.mem_sdiff.mp node.2).1⟩

@[simp]
theorem fillConfiguration_of_mem [DecidableEq Node] (nodes : Finset Node)
    (fallback : Assignment diagram) (configuration : Config diagram nodes)
    {node : Node} (hnode : node ∈ nodes) :
    fillConfiguration nodes fallback configuration node =
      configuration ⟨node, hnode⟩ := by
  unfold fillConfiguration
  rw [fillRetained_of_mem]
  exact Finset.mem_sdiff.mpr ⟨hnode, by simp⟩

/-- A point mass of the restriction pushforward is the corresponding cylinder
mass.  The fallback assignment supplies values only outside `nodes`; every
finite law supplies such an assignment through its nonempty support. -/
theorem restrictLaw_mass_eq_cylinderMass
    [DecidableEq Node]
    (law : PMF (Assignment diagram)) (nodes : Finset Node)
    (fallback : Assignment diagram) (configuration : Config diagram nodes) :
    ((law.map
        (fun assignment => Assignment.restrict diagram assignment nodes)).toOuterMeasure
        {configuration}).toReal =
      cylinderMass diagram.Value law nodes
        (fillConfiguration nodes fallback configuration) := by
  classical
  rw [PMF.toOuterMeasure_map_apply]
  unfold cylinderMass
  have hset :
      (fun assignment : Assignment diagram =>
        Assignment.restrict diagram assignment nodes) ⁻¹' {configuration} =
        {assignment | AgreeOn diagram.Value nodes assignment
          (fillConfiguration nodes fallback configuration)} := by
    ext assignment
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro heq node hnode
      rw [fillConfiguration_of_mem nodes fallback configuration hnode]
      exact congrFun heq ⟨node, hnode⟩
    · intro hagrees
      funext node
      have h := hagrees node.1 node.2
      simpa only [Assignment.restrict,
        fillConfiguration_of_mem nodes fallback configuration node.2] using h
  rw [hset]

/-- Two factorizing laws have the same retained-coordinate marginal whenever
the retained set is parent-closed and their kernels agree there.  No
positivity, faithfulness, or inhabited-domain hypothesis is required. -/
theorem restrictLaw_eq_of_factorizes_of_kernels_eqOn
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (firstLaw secondLaw : PMF (Assignment diagram))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (firstKernels secondKernels : LocalKernels diagram.Value parents)
    (hfirst : Factorizes diagram.Value firstLaw parents firstKernels)
    (hsecond : Factorizes diagram.Value secondLaw parents secondKernels)
    (retained : Finset Node) (hclosed : ParentClosed parents retained)
    (hkernels : ∀ node ∈ retained,
      firstKernels node = secondKernels node) :
    PMF.map
        (fun assignment => Assignment.restrict diagram assignment retained)
        firstLaw =
      PMF.map
        (fun assignment => Assignment.restrict diagram assignment retained)
        secondLaw := by
  apply PMF.ext
  intro configuration
  let fallback := firstLaw.support_nonempty.choose
  let witness :=
    fillConfiguration retained fallback configuration
  have hproducts :
      factorProduct diagram.Value parents firstKernels retained witness =
        factorProduct diagram.Value parents secondKernels retained witness := by
    unfold factorProduct localFactor
    apply Finset.prod_congr rfl
    intro node hnode
    rw [hkernels node hnode]
  have hfirstMass :
      (PMF.map
        (fun assignment => Assignment.restrict diagram assignment retained)
        firstLaw configuration).toReal =
      cylinderMass diagram.Value firstLaw retained witness := by
    simpa only [PMF.toOuterMeasure_apply_singleton] using
      restrictLaw_mass_eq_cylinderMass firstLaw retained fallback configuration
  have hsecondMass :
      (PMF.map
        (fun assignment => Assignment.restrict diagram assignment retained)
        secondLaw configuration).toReal =
      cylinderMass diagram.Value secondLaw retained witness := by
    simpa only [PMF.toOuterMeasure_apply_singleton] using
      restrictLaw_mass_eq_cylinderMass secondLaw retained fallback configuration
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.map
      (fun assignment => Assignment.restrict diagram assignment retained)
      firstLaw |>.apply_ne_top configuration)
    (PMF.map
      (fun assignment => Assignment.restrict diagram assignment retained)
      secondLaw |>.apply_ne_top configuration)).mp
  calc
    (PMF.map
      (fun assignment => Assignment.restrict diagram assignment retained)
      firstLaw configuration).toReal =
        cylinderMass diagram.Value firstLaw retained witness := hfirstMass
    _ = factorProduct diagram.Value parents firstKernels retained witness :=
      cylinderMass_eq_factorProduct_of_parentClosed diagram.Value firstLaw
        parents topological firstKernels hfirst retained witness hclosed
    _ = factorProduct diagram.Value parents secondKernels retained witness :=
      hproducts
    _ = cylinderMass diagram.Value secondLaw retained witness :=
      (cylinderMass_eq_factorProduct_of_parentClosed diagram.Value secondLaw
        parents topological secondKernels hsecond retained witness hclosed).symm
    _ = (PMF.map
      (fun assignment => Assignment.restrict diagram assignment retained)
      secondLaw configuration).toReal := hsecondMass.symm

end GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance
