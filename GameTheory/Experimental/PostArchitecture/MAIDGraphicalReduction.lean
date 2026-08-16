/-
# EXP-105: graphical discharge of one-site MAID reduction

This file assembles the existing relevant and nonrelevant utility-term laws
into the existing graph-free local factorization and deviation-coverage
certificates.  It adds no evaluator, probability notion, or certificate
layer.
-/

import GameTheory.Experimental.PostArchitecture.MAIDNonrelevantUtilityInvariance
import GameTheory.Experimental.PostArchitecture.MAIDRelevantUtilityContinuation

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDGraphicalReduction

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.MAIDLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDNonrelevantUtilityInvariance
open GameTheory.Experimental.PostArchitecture.MAIDRelevantUtilityContinuation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

/-- Graphical ignorability supplies the existing replacement-invariant
utility-law certificate: relevant terms use the canonical conditional
continuation, while nonrelevant terms use kernel-invariant marginals. -/
def replacementInvariantUtilityLawAt_of_graphicallyIgnorable
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (shape : IsSingleSitePruningAt pruning owner target)
    (view : UtilityView semantics)
    (hignore : view.AreGraphicallyIgnorable target
      (diagram.observedParents target.1 \ pruning.kept target.1)) :
    ReplacementInvariantUtilityLawAt pruning semantics policy owner target
      view where
  context := replacementContextLawAt_of_unique_site pruning semantics policy
    owner target shape.target_unique
  relevant term hrelevant :=
    relevantTermContinuationLawAt_of_unique_site pruning semantics policy
      owner target shape.target_unique topological view
      (by simpa [removedObservations] using hignore) term hrelevant
  nonrelevant term hnonrelevant :=
    nonrelevantTermMarginalCertificate pruning topological semantics policy
      owner target shape.target_unique view term hnonrelevant

/-- The assembled term laws discharge the existing graph-free local utility
factorization at the unique target site. -/
theorem localUtilityFactorsAt_of_graphicallyIgnorable
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (shape : IsSingleSitePruningAt pruning owner target)
    (view : UtilityView semantics)
    (hignore : view.AreGraphicallyIgnorable target
      (diagram.observedParents target.1 \ pruning.kept target.1)) :
    LocalUtilityFactorsAt pruning semantics policy owner target :=
  localUtilityFactorsAt_of_replacementInvariantUtilityLawAt pruning semantics
    policy owner target view
      (replacementInvariantUtilityLawAt_of_graphicallyIgnorable pruning
        topological semantics policy owner target shape view hignore)

/-- Under the full one-site pruning shape, graphical ignorability discharges
the canonical full-deviation coverage certificate. -/
theorem coversFullDeviationsAt_of_graphicallyIgnorable
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (shape : IsSingleSitePruningAt pruning owner target)
    (view : UtilityView semantics)
    (hignore : view.AreGraphicallyIgnorable target
      (diagram.observedParents target.1 \ pruning.kept target.1)) :
    pruning.CoversFullDeviationsAt semantics policy :=
  coversFullDeviationsAt_of_localUtilityFactorsAt pruning semantics policy
    owner target shape
      (localUtilityFactorsAt_of_graphicallyIgnorable pruning topological
        semantics policy owner target shape view hignore)

end GameTheory.Experimental.PostArchitecture.MAIDGraphicalReduction
