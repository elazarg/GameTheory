/-
# EXP-104: canonical MAID global-Markov corollary

This module applies finite global-Markov soundness to the canonical native MAID
law.  It reuses the existing evaluator, its proved effective-parent
factorization, and the causal topological order with decision-only edges
removed.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
import GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDGlobalMarkovSoundness

open GameTheory
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- The canonical native MAID law satisfies every coordinate conditional
independence certified by ancestral-moral separation of effective parents. -/
theorem native_coordinatesConditionallyIndependent_of_moralSeparation
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (hsecondEvidence : Disjoint second evidence)
    (hseparates :
      Separates (effectiveParents diagram) first second evidence) :
    CoordinatesConditionallyIndependent
      ((nativeBehavioralGameForm semantics).play policy)
      first second evidence := by
  exact coordinatesConditionallyIndependent_of_factorizes_of_separates
    ((nativeBehavioralGameForm semantics).play policy)
    (effectiveParents diagram) (effectiveTopologicalOrder topological)
    (effectiveKernels semantics policy)
    (native_play_factorizes topological semantics policy)
    first second evidence hfirstSecond hfirstEvidence hsecondEvidence hseparates

end GameTheory.Experimental.PostArchitecture.MAIDGlobalMarkovSoundness
