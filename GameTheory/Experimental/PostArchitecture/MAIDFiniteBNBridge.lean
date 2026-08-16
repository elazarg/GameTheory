/-
# EXP-104: canonical MAID finite-BN bridge

This module packages the canonical MAID point-mass factorization in the form
consumed by finite-BN marginalization.  Effective decision parents only remove
causal edges, so an existing causal topological order remains valid verbatim.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
import GameTheory.Experimental.PostArchitecture.MAIDFactorization

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge

open GameTheory
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- Every effective parent is a causal parent. -/
theorem effectiveParents_subset (node : Node) :
    effectiveParents diagram node ⊆ diagram.parents node := by
  intro parent hparent
  unfold effectiveParents at hparent
  split at hparent
  · exact hparent
  · exact diagram.observed_sub node hparent

/-- Removing unobserved incoming edges at decisions preserves the same
topological order, including its stored list and enumeration certificates. -/
def effectiveTopologicalOrder
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    GameTheory.Math.DAG.TopologicalOrder (effectiveParents diagram) where
  order := topological.order
  nodup := topological.nodup
  complete := topological.complete
  respects index parent hparent :=
    topological.respects index parent
      (effectiveParents_subset (diagram := diagram) topological.order[index]
        hparent)

/-- Canonical native MAID play factorizes over the effective chance and
decision-parent kernels in the exact interface used by finite-BN
marginalization. -/
theorem native_play_factorizes
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram)) :
    Factorizes diagram.Value
      ((nativeBehavioralGameForm semantics).play policy)
      (effectiveParents diagram) (effectiveKernels semantics policy) := by
  intro assignment
  exact native_play_prob_eq_factorProduct_univ
    topological semantics policy assignment

end GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge
