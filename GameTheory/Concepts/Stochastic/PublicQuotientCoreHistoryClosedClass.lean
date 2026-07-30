/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicQuotientCoreHistoryInterface
import Math.Probability.FiniteReachableClosedClass

/-!
# Automatic recurrent-class selection for legal quotient/core histories

A finite public Markov kernel always has a closed communicating class
reachable from the parent entry. This removes the ambient
`ReachableClosedClass` argument from the quotient/core recurrent-child
adapter.

The selected class is noncanonical. Consequently the caller supplies child
entry, whole-target preservation, and strict rank descent uniformly for any
class the finite support-graph theorem may select. Core-strategy
authorization remains explicit.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Select a reachable closed class automatically and return the recurrent
child constructor specialized to that class. The caller sees the selected
class before supplying child entry, target preservation, and rank descent. -/
theorem PublicRecurrentClassChild.exists_builder_of_legalQuotientCoreHistory
    [Fintype ι] [Fintype G.State] [DecidableEq G.State]
    {Quotient Core CoreStrategy Rank Node : Type*}
    [Finite Quotient] [Finite Core]
    {initial : G.State}
    {quotient : G.State → Quotient}
    {quotientKernel : Quotient → PMF Quotient}
    {coreStepOf :
      CoreStrategy → ∀ n, (Fin n → Core) → PMF Core}
    {IsLegalCoreStrategy : CoreStrategy → Prop}
    (D : StronglyLumpableLegalCoreHistoryDatum
      G initial Quotient Core CoreStrategy
      quotient quotientKernel coreStepOf
      IsLegalCoreStrategy)
    (nodeEntry : Node → G.State)
    (nodeTarget : Node → Payoff ι)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (parent_entry : nodeEntry parent = initial)
    (authorize :
      IsLegalCoreStrategy D.coreStrategy →
        LegalEntryInterface parent) :
    ∃ core :
        ReachableClosedClass
          (G.publicMarkovStateKernel D.publicPolicy)
          initial,
      ∀ child : Node,
        nodeEntry child = core.entry →
          nodeTarget child = nodeTarget parent →
            rankLt (nodeRank child) (nodeRank parent) →
              Nonempty
                (PublicRecurrentClassChild
                  (G.publicMarkovStateKernel D.publicPolicy)
                  nodeEntry nodeTarget nodeRank rankLt
                  LegalEntryInterface parent) := by
  obtain ⟨core⟩ :=
    exists_reachableClosedClass
      (G.publicMarkovStateKernel D.publicPolicy)
      initial
  refine ⟨core, ?_⟩
  intro child child_entry target_preserved rank_decreases
  exact ⟨PublicRecurrentClassChild.of_legalQuotientCoreHistory
    D nodeEntry nodeTarget nodeRank rankLt
    LegalEntryInterface parent core parent_entry
    child child_entry target_preserved rank_decreases
    authorize⟩

/-- Build recurrent-child data from a legal quotient/core history datum
without asking the caller to construct a reachable closed class.

Only existence of the class is automatic. The child-selection hypothesis
contains exactly the remaining target and rank obligations for the class
chosen by the finite support-graph argument. -/
theorem PublicRecurrentClassChild.exists_of_legalQuotientCoreHistory
    [Fintype ι] [Fintype G.State] [DecidableEq G.State]
    {Quotient Core CoreStrategy Rank Node : Type*}
    [Finite Quotient] [Finite Core]
    {initial : G.State}
    {quotient : G.State → Quotient}
    {quotientKernel : Quotient → PMF Quotient}
    {coreStepOf :
      CoreStrategy → ∀ n, (Fin n → Core) → PMF Core}
    {IsLegalCoreStrategy : CoreStrategy → Prop}
    (D : StronglyLumpableLegalCoreHistoryDatum
      G initial Quotient Core CoreStrategy
      quotient quotientKernel coreStepOf
      IsLegalCoreStrategy)
    (nodeEntry : Node → G.State)
    (nodeTarget : Node → Payoff ι)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node)
    (parent_entry : nodeEntry parent = initial)
    (childForClass :
      ∀ core :
          ReachableClosedClass
            (G.publicMarkovStateKernel D.publicPolicy)
            initial,
        ∃ child : Node,
          nodeEntry child = core.entry ∧
            nodeTarget child = nodeTarget parent ∧
              rankLt (nodeRank child) (nodeRank parent))
    (authorize :
      IsLegalCoreStrategy D.coreStrategy →
        LegalEntryInterface parent) :
    Nonempty
      (PublicRecurrentClassChild
        (G.publicMarkovStateKernel D.publicPolicy)
        nodeEntry nodeTarget nodeRank rankLt
        LegalEntryInterface parent) := by
  obtain ⟨core, buildChild⟩ :=
    PublicRecurrentClassChild.exists_builder_of_legalQuotientCoreHistory
      D nodeEntry nodeTarget nodeRank rankLt
      LegalEntryInterface parent parent_entry authorize
  obtain ⟨child, child_entry, target_preserved,
      rank_decreases⟩ :=
    childForClass core
  exact buildChild child child_entry
    target_preserved rank_decreases

end StochasticGame
end GameTheory
