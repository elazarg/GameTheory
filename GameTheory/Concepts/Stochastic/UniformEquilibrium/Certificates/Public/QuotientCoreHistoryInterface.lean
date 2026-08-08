/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.RecurrentClassChild
import Math.Probability.QuotientShadowLift

/-!
# Concrete public quotient/core history interfaces

This file gives a semantic input below the abstract
`LegalCoreHistoryEntryInterface` field of a public response recursion.

A public Markov policy is represented by actual mixed actions in the
stochastic game, so its state kernel is operationally legal by construction.
A core strategy is represented by a supplied adaptive core step together
with an application-specific legality predicate. Strong lumpability and a
`QuotientGluingInterface` then yield one exact causal joint history law.

The final adapter is conditional on an explicit authorization map from
concrete core-strategy legality to the recursion's opaque legal-entry
proposition. No theorem can manufacture such a map from the opaque
proposition alone.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability Math.PMFProduct

variable {ι : Type} {G : StochasticGame ι}

/-- A public Markov policy chooses an actual mixed action independently for
each player from the current public state. -/
abbrev PublicMarkovPolicy
    (G : StochasticGame ι) :=
  G.State → ∀ player, PMF (G.Act player)

/-- The behavior profile implemented by a public Markov policy. -/
def publicMarkovBehaviorProfile
    (policy : G.PublicMarkovPolicy) :
    G.BehaviorProfile :=
  fun player _ history => policy history.2 player

/-- The actual game-state kernel induced by a public Markov policy. -/
def publicMarkovStateKernel
    [Fintype ι]
    (policy : G.PublicMarkovPolicy) :
    G.State → PMF G.State :=
  fun state =>
    (pmfPi (policy state)).bind fun action =>
      G.transition state action

@[simp]
theorem stageActionDist_publicMarkovBehaviorProfile
    [Fintype ι]
    (policy : G.PublicMarkovPolicy)
    {time : ℕ} (history : G.Hist time) :
    G.stageActionDist
        (G.publicMarkovBehaviorProfile policy) history =
      pmfPi (policy history.2) :=
  rfl

/-- At every complete game history, the next-state law of the implemented
behavior profile is exactly its public Markov state kernel. -/
theorem publicMarkovBehaviorProfile_nextStateLaw
    [Fintype ι]
    (policy : G.PublicMarkovPolicy)
    {time : ℕ} (history : G.Hist time) :
    (G.stageActionDist
        (G.publicMarkovBehaviorProfile policy) history).bind
          (fun action => G.transition history.2 action) =
      G.publicMarkovStateKernel policy history.2 := by
  rw [stageActionDist_publicMarkovBehaviorProfile]
  rfl

/-- Concrete strategic data for a strongly lumpable public Markov policy
and a supplied legal core-history strategy.

`CoreStrategy` and `IsLegalCoreStrategy` are application-facing: the core
may be another stochastic game, a recurrent continuation system, or a
history automaton. The exact adaptive law it induces is `coreStepOf`.
The gluing field records the complete one-step quotient/core joint law. -/
structure StronglyLumpableLegalCoreHistoryDatum
    [Fintype ι]
    (G : StochasticGame ι)
    (initial : G.State)
    (Quotient Core CoreStrategy : Type*)
    [Finite Quotient] [Finite Core]
    (quotient : G.State → Quotient)
    (quotientKernel : Quotient → PMF Quotient)
    (coreStepOf :
      CoreStrategy → ∀ n, (Fin n → Core) → PMF Core)
    (IsLegalCoreStrategy : CoreStrategy → Prop) where
  publicPolicy : G.PublicMarkovPolicy
  lumpable :
    IsStronglyLumpable
      (G.publicMarkovStateKernel publicPolicy)
      quotient quotientKernel
  coreStrategy : CoreStrategy
  coreStrategy_legal : IsLegalCoreStrategy coreStrategy
  gluing :
    QuotientGluingInterface
      (adaptiveMarkovStep (quotient initial)
        (markovKernelComparison quotientKernel))
      (coreStepOf coreStrategy)

namespace StronglyLumpableLegalCoreHistoryDatum

variable
    [Fintype ι]
    {Quotient Core CoreStrategy : Type*}
    [Finite G.State] [Finite Quotient] [Finite Core]
    {initial : G.State}
    {quotient : G.State → Quotient}
    {quotientKernel : Quotient → PMF Quotient}
    {coreStepOf :
      CoreStrategy → ∀ n, (Fin n → Core) → PMF Core}
    {IsLegalCoreStrategy : CoreStrategy → Prop}

/-- The causal full-state/core step produced by the concrete datum. -/
def liftStep
    (D : StronglyLumpableLegalCoreHistoryDatum
      G initial Quotient Core CoreStrategy
      quotient quotientKernel coreStepOf
      IsLegalCoreStrategy) :
    ∀ n, (Fin n → G.State × Core) →
      PMF (G.State × Core) :=
  D.gluing.liftStep quotient
    (adaptiveMarkovStep initial
      (markovKernelComparison
        (G.publicMarkovStateKernel D.publicPolicy)))

/-- Strong lumpability plus the supplied legal core gluing gives exact
full-state, core-state, and quotient/core history laws simultaneously. -/
theorem adaptiveHistoryLaw_liftStep_exact
    (D : StronglyLumpableLegalCoreHistoryDatum
      G initial Quotient Core CoreStrategy
      quotient quotientKernel coreStepOf
      IsLegalCoreStrategy)
    (T : ℕ) :
    let controlled :=
      adaptiveMarkovStep initial
        (markovKernelComparison
          (G.publicMarkovStateKernel D.publicPolicy))
    (adaptiveHistoryLaw D.liftStep T).map
          (mapFiniteHistory Prod.fst) =
        adaptiveHistoryLaw controlled T ∧
      (adaptiveHistoryLaw D.liftStep T).map
          (mapFiniteHistory Prod.snd) =
        adaptiveHistoryLaw (coreStepOf D.coreStrategy) T ∧
      (adaptiveHistoryLaw D.liftStep T).map
          (mapFiniteHistory (quotientPairMap quotient)) =
        adaptiveHistoryLaw D.gluing.jointStep T := by
  exact
    D.gluing.adaptiveHistoryLaw_strongLumpableMarkov_liftStep_exact
      initial (G.publicMarkovStateKernel D.publicPolicy)
      quotient quotientKernel D.lumpable
      (coreStepOf D.coreStrategy) T

end StronglyLumpableLegalCoreHistoryDatum

/-- Conditional adapter from concrete quotient/core strategy data to a
recurrent child.

The public kernel comes from actual mixed actions. `core` supplies reachable
closed entry under that kernel; whole-target preservation and rank decrease
remain explicit. `authorize` is the irreducible application theorem saying
that legality of the supplied core strategy satisfies the recursion-specific
opaque entry proposition. -/
def PublicRecurrentClassChild.of_legalQuotientCoreHistory
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
    (core :
      ReachableClosedClass
        (G.publicMarkovStateKernel D.publicPolicy)
        initial)
    (parent_entry : nodeEntry parent = initial)
    (child : Node)
    (child_entry : nodeEntry child = core.entry)
    (target_preserved : nodeTarget child = nodeTarget parent)
    (rank_decreases :
      rankLt (nodeRank child) (nodeRank parent))
    (authorize :
      IsLegalCoreStrategy D.coreStrategy →
        LegalEntryInterface parent) :
    PublicRecurrentClassChild
      (G.publicMarkovStateKernel D.publicPolicy)
      nodeEntry nodeTarget nodeRank rankLt
      LegalEntryInterface parent := by
  subst initial
  exact {
    core := core
    child := child
    child_entry := child_entry
    target_preserved := target_preserved
    rank_decreases := rank_decreases
    legal_entry_interface := authorize D.coreStrategy_legal
  }

end StochasticGame
end GameTheory
