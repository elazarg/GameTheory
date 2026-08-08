/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.LocalResponseRecursion
import Math.Probability.ChargedOccupationAlternative
import Math.Probability.ReachableClosedClass

/-!
# Reachable recurrent children for public local-response recursion

A positive operational occupation circulation realizes a stationary
response on its active support.  Three further facts are required before
that response can be used as a recursive child:

1. a closed communicating class must be reachable from the parent's actual
   entry under a legal public kernel;
2. the child must carry the complete payoff-vector target, not merely the
   charged owner's coordinate;
3. the child must have strictly smaller recursion rank.

`PublicRecurrentClassChild` is the minimal constructor output containing
these obligations.  Its certificate theorem shows that its target and rank
fields are exactly what is needed to invoke the recursive hypothesis.

The counterexamples at the end show that a positive player-owned
circulation supplies none of target transport or rank descent by itself.
Reachability already fails in the two-state example in
`Math.Probability.ReachableClosedClass`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

/-- A recurrent child selected from a parent node.

`legalKernel` is the actual public kernel used to enter and remain in the
selected class.  `LegalEntryInterface parent` records any additional
history, coupling, or implementation evidence required by the application.
Target preservation is equality of the entire player-indexed vector. -/
structure PublicRecurrentClassChild
    {State Player Rank Node : Type*}
    [Fintype State] [DecidableEq State]
    (legalKernel : State → PMF State)
    (entry : Node → State)
    (target : Node → Player → ℝ)
    (rank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent : Node) where
  core : ReachableClosedClass legalKernel (entry parent)
  child : Node
  child_entry : entry child = core.entry
  target_preserved : target child = target parent
  rank_decreases : rankLt (rank child) (rank parent)
  legal_entry_interface : LegalEntryInterface parent

/-- The weakest constructor shape needed from the recurrent-flow branch.
The concrete flow type may depend on the parent node. -/
abbrev PublicRecurrentClassChildConstructor
    {State Player Rank Node : Type*}
    [Fintype State] [DecidableEq State]
    (Flow : Node → Type*)
    (legalKernel : State → PMF State)
    (entry : Node → State)
    (target : Node → Player → ℝ)
    (rank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop) :=
  ∀ parent, Flow parent →
    PublicRecurrentClassChild
      legalKernel entry target rank rankLt
      LegalEntryInterface parent

namespace PublicRecurrentClassChild

variable
    {State Player Rank Node : Type*}
    [Fintype State] [DecidableEq State]
    {legalKernel : State → PMF State}
    {entry : Node → State}
    {target : Node → Player → ℝ}
    {rank : Node → Rank}
    {rankLt : Rank → Rank → Prop}
    {LegalEntryInterface : Node → Prop}
    {parent : Node}

/-- Target preservation and strict rank descent transport a recursive
certificate to the child entry with the parent's full vector target. -/
theorem invokeRecursiveCertificate
    (C : PublicRecurrentClassChild
      legalKernel entry target rank rankLt
      LegalEntryInterface parent)
    (Certificate : State → (Player → ℝ) → Prop)
    (recurse :
      ∀ child, rankLt (rank child) (rank parent) →
        Certificate (entry child) (target child)) :
    Certificate (entry C.child) (target parent) := by
  simpa only [C.target_preserved] using
    recurse C.child C.rank_decreases

end PublicRecurrentClassChild

/-- Public-phase specialization of `invokeRecursiveCertificate`.  A
recurrent-child constructor provides exactly a legal lower-ranked recursive
call carrying the complete parent target. -/
theorem PublicLocalResponseRecursionAt.recurrentChildCertificate
    {ι : Type} {G : StochasticGame ι}
    [Fintype ι] [DecidableEq ι]
    [Fintype G.State] [DecidableEq G.State]
    [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {v : Payoff ι} {δ : ℝ}
    (C : G.PublicLocalResponseRecursionAt s₀ v δ)
    (legalKernel : G.State → PMF G.State)
    (parent : C.Node)
    (childData :
      PublicRecurrentClassChild
        legalKernel C.entry C.target C.rank C.rankLt
        C.LegalCoreHistoryEntryInterface parent)
    (recurse :
      ∀ child : C.Node,
        C.rankLt (C.rank child) (C.rank parent) →
          G.IsPublicPhasePunishmentSystemAt
            (C.entry child) (C.target child) δ) :
    G.IsPublicPhasePunishmentSystemAt
      (C.entry childData.child) (C.target parent) δ := by
  exact childData.invokeRecursiveCertificate
    (fun state target =>
      G.IsPublicPhasePunishmentSystemAt state target δ)
    recurse

namespace PositiveOwnerFlowDoesNotTransportTarget

abbrev Player := Bool
abbrev State := Unit
abbrev Index := Unit

def kernel (_ : Index) : PMF State :=
  PMF.pure ()

def source (_ : Index) : State :=
  ()

def charge (_ : Index) : ℝ :=
  1

/-- The one-state self-loop is a normalized positive charged circulation. -/
theorem hasPositiveOwnerFlow :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn kernel source) charge := by
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_, ?_⟩
  · intro destination
    cases destination
    simp [actualOccupationColumn, kernel, source]
  · norm_num [charge]

/-- The selected owner's recurrent payoff coordinate is correct, while the
other player's coordinate is not. -/
def recurrentPayoff (_ : State) (who : Player) : ℝ :=
  if who then 0 else 1

def target (_ : Player) : ℝ :=
  1

theorem owner_coordinate_preserved :
    recurrentPayoff () false = target false := by
  simp [recurrentPayoff, target]

/-- Positive owner charge does not transport the complete payoff vector. -/
theorem full_target_not_preserved :
    recurrentPayoff () ≠ target := by
  intro heq
  have htrue := congrFun heq true
  norm_num [recurrentPayoff, target] at htrue

end PositiveOwnerFlowDoesNotTransportTarget

namespace PositiveOwnerFlowDoesNotDecreaseRank

abbrev Rank := Unit

def rankLt (_ _ : Rank) : Prop :=
  False

theorem no_strict_child :
    ¬∃ child : Rank, rankLt child () := by
  simp [rankLt]

/-- The same positive owner flow may coexist with a rank having no smaller
element.  Rank descent must therefore be supplied by the constructor. -/
theorem positiveFlow_and_no_rank_descent :
    HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          PositiveOwnerFlowDoesNotTransportTarget.kernel
          PositiveOwnerFlowDoesNotTransportTarget.source)
        PositiveOwnerFlowDoesNotTransportTarget.charge ∧
      ¬∃ child : Rank, rankLt child () :=
  ⟨PositiveOwnerFlowDoesNotTransportTarget.hasPositiveOwnerFlow,
    no_strict_child⟩

end PositiveOwnerFlowDoesNotDecreaseRank

end StochasticGame
end GameTheory
