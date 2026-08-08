/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.ConstraintPublicResponse
import Math.FiniteInequalityCompatibility

/-!
# Rectangular mixed-player continuation compatibility

Bellman inequalities owned by player `i` depend only on player `i`'s
continuation coordinate. Separate playerwise feasibility therefore implies
simultaneous feasibility when the permitted continuation set is a product
of player-coordinate sets.

This file formalizes that sufficient condition and builds it directly into a
public-response branching recursion. The recursion's compatibility branch is
no longer an opaque proposition: it contains one whole-vector continuation
satisfying every coordinate permission and every player-owned linear
inequality.

The condition is genuinely restrictive. Coupled continuation sets such as
the diagonal segment in `FinkContinuationCompatibilityCounterexample` are
not rectangular and are intentionally outside the theorem.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.LinearAlgebra

variable {State Player : Type*}
  [Fintype State] [Fintype Player]
  {Constraint : Player → Type*}
  [∀ player, Fintype (Constraint player)]

/-- Player-block continuation geometry and player-owned Bellman
inequalities.

`coordinatePermitted player` is the player's factor of the permitted
continuation product. `delta` is normally a transition-difference row and
`rhs` its Bellman lower bound. -/
structure RectangularContinuationSystem
    (State Player : Type*)
    (Constraint : Player → Type*) where
  coordinatePermitted : ∀ _player : Player, (State → ℝ) → Prop
  delta : ∀ player, Constraint player → State → ℝ
  rhs : ∀ player, Constraint player → ℝ

namespace RectangularContinuationSystem

/-- Every player can choose a feasible continuation in their own coordinate
factor. -/
def PlayerwiseFeasible
    (S : RectangularContinuationSystem
      State Player Constraint) : Prop :=
  ∀ player,
    ∃ coordinate : State → ℝ,
      S.coordinatePermitted player coordinate ∧
        ∀ constraint,
          S.rhs player constraint ≤
            dotProduct (S.delta player constraint) coordinate

/-- One whole payoff-vector continuation is feasible for every player at
once. -/
def SimultaneouslyFeasible
    (S : RectangularContinuationSystem
      State Player Constraint) : Prop :=
  ∃ continuation : State → Player → ℝ,
    (∀ player,
      S.coordinatePermitted player
        (fun state => continuation state player)) ∧
    ∀ player constraint,
      S.rhs player constraint ≤
        dotProduct (S.delta player constraint)
          (fun state => continuation state player)

omit [Fintype Player] [∀ player, Fintype (Constraint player)] in
/-- Rectangularity turns separate coordinate witnesses into one simultaneous
whole-vector continuation without loss or an additional compatibility
assumption. -/
theorem simultaneouslyFeasible_of_playerwise
    (S : RectangularContinuationSystem
      State Player Constraint)
    (playerwise : S.PlayerwiseFeasible) :
    S.SimultaneouslyFeasible := by
  choose coordinate coordinatePermitted inequalities using playerwise
  refine ⟨fun state player => coordinate player state, ?_, ?_⟩
  · intro player
    exact coordinatePermitted player
  · intro player constraint
    exact inequalities player constraint

omit [Fintype Player] [∀ player, Fintype (Constraint player)] in
/-- The simultaneous witness exposes a feasible finite inequality potential
in each player block. -/
theorem finiteInequalityFeasible_of_simultaneouslyFeasible
    (S : RectangularContinuationSystem
      State Player Constraint)
    (simultaneous : S.SimultaneouslyFeasible)
    (player : Player) :
    ∃ coordinate : State → ℝ,
      ∀ constraint,
        S.rhs player constraint ≤
          dotProduct (S.delta player constraint) coordinate := by
  obtain ⟨continuation, -, inequalities⟩ := simultaneous
  exact ⟨fun state => continuation state player,
    inequalities player⟩

end RectangularContinuationSystem

variable {ι : Type} {G : StochasticGame ι}

/-- A public-response branching recursion whose compatible branch is
certified by rectangular player-block continuation geometry.

The response closer and legal core-history interface remain strategic data.
Only the mixed-player continuation-gluing obligation is discharged here. -/
structure RectangularContinuationBranchingRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Fintype G.State] [∀ player, Finite (G.Act player)]
    (Constraint : ι → Type*)
    [∀ player, Fintype (Constraint player)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    extends G.LocalResponseNodes s₀ v where
  continuationSystem :
    Node →
      RectangularContinuationSystem
        G.State ι Constraint
  PublicResponse : Node → Prop
  LegalCoreHistoryEntryInterface : Node → Prop
  playerwiseCompatibilityOrPublicResponse :
    ∀ node,
      (continuationSystem node).PlayerwiseFeasible ∨
        PublicResponse node
  legalCoreHistoryEntryInterface :
    ∀ node, LegalCoreHistoryEntryInterface node
  closeCompatible :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      (continuationSystem node).SimultaneouslyFeasible →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ
  closeResponse :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      PublicResponse node →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ

namespace RectangularContinuationBranchingRecursionAt

variable
    [Fintype ι] [DecidableEq ι]
    [Fintype G.State] [∀ player, Finite (G.Act player)]
    {Constraint : ι → Type*}
    [∀ player, Fintype (Constraint player)]
    {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Compile rectangular playerwise feasibility into the simultaneous
compatibility branch of the existing public-response recursion. -/
def toPublicResponseBranchingRecursionAt
    (C : G.RectangularContinuationBranchingRecursionAt
      Constraint s₀ v δ) :
    G.PublicResponseBranchingRecursionAt s₀ v δ where
  toLocalResponseNodes := C.toLocalResponseNodes
  CompatibleContinuation := fun node =>
    (C.continuationSystem node).SimultaneouslyFeasible
  PublicResponse := C.PublicResponse
  LegalCoreHistoryEntryInterface :=
    C.LegalCoreHistoryEntryInterface
  compatibilityOrPublicResponse := fun node =>
    (C.playerwiseCompatibilityOrPublicResponse node).imp
      (fun playerwise =>
        RectangularContinuationSystem.simultaneouslyFeasible_of_playerwise
          (C.continuationSystem node) playerwise)
      id
  legalCoreHistoryEntryInterface :=
    C.legalCoreHistoryEntryInterface
  closeCompatible := C.closeCompatible
  closeResponse := C.closeResponse

/-- Rectangular continuation compatibility compiles through the existing
well-founded public local-response verifier. -/
theorem toIsPublicPhasePunishmentSystemAt
    (C : G.RectangularContinuationBranchingRecursionAt
      Constraint s₀ v δ) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  PublicResponseBranchingRecursionAt.toIsPublicPhasePunishmentSystemAt
    C.toPublicResponseBranchingRecursionAt

end RectangularContinuationBranchingRecursionAt

end StochasticGame
end GameTheory
