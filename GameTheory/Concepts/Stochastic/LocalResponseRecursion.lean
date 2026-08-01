/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MultiRound.StochasticGame

/-!
# Goal-generic well-founded local-response recursion

Several packaging layers in this directory repeat one and the same
construction: state-indexed nodes ranked by a well-founded relation, a root
pinned to the ambient entry state and target payoff, two explicit strategic
witnesses, and a local closer that may consult only strictly lower-ranked
children.  Only the *conclusion* of the closer changes between them: a
public-phase punishment system, an expectation-level adaptive potential
certificate, and so on.

This file isolates that skeleton once.

* `LocalResponseNodes` is the static ranked-node data with its root pinning.
* `LocalResponseRecursionAt Goal` fixes one accuracy `δ` and closes `Goal` at
  every node from `Goal` at its strictly lower-ranked children.
* `AccuracyPolymorphicLocalResponseRecursion Goal` keeps the accuracy
  quantifier inside the induction hypothesis, so a parent closing at `error`
  may request a child at any other positive accuracy such as `error / 2`.

`Goal` is an arbitrary predicate on an entry state, a target payoff, and an
accuracy.  No strategic content is added or removed by this file: the closers
are hypotheses, and the only theorems are the two well-founded compilations.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- The static skeleton shared by every well-founded local-response
construction: nodes carrying an entry state and a target payoff, ranked by a
well-founded relation, with a distinguished root pinned to `s₀` and `v`.

Ranking through `rank : Node → Rank` rather than directly on `Node` is what
lets a construction reuse one node at several ranks. -/
structure LocalResponseNodes (G : StochasticGame ι)
    (s₀ : G.State) (v : Payoff ι) where
  Rank : Type
  rankLt : Rank → Rank → Prop
  rank_wellFounded : WellFounded rankLt
  Node : Type
  rank : Node → Rank
  root : Node
  entry : Node → G.State
  target : Node → Payoff ι
  root_entry : entry root = s₀
  root_target : target root = v

namespace LocalResponseNodes

variable {G : StochasticGame ι} {s₀ : G.State} {v : Payoff ι}

/-- The rank pullback order on nodes is well founded, so a construction may
recurse on strictly lower-ranked children. -/
theorem nodeLt_wellFounded (N : G.LocalResponseNodes s₀ v) :
    WellFounded (N.rankLt.onFun N.rank) :=
  N.rank_wellFounded.onFun (f := N.rank)

end LocalResponseNodes

/-- One completed well-founded local-response recursion at accuracy `δ`,
generic in the local goal predicate `Goal`.

`closeLocalResponse` is the application-facing induction step. Its recursive
argument can only be invoked on a node of strictly lower rank, and returns
`Goal` at that child's own entry state and target payoff. This state-indexing
prevents a projected or hidden-belief core interface from being silently
replaced by the root problem.

The two strategic compatibility propositions are deliberately abstract
because their concrete statements depend on the local-response construction;
their proofs remain mandatory node-indexed fields and are passed explicitly
to the closer. -/
structure LocalResponseRecursionAt (G : StochasticGame ι)
    (Goal : G.State → Payoff ι → ℝ → Prop)
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    extends G.LocalResponseNodes s₀ v where
  MixedPlayerContinuationCompatibility : Node → Prop
  LegalCoreHistoryEntryInterface : Node → Prop
  mixedPlayerContinuationCompatibility :
    ∀ node, MixedPlayerContinuationCompatibility node
  legalCoreHistoryEntryInterface :
    ∀ node, LegalCoreHistoryEntryInterface node
  closeLocalResponse :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        Goal (entry child) (target child) δ) →
      MixedPlayerContinuationCompatibility node →
      LegalCoreHistoryEntryInterface node →
      Goal (entry node) (target node) δ

namespace LocalResponseRecursionAt

variable {G : StochasticGame ι} {Goal : G.State → Payoff ι → ℝ → Prop}
  {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Every node of a completed recursion carries the local goal, by
well-founded induction on the node rank. -/
theorem goal_at_node
    (construction : G.LocalResponseRecursionAt Goal s₀ v δ)
    (node : construction.Node) :
    Goal (construction.entry node) (construction.target node) δ := by
  have compile : ∀ node : construction.Node,
      Goal (construction.entry node) (construction.target node) δ :=
    construction.nodeLt_wellFounded.fix fun node recurse =>
      construction.closeLocalResponse node
        (fun child hchild => recurse child hchild)
        (construction.mixedPlayerContinuationCompatibility node)
        (construction.legalCoreHistoryEntryInterface node)
  exact compile node

/-- Compile the root of a completed local-response recursion to the goal at
the ambient entry state and target payoff. -/
theorem compile (construction : G.LocalResponseRecursionAt Goal s₀ v δ) :
    Goal s₀ v δ := by
  simpa only [construction.root_entry, construction.root_target] using
    construction.goal_at_node construction.root

end LocalResponseRecursionAt

/-- A well-founded local-response recursion whose induction hypothesis gives
each strictly lower-ranked child the goal at *every* positive accuracy.

Finite-prefix splices need this variance: to close at error `error` they
request children at strictly smaller errors such as `error / 2`.

Allowing both strategic interfaces to depend on the requested accuracy
preserves the actual quantifier order: a local implementation chosen for one
tolerance need not serve at every other tolerance. -/
structure AccuracyPolymorphicLocalResponseRecursion (G : StochasticGame ι)
    (Goal : G.State → Payoff ι → ℝ → Prop)
    (s₀ : G.State) (v : Payoff ι)
    extends G.LocalResponseNodes s₀ v where
  MixedPlayerContinuationCompatibility : Node → ℝ → Prop
  LegalCoreHistoryEntryInterface : Node → ℝ → Prop
  mixedPlayerContinuationCompatibility :
    ∀ node error, 0 < error →
      MixedPlayerContinuationCompatibility node error
  legalCoreHistoryEntryInterface :
    ∀ node error, 0 < error →
      LegalCoreHistoryEntryInterface node error
  closeLocalResponse :
    ∀ (node : Node) (error : ℝ), 0 < error →
      (∀ child : Node, rankLt (rank child) (rank node) →
        ∀ childError : ℝ, 0 < childError →
          Goal (entry child) (target child) childError) →
      MixedPlayerContinuationCompatibility node error →
      LegalCoreHistoryEntryInterface node error →
      Goal (entry node) (target node) error

namespace AccuracyPolymorphicLocalResponseRecursion

variable {G : StochasticGame ι} {Goal : G.State → Payoff ι → ℝ → Prop}
  {s₀ : G.State} {v : Payoff ι}

/-- Compile the whole positive-accuracy family at every node by one
well-founded induction.  The recursive hypothesis retains the accuracy
quantifier, so a parent may invoke one child at several accuracies. -/
theorem goal_at_node
    (construction :
      G.AccuracyPolymorphicLocalResponseRecursion Goal s₀ v)
    (node : construction.Node) :
    ∀ error : ℝ, 0 < error →
      Goal (construction.entry node) (construction.target node) error := by
  have compile : ∀ node : construction.Node, ∀ error : ℝ, 0 < error →
      Goal (construction.entry node) (construction.target node) error :=
    construction.nodeLt_wellFounded.fix fun node recurse error error_pos =>
      construction.closeLocalResponse node error error_pos
        (fun child hchild childError childError_pos =>
          recurse child hchild childError childError_pos)
        (construction.mixedPlayerContinuationCompatibility node error error_pos)
        (construction.legalCoreHistoryEntryInterface node error error_pos)
  exact compile node

/-- Compile the root at any requested positive accuracy. -/
theorem compile
    (construction :
      G.AccuracyPolymorphicLocalResponseRecursion Goal s₀ v)
    (error : ℝ) (error_pos : 0 < error) :
    Goal s₀ v error := by
  simpa only [construction.root_entry, construction.root_target] using
    construction.goal_at_node construction.root error error_pos

end AccuracyPolymorphicLocalResponseRecursion

end StochasticGame
end GameTheory
