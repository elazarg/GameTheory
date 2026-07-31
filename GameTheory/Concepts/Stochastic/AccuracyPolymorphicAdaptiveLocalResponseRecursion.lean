/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptiveLocalResponseRecursion
import GameTheory.Concepts.Stochastic.PublicFixedDepthAdaptiveCertificate

/-!
# Accuracy-polymorphic adaptive local-response recursion

`AdaptiveLocalResponseRecursionAt` fixes one error tolerance throughout its
well-founded recursion.  That interface remains useful when a local closer
uses every child at exactly the parent tolerance.  Finite-prefix splices have
a different variance: to construct a parent certificate at error `δ`, they
request child certificates at smaller positive errors such as `δ / 2`.

This file adds a backward-compatible recursion whose induction hypothesis is
polymorphic in the child error.  At a node, the closer may request any
strictly lower-ranked child at any positive tolerance.  Well-founded
induction first constructs the whole positive-error family at each child and
then exposes that family to the parent closer.

The strategic compatibility and legal-entry interfaces remain explicit and
may depend on the requested parent error.  No game-theoretic hypothesis is
hidden in the recursion package.

The final section connects the polymorphic induction hypothesis to the
existing fixed-depth deviation-safe public-selector compiler.  Its scope is
the same as that compiler: selector terminal states are globally stopped
under every joint action.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- A well-founded local-response recursion whose induction hypothesis gives
each lower-ranked child certificate at every positive accuracy.

Allowing both strategic interfaces to depend on `error` preserves the actual
quantifier order: a local implementation chosen for one tolerance need not
serve at every other tolerance. -/
structure AccuracyPolymorphicAdaptiveLocalResponseRecursion
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Finite (G.Act who)]
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
          G.IsAdaptivePotentialCertificateAt
            (entry child) (target child) childError) →
      MixedPlayerContinuationCompatibility node error →
      LegalCoreHistoryEntryInterface node error →
      G.IsAdaptivePotentialCertificateAt
        (entry node) (target node) error

namespace AccuracyPolymorphicAdaptiveLocalResponseRecursion

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]
  {s₀ : G.State} {v : Payoff ι}

/-- Compile every node at every positive error by one well-founded
induction.  The recursive hypothesis retains the error quantifier, so a
parent may invoke one child at several different accuracies. -/
theorem isAdaptivePotentialCertificateAt
    (construction :
      G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v)
    (error : ℝ) (error_pos : 0 < error) :
    G.IsAdaptivePotentialCertificateAt s₀ v error := by
  let nodeLt : construction.Node → construction.Node → Prop :=
    construction.rankLt.onFun construction.rank
  have node_wellFounded : WellFounded nodeLt :=
    construction.rank_wellFounded.onFun (f := construction.rank)
  let compile : ∀ node : construction.Node,
      ∀ childError : ℝ, 0 < childError →
        G.IsAdaptivePotentialCertificateAt
          (construction.entry node)
          (construction.target node) childError :=
    node_wellFounded.fix fun node recurse childError childError_pos =>
      construction.closeLocalResponse node childError childError_pos
        (fun child child_lt requestedError requestedError_pos =>
          recurse child child_lt requestedError requestedError_pos)
        (construction.mixedPlayerContinuationCompatibility
          node childError childError_pos)
        (construction.legalCoreHistoryEntryInterface
          node childError childError_pos)
  simpa only [construction.root_entry, construction.root_target] using
    compile construction.root error error_pos

/-- The polymorphic recursion supplies the verifier's all-errors adaptive
certificate family directly. -/
theorem isAdaptivePotentialEquilibriumCertificate
    (construction :
      G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v :=
  fun error error_pos =>
    construction.isAdaptivePotentialCertificateAt error error_pos

/-- Compile the polymorphic recursion to the pre-existing completed adaptive
recursion interface.  Each requested tolerance is represented by a one-node
recursion carrying the already well-foundedly compiled root certificate. -/
def toCompletedAdaptiveLocalResponseRecursion
    (construction :
      G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v) :
    G.CompletedAdaptiveLocalResponseRecursion s₀ v where
  recursionAt error error_pos := {
    Rank := PUnit
    rankLt := fun _ _ => False
    rank_wellFounded := ⟨fun _ => ⟨_, fun _ impossible => impossible.elim⟩⟩
    Node := PUnit
    rank := fun _ => PUnit.unit
    root := PUnit.unit
    entry := fun _ => s₀
    target := fun _ => v
    root_entry := rfl
    root_target := rfl
    MixedPlayerContinuationCompatibility := fun _ => True
    LegalCoreHistoryEntryInterface := fun _ => True
    mixedPlayerContinuationCompatibility := fun _ => True.intro
    legalCoreHistoryEntryInterface := fun _ => True.intro
    closeLocalResponse := fun _ _ _ _ =>
      construction.isAdaptivePotentialCertificateAt error error_pos
  }

/-- Existing completed adaptive recursions embed without changing their
semantics.  The embedding has one node because the existing package has
already compiled its error-specific well-founded recursion. -/
def ofCompletedAdaptiveLocalResponseRecursion
    (construction : G.CompletedAdaptiveLocalResponseRecursion s₀ v) :
    G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v where
  Rank := PUnit
  rankLt := fun _ _ => False
  rank_wellFounded := ⟨fun _ => ⟨_, fun _ impossible => impossible.elim⟩⟩
  Node := PUnit
  rank := fun _ => PUnit.unit
  root := PUnit.unit
  entry := fun _ => s₀
  target := fun _ => v
  root_entry := rfl
  root_target := rfl
  MixedPlayerContinuationCompatibility := fun _ _ => True
  LegalCoreHistoryEntryInterface := fun _ _ => True
  mixedPlayerContinuationCompatibility := fun _ _ _ => True.intro
  legalCoreHistoryEntryInterface := fun _ _ _ => True.intro
  closeLocalResponse := fun _ error error_pos _ _ _ =>
    (construction.recursionAt error error_pos).toIsAdaptivePotentialCertificateAt

/-- Existing completed public recursions embed through the established
public-to-adaptive bridge. -/
def ofCompletedPublicLocalResponseRecursion
    (construction : G.CompletedPublicLocalResponseRecursion s₀ v) :
    G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v :=
  ofCompletedAdaptiveLocalResponseRecursion
    (CompletedAdaptiveLocalResponseRecursion.ofPublic construction)

/-- Uniform-equilibrium capstone for the accuracy-polymorphic recursion. -/
theorem isUniformEquilibriumPayoff
    (construction :
      G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    s₀ v construction.isAdaptivePotentialEquilibriumCertificate

end AccuracyPolymorphicAdaptiveLocalResponseRecursion

/-- Static data for a well-founded family of exact fixed-depth public
selector splices.

`childNode node child` is required to be strictly lower-ranked for every
selector outcome, including outcomes of zero probability.  This matches the
finite-child family consumed by the existing splice theorem and prevents an
unproved support restriction from entering the induction.

The compatibility and legal-entry predicates are retained explicitly even
though the globally stopped fixed-depth selector closes the local adaptive
certificate without inspecting their witnesses. -/
structure FixedDepthAccuracyPolymorphicLocalResponseData
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Finite (G.Act who)]
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
  Child : Node → Type
  child_finite : ∀ node, Finite (Child node)
  childNode : ∀ node, Child node → Node
  child_rank_lt :
    ∀ node child, rankLt (rank (childNode node child)) (rank node)
  selector : ∀ node, DeviationSafePublicCoinSelector G (Child node)
  selection : Node → G.BehaviorProfile
  fuel : Node → ℕ
  fuel_covers_rank :
    ∀ node, (selector node).process.rank (entry node) ≤ fuel node
  terminal_entry :
    ∀ node state, (selector node).process.terminal state →
      state =
        entry (childNode node ((selector node).process.observe state))
  exact_target :
    ∀ node who,
      expect ((selector node).process.value (entry node))
        (fun child => target (childNode node child) who) =
          target node who
  MixedPlayerContinuationCompatibility : Node → ℝ → Prop
  LegalCoreHistoryEntryInterface : Node → ℝ → Prop
  mixedPlayerContinuationCompatibility :
    ∀ node error, 0 < error →
      MixedPlayerContinuationCompatibility node error
  legalCoreHistoryEntryInterface :
    ∀ node error, 0 < error →
      LegalCoreHistoryEntryInterface node error

namespace FixedDepthAccuracyPolymorphicLocalResponseData

open FixedDepthAdaptivePotentialSplice

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]
  {s₀ : G.State} {v : Payoff ι}

/-- Convert exact fixed-depth selector data to an accuracy-polymorphic
well-founded recursion.  The local compiler is free to request the selected
child at `error / 2` because the induction hypothesis supplies every
positive child error. -/
def toAccuracyPolymorphicAdaptiveLocalResponseRecursion
    (data :
      G.FixedDepthAccuracyPolymorphicLocalResponseData s₀ v) :
    G.AccuracyPolymorphicAdaptiveLocalResponseRecursion s₀ v where
  Rank := data.Rank
  rankLt := data.rankLt
  rank_wellFounded := data.rank_wellFounded
  Node := data.Node
  rank := data.rank
  root := data.root
  entry := data.entry
  target := data.target
  root_entry := data.root_entry
  root_target := data.root_target
  MixedPlayerContinuationCompatibility :=
    data.MixedPlayerContinuationCompatibility
  LegalCoreHistoryEntryInterface := data.LegalCoreHistoryEntryInterface
  mixedPlayerContinuationCompatibility :=
    data.mixedPlayerContinuationCompatibility
  legalCoreHistoryEntryInterface := data.legalCoreHistoryEntryInterface
  closeLocalResponse :=
    fun node error error_pos childCertificates _ _ => by
      letI : Finite (data.Child node) := data.child_finite node
      letI : Fintype (data.Child node) :=
        Fintype.ofFinite (data.Child node)
      apply
        isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
          (selector := data.selector node)
          (entry := fun child => data.entry (data.childNode node child))
          (target := fun child => data.target (data.childNode node child))
          (initial := data.entry node)
          (fuel := data.fuel node)
          (data.selection node) (data.target node) error error_pos
      · exact data.fuel_covers_rank node
      · exact data.terminal_entry node
      · exact data.exact_target node
      · intro child childError childError_pos
        exact
          childCertificates (data.childNode node child)
            (data.child_rank_lt node child) childError childError_pos

/-- Direct all-errors certificate capstone for exact fixed-depth selector
recursions. -/
theorem isAdaptivePotentialEquilibriumCertificate
    (data :
      G.FixedDepthAccuracyPolymorphicLocalResponseData s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v := by
  let recursion :=
    data.toAccuracyPolymorphicAdaptiveLocalResponseRecursion
  exact recursion.isAdaptivePotentialEquilibriumCertificate

/-- Uniform-equilibrium capstone for exact fixed-depth selector recursions. -/
theorem isUniformEquilibriumPayoff
    (data :
      G.FixedDepthAccuracyPolymorphicLocalResponseData s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  let recursion :=
    data.toAccuracyPolymorphicAdaptiveLocalResponseRecursion
  exact recursion.isUniformEquilibriumPayoff

end FixedDepthAccuracyPolymorphicLocalResponseData

end StochasticGame
end GameTheory
