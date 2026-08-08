/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.AdaptiveLocalResponseRecursion

/-!
# A typed obstruction atlas for adaptive local responses

An exhaustive case split is useful only when every leaf carries enough data
to advance the proof.  This file enforces four honest leaf forms:

* `close`: the current adaptive potential certificate;
* `descend`: a strictly lower child and a reconstruction map;
* `account`: realized account data together with the theorem consuming it
  into the current certificate;
* `obstruction`: an explicit witness describing why construction failed.

The well-founded compiler returns either the root certificate or an actual
obstruction witness at some visited node.  In particular, a bare budget,
span membership, circulation, or rank comparison cannot masquerade as a
successful terminal leaf.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- One productive or explicitly blocked step at a node of an adaptive
local-response atlas. -/
inductive AdaptiveLocalResponseStepAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {Rank Node : Type}
    (rankLt : Rank → Rank → Prop) (rank : Node → Rank)
    (entry : Node → G.State) (target : Node → Payoff ι)
    (error : ℝ) (Obstruction : Node → Type)
    (node : Node) : Type 1
  | close
      (certificate :
        G.IsAdaptivePotentialCertificateAt
          (entry node) (target node) error)
  | descend
      (child : Node)
      (decrease : rankLt (rank child) (rank node))
      (resume :
        G.IsAdaptivePotentialCertificateAt
            (entry child) (target child) error →
          G.IsAdaptivePotentialCertificateAt
            (entry node) (target node) error)
  | account
      (Account : Type)
      (ledger : Account)
      (discharge :
        Account →
          G.IsAdaptivePotentialCertificateAt
            (entry node) (target node) error)
  | obstruction
      (witness : Obstruction node)

/-- A well-founded exhaustive classifier whose unsuccessful leaves carry a
typed obstruction. -/
structure AdaptiveLocalResponseAtlasAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (error : ℝ)
    extends G.LocalResponseNodes s₀ v where
  Obstruction : Node → Type
  classify :
    ∀ node,
      AdaptiveLocalResponseStepAt G rankLt rank entry target error
        Obstruction node

namespace AdaptiveLocalResponseAtlasAt

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι} {error : ℝ}

/-- Compile the well-founded case tree.  The right branch contains a
specific blocked node and its obstruction witness. -/
theorem certificate_or_obstruction
    (atlas : G.AdaptiveLocalResponseAtlasAt s₀ v error) :
    G.IsAdaptivePotentialCertificateAt s₀ v error ∨
      ∃ node : atlas.Node, Nonempty (atlas.Obstruction node) := by
  have hnode : WellFounded (atlas.rankLt.onFun atlas.rank) :=
    atlas.nodeLt_wellFounded
  let compile : ∀ node : atlas.Node,
      G.IsAdaptivePotentialCertificateAt
          (atlas.entry node) (atlas.target node) error ∨
        ∃ blocked : atlas.Node,
          Nonempty (atlas.Obstruction blocked) :=
    hnode.fix fun node recurse =>
      match atlas.classify node with
      | .close certificate => Or.inl certificate
      | .descend child decrease resume =>
          match recurse child decrease with
          | Or.inl childCertificate =>
              Or.inl (resume childCertificate)
          | Or.inr obstruction =>
              Or.inr obstruction
      | .account _ ledger discharge =>
          Or.inl (discharge ledger)
      | .obstruction witness =>
          Or.inr ⟨node, ⟨witness⟩⟩
  simpa only [atlas.root_entry, atlas.root_target] using
    compile atlas.root

/-- If every obstruction type is empty, the atlas constructs the root
adaptive potential certificate. -/
theorem toIsAdaptivePotentialCertificateAt
    (atlas : G.AdaptiveLocalResponseAtlasAt s₀ v error)
    (hno : ∀ node, IsEmpty (atlas.Obstruction node)) :
    G.IsAdaptivePotentialCertificateAt s₀ v error := by
  rcases atlas.certificate_or_obstruction with certificate | obstruction
  · exact certificate
  · obtain ⟨node, ⟨witness⟩⟩ := obstruction
    exact False.elim ((hno node).false witness)

end AdaptiveLocalResponseAtlasAt

/-- An obstruction-free typed atlas at every positive accuracy. -/
structure CompletedAdaptiveLocalResponseAtlas
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) where
  atlasAt :
    ∀ error : ℝ, 0 < error →
      G.AdaptiveLocalResponseAtlasAt s₀ v error
  obstruction_empty :
    ∀ error (herror : 0 < error)
      (node : (atlasAt error herror).Node),
      IsEmpty ((atlasAt error herror).Obstruction node)

namespace CompletedAdaptiveLocalResponseAtlas

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι}

/-- An obstruction-free completed atlas supplies the verifier at every
accuracy. -/
theorem isAdaptivePotentialEquilibriumCertificate
    (atlas : G.CompletedAdaptiveLocalResponseAtlas s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v :=
  fun error herror =>
    (atlas.atlasAt error herror).toIsAdaptivePotentialCertificateAt
      (atlas.obstruction_empty error herror)

/-- Capstone for the typed obstruction atlas. -/
theorem isUniformEquilibriumPayoff
    (atlas : G.CompletedAdaptiveLocalResponseAtlas s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    s₀ v atlas.isAdaptivePotentialEquilibriumCertificate

end CompletedAdaptiveLocalResponseAtlas

end StochasticGame
end GameTheory
