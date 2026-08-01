/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptiveCertificate
import GameTheory.Concepts.Stochastic.PublicLocalResponseRecursion

/-!
# Well-founded adaptive local-response recursion

The public-phase recursion is useful when every local inequality is available
at every public history.  A stopped selection or coupling argument often
provides only the expectation-level inequalities required by
`IsAdaptivePotentialCertificateAt`: histories outside the prescribed or
deviating law should not become artificial obligations.

This file provides the corresponding well-founded packaging.  It changes no
strategic hypothesis.  A local closer must still construct an honest adaptive
potential certificate at the current entry state and target, using only
certificates at strictly lower-ranked children.  The final verifier already
accepts this interface directly.

Every completed public recursion embeds into this adaptive recursion.  The
reverse implication is intentionally absent.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- One completed well-founded local-response recursion whose local result is
the expectation-level adaptive potential certificate.

This is the `Goal`-generic `LocalResponseRecursionAt` at the adaptive
potential certificate goal: it differs from
`PublicLocalResponseRecursionAt` in exactly that predicate. -/
abbrev AdaptiveLocalResponseRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Type 1 :=
  G.LocalResponseRecursionAt G.IsAdaptivePotentialCertificateAt s₀ v δ

namespace AdaptiveLocalResponseRecursionAt

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Compile the root certificate by well-founded induction on the node rank. -/
theorem toIsAdaptivePotentialCertificateAt
    (construction : G.AdaptiveLocalResponseRecursionAt s₀ v δ) :
    G.IsAdaptivePotentialCertificateAt s₀ v δ :=
  construction.compile

/-- A public local-response recursion is, in particular, an adaptive one. -/
def ofPublic
    (construction : G.PublicLocalResponseRecursionAt s₀ v δ) :
    G.AdaptiveLocalResponseRecursionAt s₀ v δ where
  Rank := PUnit
  rankLt := fun _ _ => False
  rank_wellFounded := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
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
  closeLocalResponse _ _ _ _ :=
    G.isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
      s₀ v δ construction.toIsPublicPhasePunishmentSystemAt

end AdaptiveLocalResponseRecursionAt

/-- An adaptive local-response recursion at every positive accuracy. -/
structure CompletedAdaptiveLocalResponseRecursion
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) where
  recursionAt :
    ∀ δ : ℝ, 0 < δ →
      G.AdaptiveLocalResponseRecursionAt s₀ v δ

namespace CompletedAdaptiveLocalResponseRecursion

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι}

/-- Forget the pointwise public-history strength of a completed public
recursion and retain its expectation-level certificates. -/
def ofPublic
    (construction : G.CompletedPublicLocalResponseRecursion s₀ v) :
    G.CompletedAdaptiveLocalResponseRecursion s₀ v where
  recursionAt δ hδ :=
    AdaptiveLocalResponseRecursionAt.ofPublic
      (construction.recursionAt δ hδ)

/-- A completed adaptive recursion is exactly sufficient for the existing
adaptive-potential equilibrium verifier. -/
theorem isAdaptivePotentialEquilibriumCertificate
    (construction : G.CompletedAdaptiveLocalResponseRecursion s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v :=
  fun δ hδ =>
    (construction.recursionAt δ hδ).toIsAdaptivePotentialCertificateAt

/-- Capstone for the expectation-level recursion. -/
theorem isUniformEquilibriumPayoff
    (construction : G.CompletedAdaptiveLocalResponseRecursion s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    s₀ v construction.isAdaptivePotentialEquilibriumCertificate

end CompletedAdaptiveLocalResponseRecursion

/-- Existential capstone for an expectation-level local-response
construction. -/
theorem exists_uniformDeviationCapConstructor_of_completedAdaptiveResponse
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (hconstruction :
      ∃ v : Payoff ι,
        Nonempty (G.CompletedAdaptiveLocalResponseRecursion s₀ v)) :
    ∃ v : Payoff ι, G.HasUniformDeviationCapConstructor s₀ v := by
  obtain ⟨v, ⟨construction⟩⟩ := hconstruction
  exact ⟨v,
    (G.hasUniformDeviationCapConstructor_iff s₀ v).mpr
      construction.isUniformEquilibriumPayoff⟩

end StochasticGame
end GameTheory
