/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.LocalResponseRecursion
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.PhaseCertificate

/-!
# Well-founded public local-response recursion

This file is the thin packaging layer between a completed public
local-response construction and the existing public-phase verifier.

At one accuracy level, a construction consists of state-indexed nodes ranked
by a well-founded relation. The local closer at a node may use public-phase
certificates only from strictly lower-ranked nodes, at the entry state and
target payoff carried by each child. It must also consume two explicit
strategic witnesses:

* mixed-player continuation compatibility;
* a legal core-history entry and continuation interface.

The local closer returns the existing
`IsPublicPhasePunishmentSystemAt` certificate.  Thus no strategic content is
hidden in this packaging layer.  A uniform construction supplies such a
completed recursion for every positive accuracy.  The existing public-phase
and adaptive-potential bridges then yield a uniform equilibrium payoff.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- One completed well-founded local-response recursion at accuracy `δ`.

`closeLocalResponse` is the application-facing induction step. Its recursive
argument can only be invoked on a node of strictly lower rank, and returns a
certificate for that child's own entry state and target payoff. This
state-indexing prevents a projected or hidden-belief core interface from being
silently replaced by the root problem.

The two strategic compatibility propositions are deliberately abstract here
because their concrete statements depend on the local-response construction;
their proofs remain mandatory node-indexed fields and are passed explicitly
to the closer.

This is the `Goal`-generic `LocalResponseRecursionAt` at the public-phase
punishment-system goal; all field names and the well-founded compilation are
inherited from there. -/
abbrev PublicLocalResponseRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Type 1 :=
  G.LocalResponseRecursionAt G.IsPublicPhasePunishmentSystemAt s₀ v δ

namespace PublicLocalResponseRecursionAt

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Compile the root of a completed local-response recursion to the existing
public-phase punishment-system interface. -/
theorem toIsPublicPhasePunishmentSystemAt
    (C : G.PublicLocalResponseRecursionAt s₀ v δ) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  C.compile

end PublicLocalResponseRecursionAt

/-- A completed public local-response recursion at every positive accuracy.

The recursion, its phase spaces, rank, and strategic witnesses may all depend
on `δ`.  This quantifier is essential: one local certificate at a fixed
accuracy does not imply a uniform equilibrium. -/
structure CompletedPublicLocalResponseRecursion
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) where
  recursionAt :
    ∀ δ : ℝ, 0 < δ →
      G.PublicLocalResponseRecursionAt s₀ v δ

namespace CompletedPublicLocalResponseRecursion

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {s₀ : G.State} {v : Payoff ι}

/-- Extract the public-phase punishment system at any requested positive
accuracy. -/
theorem isPublicPhasePunishmentSystemAt
    (C : G.CompletedPublicLocalResponseRecursion s₀ v)
    (δ : ℝ) (hδ : 0 < δ) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  (C.recursionAt δ hδ).toIsPublicPhasePunishmentSystemAt

/-- Compile the completed recursion at one accuracy to the existing adaptive
potential certificate. -/
theorem isAdaptivePotentialCertificateAt
    (C : G.CompletedPublicLocalResponseRecursion s₀ v)
    (δ : ℝ) (hδ : 0 < δ) :
    G.IsAdaptivePotentialCertificateAt s₀ v δ :=
  G.isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
    s₀ v δ (C.isPublicPhasePunishmentSystemAt δ hδ)

/-- A completed recursion for every positive accuracy is an adaptive
potential equilibrium certificate. -/
theorem isAdaptivePotentialEquilibriumCertificate
    (C : G.CompletedPublicLocalResponseRecursion s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v :=
  fun δ hδ => C.isAdaptivePotentialCertificateAt δ hδ

/-- Capstone packaging theorem: a completed well-founded public
local-response recursion at every positive accuracy yields a uniform
equilibrium payoff through the existing adaptive-potential verifier. -/
theorem isUniformEquilibriumPayoff
    (C : G.CompletedPublicLocalResponseRecursion s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    s₀ v C.isAdaptivePotentialEquilibriumCertificate

/-- A completed public local-response recursion supplies exactly the
quantitative deviation-cap constructor isolated in `Uniform`. -/
theorem hasUniformDeviationCapConstructor
    (C : G.CompletedPublicLocalResponseRecursion s₀ v) :
    G.HasUniformDeviationCapConstructor s₀ v :=
  (G.hasUniformDeviationCapConstructor_iff s₀ v).mpr
    C.isUniformEquilibriumPayoff

end CompletedPublicLocalResponseRecursion

/-- Existential construction capstone: once the global invariant produces a
completed public local-response recursion and its target payoff, the
quantitative existence obligation is discharged. -/
theorem exists_uniformDeviationCapConstructor_of_completedPublicResponse
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (hconstruction :
      ∃ v : Payoff ι,
        Nonempty (G.CompletedPublicLocalResponseRecursion s₀ v)) :
    ∃ v : Payoff ι, G.HasUniformDeviationCapConstructor s₀ v := by
  obtain ⟨v, ⟨C⟩⟩ := hconstruction
  exact ⟨v, C.hasUniformDeviationCapConstructor⟩

end StochasticGame
end GameTheory
