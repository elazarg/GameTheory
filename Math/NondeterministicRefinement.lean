/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction
import Math.Coupling

/-!
# Nondeterministic refinement of probability-law families

Neutral mathematical vocabulary for systems where a single object (a profile,
state, or trace) does not determine one probability law, but a *family* of laws
indexed by an unweighted **resolution**:

```text
LawFamily R α := R → PMF α
```

`R` is a scheduler, environment, implementation choice, tie-breaker, completion,
or public string. No probability law on `R` is assumed — that is an extra
modeling choice, not part of bare nondeterminism. The two questions this module
formalizes are:

* **Invariance** (`InvariantUnder`): does the law, viewed through a projection,
  ignore the resolution? When it does, the nondeterminism *disappears at that
  boundary* and the family collapses to a single law (`projectedLaw`).
* **Refinement** (`Refines`): does every implementation resolution have a
  matching specification resolution after projection? This is the law-family
  analogue of behavioral inclusion, with the quantifier order made explicit.

The point is to **not** bake in one semantic level: the same `InvariantUnder`
says "schedule is erased by observations" or "payoff law is independent of the
environment" depending on the projection supplied.

This module defines no game-theoretic concepts (no Nash, no behavioral
strategies, no payoff transport) and takes no stance on whether nondeterminism
is demonic, angelic, robust, or erased — those are interpretations later layers
build on this vocabulary. It builds on `Math.Coupling` for the relational
variant and is the law-family companion to `Math.TraceRun`.
-/

set_option autoImplicit false

namespace Math
namespace NondetRefinement

variable {R S T α β γ : Type*}

/-- A family of probability laws indexed by an unweighted resolution type `R`.
There is no probability law on `R` itself. -/
abbrev LawFamily (R α : Type*) := R → PMF α

/-! ## Invariance -/

/-- `law` is **invariant under** the projection `proj` when the projected law
does not depend on the resolution. With `proj = id` this is full resolution
independence (`Invariant`); with a coarser `proj` it says the boundary `proj`
erases the nondeterminism even if the underlying law does not. -/
def InvariantUnder (proj : α → β) (law : R → PMF α) : Prop :=
  ∀ r r', (law r).map proj = (law r').map proj

/-- Full invariance: the entire law is resolution-independent. -/
abbrev Invariant (law : R → PMF α) : Prop := InvariantUnder id law

/-- Coarsening: invariance under a projection is preserved by composing with any
further map. If observations already erase the resolution, so does any function
of the observations. -/
theorem InvariantUnder.comp {proj : α → β} {law : R → PMF α}
    (h : InvariantUnder proj law) (g : β → γ) :
    InvariantUnder (g ∘ proj) law := by
  intro r r'
  rw [← PMF.map_comp, ← PMF.map_comp, h r r']

/-- Full invariance implies invariance under every projection. -/
theorem Invariant.invariantUnder {law : R → PMF α} (h : Invariant law)
    (proj : α → β) : InvariantUnder proj law := by
  intro r r'
  have hrr' := h r r'
  rw [PMF.map_id, PMF.map_id] at hrr'
  rw [hrr']

/-- The common projected law, witnessed by a chosen resolution `r₀`. Under
invariance this is independent of the choice (`InvariantUnder.projectedLaw_eq`),
so it is *the* law the boundary `proj` sees. -/
noncomputable def projectedLaw (proj : α → β) (law : R → PMF α) (r₀ : R) : PMF β :=
  (law r₀).map proj

/-- Collapse: under invariance every resolution projects to the same law. -/
theorem InvariantUnder.projectedLaw_eq {proj : α → β} {law : R → PMF α}
    (h : InvariantUnder proj law) (r₀ r : R) :
    (law r).map proj = projectedLaw proj law r₀ :=
  h r r₀

/-! ## Refinement -/

/-- **Exact refinement**: every implementation law, viewed through `proj`,
coincides with some specification law. Equivalently
`Set.range (fun r => (impl r).map proj) ⊆ Set.range spec`. The quantifier order
— `∀ impl resolution, ∃ spec resolution` — is the content. -/
def Refines (proj : α → β) (impl : R → PMF α) (spec : S → PMF β) : Prop :=
  ∀ r, ∃ s, (impl r).map proj = spec s

/-- Reflexivity along the identity projection. -/
theorem Refines.refl (law : R → PMF α) : Refines id law law :=
  fun r => ⟨r, PMF.map_id (law r)⟩

/-- Transitivity along composed projections. -/
theorem Refines.trans {proj₁ : α → β} {proj₂ : β → γ}
    {impl : R → PMF α} {mid : S → PMF β} {spec : T → PMF γ}
    (h₁ : Refines proj₁ impl mid) (h₂ : Refines proj₂ mid spec) :
    Refines (proj₂ ∘ proj₁) impl spec := by
  intro r
  obtain ⟨s, hs⟩ := h₁ r
  obtain ⟨t, ht⟩ := h₂ s
  exact ⟨t, by rw [← PMF.map_comp, hs, ht]⟩

/-- A **functional** witness for refinement: a map on resolutions realizing the
projected-law equality pointwise. Carries data, like `Coupling.HasCoupling`. -/
structure FunRefinement (proj : α → β) (impl : R → PMF α) (spec : S → PMF β) where
  /-- The specification resolution chosen for each implementation resolution. -/
  resolve : R → S
  /-- Each implementation law projects exactly onto its chosen spec law. -/
  map_eq : ∀ r, (impl r).map proj = spec (resolve r)

/-- A functional witness yields exact refinement. -/
theorem FunRefinement.refines {proj : α → β} {impl : R → PMF α} {spec : S → PMF β}
    (h : FunRefinement proj impl spec) : Refines proj impl spec :=
  fun r => ⟨h.resolve r, h.map_eq r⟩

/-- Interplay: if the specification family is invariant, refinement collapses the
implementation family's projected nondeterminism — `impl` is itself invariant
under `proj`, so the spec resolution is irrelevant. -/
theorem Refines.invariantUnder_of_spec_invariant {proj : α → β}
    {impl : R → PMF α} {spec : S → PMF β}
    (hr : Refines proj impl spec) (hs : Invariant spec) :
    InvariantUnder proj impl := by
  intro r r'
  obtain ⟨s, hs1⟩ := hr r
  obtain ⟨s', hs2⟩ := hr r'
  rw [hs1, hs2]
  have := hs s s'
  rwa [PMF.map_id, PMF.map_id] at this

/-! ## Relational refinement via couplings

`Refines` asks for *equality* of projected laws. Replacing the functional
projection by an arbitrary relation and equality by a coupling gives the
relational variant, reusing `Math.Coupling`. With the functional relation
`fun a b => proj a = b` it recovers `Refines` (`refinesRel_projEq_iff`). -/

open Coupling

/-- **Relational refinement**: every implementation law is `Rel`-coupled to some
specification law. -/
def RefinesRel (Rel : α → β → Prop) (impl : R → PMF α) (spec : S → PMF β) : Prop :=
  ∀ r, ∃ s, Nonempty (HasCoupling Rel (impl r) (spec s))

/-- Relation weakening: a coarser relation still refines. -/
theorem RefinesRel.mono {Rel Rel' : α → β → Prop} {impl : R → PMF α} {spec : S → PMF β}
    (h : RefinesRel Rel impl spec) (hsub : ∀ a b, Rel a b → Rel' a b) :
    RefinesRel Rel' impl spec :=
  fun r => (h r).imp fun _ => Nonempty.map fun c => c.mono hsub

/-- Functional-projection coupling (refinement direction): a coupling for
`fun a b => proj a = b` between `μ` and `ν` exists iff `μ.map proj = ν`. The
transpose of `Coupling.hasCoupling_proj_iff_map_eq`. -/
theorem hasCoupling_projEq_iff_map_eq {proj : α → β} {μ : PMF α} {ν : PMF β} :
    Nonempty (HasCoupling (fun a b => proj a = b) μ ν) ↔ μ.map proj = ν := by
  refine ⟨fun ⟨c⟩ => ?_, fun h => ?_⟩
  · calc μ.map proj
        = (c.joint.map Prod.fst).map proj := by rw [c.marginal_fst]
      _ = c.joint.map (proj ∘ Prod.fst) := by rw [← PMF.map_comp]
      _ = c.joint.map Prod.snd := by
            change c.joint.bind (fun p => PMF.pure (proj p.1))
                = c.joint.bind (fun p => PMF.pure p.2)
            apply Math.ProbabilityMassFunction.bind_congr_on_support
            intro p hp
            rw [c.rel_holds p hp]
      _ = ν := c.marginal_snd
  · refine ⟨{ joint := μ.map (fun a => (a, proj a))
              marginal_fst := ?_
              marginal_snd := ?_
              rel_holds := ?_ }⟩
    · rw [PMF.map_comp]; change μ.map id = μ; exact PMF.map_id μ
    · rw [PMF.map_comp]; change μ.map proj = ν; exact h
    · intro p hp
      simp only [PMF.support_map, Set.mem_image] at hp
      obtain ⟨a, _ha, heq⟩ := hp
      rw [← heq]

/-- Relational refinement along the functional relation is exact refinement. -/
theorem refinesRel_projEq_iff {proj : α → β} {impl : R → PMF α} {spec : S → PMF β} :
    RefinesRel (fun a b => proj a = b) impl spec ↔ Refines proj impl spec :=
  forall_congr' fun _ => exists_congr fun _ => hasCoupling_projEq_iff_map_eq

end NondetRefinement
end Math
