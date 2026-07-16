/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction

/-!
# Couplings and relation lifting on PMFs

A `HasCoupling R μ ν` is a witness that the PMFs `μ : PMF α` and
`ν : PMF β` are related by `R : α → β → Prop` in the lifted sense:
there is a joint distribution on `α × β` whose marginals are `μ` and `ν`
and whose support is contained in `R`.

This is the standard categorical-probability primitive (Larsen-Skou,
Desharnais-Edalat-Panangaden, Jacobs). It generalizes:

* equality of PMFs (`R = (· = ·)`);
* projection-along-a-function (`R a b ↔ a = f b`);
* probabilistic bisimulation (`R` is the bisimulation relation).

The structural lemmas here — `pure`, `map`, `bind` — give relation
lifting its compositional power: if a relation lifts at the leaves and
through one step, it lifts through the whole Kleisli computation.
-/

set_option autoImplicit false

namespace Math
namespace Coupling

variable {α α' β β' γ δ : Type*}

/-- A coupling witnessing `R`-relatedness of two PMFs: a joint
distribution with the prescribed marginals whose support lies in `R`. -/
structure HasCoupling (R : α → β → Prop) (μ : PMF α) (ν : PMF β) where
  joint : PMF (α × β)
  marginal_fst : joint.map Prod.fst = μ
  marginal_snd : joint.map Prod.snd = ν
  rel_holds : ∀ p ∈ joint.support, R p.1 p.2

namespace HasCoupling

-- ============================================================================
-- Structural lemmas
-- ============================================================================

/-- Point-mass coupling. -/
noncomputable def pure {R : α → β → Prop} (a : α) (b : β) (h : R a b) :
    HasCoupling R (PMF.pure a) (PMF.pure b) where
  joint := PMF.pure (a, b)
  marginal_fst := by simp [PMF.pure_map]
  marginal_snd := by simp [PMF.pure_map]
  rel_holds := by
    intro p hp
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact h

/-- Coupling-relation weakening: any relation containing the coupling's
relation gives a coupling for the same PMFs. -/
def mono {R R' : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (hR : ∀ a b, R a b → R' a b)
    (c : HasCoupling R μ ν) :
    HasCoupling R' μ ν :=
  { c with rel_holds := fun p hp => hR p.1 p.2 (c.rel_holds p hp) }

/-- Swap the two marginals of a coupling, reversing the lifted relation. -/
noncomputable def symm {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (c : HasCoupling R μ ν) :
    HasCoupling (fun b a => R a b) ν μ where
  joint := c.joint.map Prod.swap
  marginal_fst := by
    rw [PMF.map_comp]
    change c.joint.map Prod.snd = ν
    exact c.marginal_snd
  marginal_snd := by
    rw [PMF.map_comp]
    change c.joint.map Prod.fst = μ
    exact c.marginal_fst
  rel_holds := by
    intro p hp
    simp only [PMF.support_map, Set.mem_image] at hp
    obtain ⟨q, hq, heq⟩ := hp
    rw [← heq]
    exact c.rel_holds q hq

/-- Functorial action: maps respecting the relation lift the coupling. -/
noncomputable def map {R : α → β → Prop} {R' : α' → β' → Prop}
    {μ : PMF α} {ν : PMF β}
    (c : HasCoupling R μ ν)
    (f : α → α') (g : β → β')
    (hR : ∀ a b, R a b → R' (f a) (g b)) :
    HasCoupling R' (μ.map f) (ν.map g) where
  joint := c.joint.map (fun p => (f p.1, g p.2))
  marginal_fst := by
    rw [PMF.map_comp]
    change c.joint.map (f ∘ Prod.fst) = μ.map f
    rw [← PMF.map_comp, c.marginal_fst]
  marginal_snd := by
    rw [PMF.map_comp]
    change c.joint.map (g ∘ Prod.snd) = ν.map g
    rw [← PMF.map_comp, c.marginal_snd]
  rel_holds := by
    intro p hp
    simp only [PMF.support_map, Set.mem_image] at hp
    obtain ⟨q, hq, heq⟩ := hp
    rw [← heq]
    exact hR q.1 q.2 (c.rel_holds q hq)

/-- If a coupling relation preserves an observation, the pushed-forward laws of
that observation are equal. -/
theorem map_eq_of_rel {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (c : HasCoupling R μ ν)
    (f : α → γ) (g : β → γ)
    (hR : ∀ a b, R a b → f a = g b) :
    μ.map f = ν.map g := by
  calc
    μ.map f = (c.joint.map Prod.fst).map f := by
      rw [c.marginal_fst]
    _ = c.joint.map (f ∘ Prod.fst) := by
      rw [PMF.map_comp]
    _ = c.joint.map (g ∘ Prod.snd) := by
      change
        c.joint.bind (fun p => PMF.pure (f p.1)) =
          c.joint.bind (fun p => PMF.pure (g p.2))
      apply ProbabilityMassFunction.bind_congr_on_support
      intro p hp
      rw [hR p.1 p.2 (c.rel_holds p hp)]
    _ = (c.joint.map Prod.snd).map g := by
      rw [PMF.map_comp]
    _ = ν.map g := by
      rw [c.marginal_snd]

/-- Nonempty version of `map_eq_of_rel`. -/
theorem map_eq_of_nonempty_rel {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (c : Nonempty (HasCoupling R μ ν))
    (f : α → γ) (g : β → γ)
    (hR : ∀ a b, R a b → f a = g b) :
    μ.map f = ν.map g := by
  rcases c with ⟨coupling⟩
  exact coupling.map_eq_of_rel f g hR

/-- If coupled prefixes have equal suffix kernels on related states, the
resulting bind laws are equal. -/
theorem bind_eq_of_rel {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (c : HasCoupling R μ ν)
    (k₁ : α → PMF γ) (k₂ : β → PMF γ)
    (hR : ∀ a b, R a b → k₁ a = k₂ b) :
    μ.bind k₁ = ν.bind k₂ := by
  calc
    μ.bind k₁ = (c.joint.map Prod.fst).bind k₁ := by
      rw [c.marginal_fst]
    _ = c.joint.bind (fun p => k₁ p.1) := by
      rw [PMF.bind_map]
      rfl
    _ = c.joint.bind (fun p => k₂ p.2) := by
      apply Math.ProbabilityMassFunction.bind_congr_on_support
      intro p hp
      exact hR p.1 p.2 (c.rel_holds p hp)
    _ = (c.joint.map Prod.snd).bind k₂ := by
      rw [PMF.bind_map]
      rfl
    _ = ν.bind k₂ := by
      rw [c.marginal_snd]

/-- Nonempty version of `bind_eq_of_rel`. -/
theorem bind_eq_of_nonempty_rel {R : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (c : Nonempty (HasCoupling R μ ν))
    (k₁ : α → PMF γ) (k₂ : β → PMF γ)
    (hR : ∀ a b, R a b → k₁ a = k₂ b) :
    μ.bind k₁ = ν.bind k₂ := by
  rcases c with ⟨coupling⟩
  exact coupling.bind_eq_of_rel k₁ k₂ hR

/-- Bind-coherence: if `R` lifts to a coupling of `μ`, `ν` and `R'`
lifts to couplings of `k₁ a`, `k₂ b` for every `R`-related pair, then
`R'` lifts to a coupling of the binds. The killer compositional
property of relation lifting. -/
noncomputable def bind {R : α → β → Prop} {R' : γ → δ → Prop}
    {μ : PMF α} {ν : PMF β} {k₁ : α → PMF γ} {k₂ : β → PMF δ}
    (c : HasCoupling R μ ν)
    (k : ∀ a b, R a b → HasCoupling R' (k₁ a) (k₂ b)) :
    HasCoupling R' (μ.bind k₁) (ν.bind k₂) := by
  classical
  let chooser : α × β → PMF (γ × δ) := fun p =>
    if h : R p.1 p.2 then (k p.1 p.2 h).joint
    else ProbabilityMassFunction.prod (k₁ p.1) (k₂ p.2)
  have h_fst : ∀ p, (chooser p).map Prod.fst = k₁ p.1 := by
    intro p
    by_cases h : R p.1 p.2
    · simp only [chooser, h, dif_pos]
      exact (k p.1 p.2 h).marginal_fst
    · simp only [chooser, h, dif_neg, not_false_eq_true]
      exact ProbabilityMassFunction.prod_map_fst _ _
  have h_snd : ∀ p, (chooser p).map Prod.snd = k₂ p.2 := by
    intro p
    by_cases h : R p.1 p.2
    · simp only [chooser, h, dif_pos]
      exact (k p.1 p.2 h).marginal_snd
    · simp only [chooser, h, dif_neg, not_false_eq_true]
      exact ProbabilityMassFunction.prod_map_snd _ _
  refine
    { joint := c.joint.bind chooser
      marginal_fst := ?_
      marginal_snd := ?_
      rel_holds := ?_ }
  · rw [PMF.map_bind]
    conv_lhs => enter [2, p]; rw [h_fst p]
    rw [show (fun p : α × β => k₁ p.1) = k₁ ∘ Prod.fst from rfl,
        ← PMF.bind_map, c.marginal_fst]
  · rw [PMF.map_bind]
    conv_lhs => enter [2, p]; rw [h_snd p]
    rw [show (fun p : α × β => k₂ p.2) = k₂ ∘ Prod.snd from rfl,
        ← PMF.bind_map, c.marginal_snd]
  · intro q hq
    rw [PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq'⟩ := hq
    have hRp : R p.1 p.2 := c.rel_holds p hp
    simp only [chooser, hRp, dif_pos] at hq'
    exact (k p.1 p.2 hRp).rel_holds q hq'

end HasCoupling

-- ============================================================================
-- Functional special case
-- ============================================================================

/-- Graph coupling: `μ` couples to its pushforward along `f`. -/
noncomputable def HasCoupling.ofMap (μ : PMF α) (f : α → β) :
    HasCoupling (fun a b => f a = b) μ (μ.map f) where
  joint := μ.map (fun a => (a, f a))
  marginal_fst := by
    rw [PMF.map_comp]
    change μ.map id = μ
    exact PMF.map_id μ
  marginal_snd := by
    rw [PMF.map_comp]
    rfl
  rel_holds := by
    intro p hp
    simp only [PMF.support_map, Set.mem_image] at hp
    obtain ⟨a, _ha, heq⟩ := hp
    rw [← heq]

/-- Diagonal coupling of a probability law with itself. -/
noncomputable def HasCoupling.refl (μ : PMF α) : HasCoupling Eq μ μ := by
  have h := HasCoupling.ofMap μ (id : α → α)
  rw [PMF.map_id] at h
  exact h

/-- Functional projection coupling: when `μ = ν.map f`, the relation
`fun a b => a = f b` lifts via the diagonal. -/
noncomputable def HasCoupling.ofProj {f : β → α} (ν : PMF β) :
    HasCoupling (fun a b => a = f b) (ν.map f) ν where
  joint := ν.map (fun b => (f b, b))
  marginal_fst := by
    rw [PMF.map_comp]; rfl
  marginal_snd := by
    rw [PMF.map_comp]
    change ν.map id = ν
    exact PMF.map_id ν
  rel_holds := by
    intro p hp
    simp only [PMF.support_map, Set.mem_image] at hp
    obtain ⟨b, _hb, heq⟩ := hp
    rw [← heq]

/-- Functional case bridge: `μ = ν.map f` is exactly the projection
coupling existing. -/
theorem hasCoupling_proj_iff_map_eq {f : β → α} {μ : PMF α} {ν : PMF β} :
    Nonempty (HasCoupling (fun a b => a = f b) μ ν) ↔ μ = ν.map f := by
  refine ⟨fun ⟨c⟩ => ?_, fun h => ?_⟩
  · calc μ
        = c.joint.map Prod.fst := c.marginal_fst.symm
      _ = c.joint.map (f ∘ Prod.snd) := by
          change c.joint.bind (fun p => PMF.pure p.1)
              = c.joint.bind (fun p => PMF.pure (f p.2))
          apply Math.ProbabilityMassFunction.bind_congr_on_support
          intro p hp
          rw [c.rel_holds p hp]
      _ = (c.joint.map Prod.snd).map f := by rw [← PMF.map_comp]
      _ = ν.map f := by rw [c.marginal_snd]
  · subst h
    exact ⟨HasCoupling.ofProj ν⟩

end Coupling
end Math
