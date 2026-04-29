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

/-- Product coupling: when no relational constraint holds, pair samples
independently. Used as the "off-support" filler in `bind`. -/
private noncomputable def product (μ : PMF γ) (ν : PMF δ) : PMF (γ × δ) :=
  μ.bind (fun c => ν.map (fun d => (c, d)))

private theorem product_marginal_fst (μ : PMF γ) (ν : PMF δ) :
    (product μ ν).map Prod.fst = μ := by
  unfold product
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, c]
    rw [PMF.map_comp]
    rw [show (Prod.fst ∘ fun d : δ => (c, d)) = Function.const δ c from rfl]
    rw [PMF.map_const]
  rw [PMF.bind_pure]

private theorem product_marginal_snd (μ : PMF γ) (ν : PMF δ) :
    (product μ ν).map Prod.snd = ν := by
  unfold product
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, c]
    rw [PMF.map_comp]
    rw [show (Prod.snd ∘ fun d : δ => (c, d)) = (id : δ → δ) from rfl]
    rw [PMF.map_id]
  exact PMF.bind_const _ _

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
    else product (k₁ p.1) (k₂ p.2)
  have h_fst : ∀ p, (chooser p).map Prod.fst = k₁ p.1 := by
    intro p
    by_cases h : R p.1 p.2
    · simp only [chooser, h, dif_pos]
      exact (k p.1 p.2 h).marginal_fst
    · simp only [chooser, h, dif_neg, not_false_eq_true]
      exact product_marginal_fst _ _
  have h_snd : ∀ p, (chooser p).map Prod.snd = k₂ p.2 := by
    intro p
    by_cases h : R p.1 p.2
    · simp only [chooser, h, dif_pos]
      exact (k p.1 p.2 h).marginal_snd
    · simp only [chooser, h, dif_neg, not_false_eq_true]
      exact product_marginal_snd _ _
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
