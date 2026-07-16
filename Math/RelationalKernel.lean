/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.Coupling

/-!
# Relational rules for probabilistic kernels

`Kernel.Relates pre post k₁ k₂` is the coupling-based relational judgment for
discrete stochastic kernels: `pre`-related inputs produce output laws admitting
a coupling supported on `post`. It consolidates the pointwise coupling pattern
used by kernel bisimulation, trace simulation, and relational refinement.

The rules in this file are deliberately game-independent. Point masses,
sampling, deterministic maps, Kleisli composition, and pushforward of coupled
input laws all live here; bounded iteration is the invariant specialization in
`Math.PMFIter`.
-/

set_option autoImplicit false

namespace Math
namespace Probability
namespace Kernel

open Math.Coupling

variable {α β γ δ ε ζ : Type*}

/-- A coupling-based relational judgment on stochastic kernels. Every pair of
`pre`-related inputs must produce laws coupled by `post`. The coupling witness
is propositionally truncated because the judgment records existence, while
`HasCoupling` remains the witness-producing layer. -/
def Relates (pre : α → β → Prop) (post : γ → δ → Prop)
    (k₁ : Kernel α γ) (k₂ : Kernel β δ) : Prop :=
  ∀ a b, pre a b → Nonempty (HasCoupling post (k₁ a) (k₂ b))

namespace Relates

/-- Deterministic kernels relate outputs whenever their functions preserve the
input relation. -/
theorem ofFun {pre : α → β → Prop} {post : γ → δ → Prop}
    {f : α → γ} {g : β → δ}
    (h : ∀ a b, pre a b → post (f a) (g b)) :
    Relates pre post (Kernel.ofFun f) (Kernel.ofFun g) := by
  intro a b hab
  exact ⟨HasCoupling.pure (f a) (g b) (h a b hab)⟩

/-- A supplied coupling relates constant sampling kernels. -/
theorem const {pre : α → β → Prop} {post : γ → δ → Prop}
    {μ : PMF γ} {ν : PMF δ}
    (h : Nonempty (HasCoupling post μ ν)) :
    Relates pre post (fun _ => μ) (fun _ => ν) :=
  fun _ _ _ => h

/-- Every kernel relates to itself under equality. -/
theorem refl (k : Kernel α γ) : Relates Eq Eq k k := by
  intro a b hab
  subst b
  exact ⟨HasCoupling.refl (k a)⟩

/-- Strengthen the input relation and weaken the output relation. -/
theorem mono {pre pre' : α → β → Prop} {post post' : γ → δ → Prop}
    {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    (h : Relates pre post k₁ k₂)
    (hpre : ∀ a b, pre' a b → pre a b)
    (hpost : ∀ c d, post c d → post' c d) :
    Relates pre' post' k₁ k₂ := by
  intro a b hab
  obtain ⟨c⟩ := h a b (hpre a b hab)
  exact ⟨c.mono hpost⟩

/-- Reverse both the input and output relations. -/
theorem symm {pre : α → β → Prop} {post : γ → δ → Prop}
    {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    (h : Relates pre post k₁ k₂) :
    Relates (fun b a => pre a b) (fun d c => post c d) k₂ k₁ := by
  intro b a hab
  obtain ⟨c⟩ := h a b hab
  exact ⟨c.symm⟩

/-- Deterministic postprocessing transports a relational kernel judgment. -/
theorem map {pre : α → β → Prop} {post : γ → δ → Prop}
    {post' : ε → ζ → Prop} {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    (h : Relates pre post k₁ k₂) (f : γ → ε) (g : δ → ζ)
    (hpost : ∀ c d, post c d → post' (f c) (g d)) :
    Relates pre post' (fun a => (k₁ a).map f) (fun b => (k₂ b).map g) := by
  intro a b hab
  obtain ⟨c⟩ := h a b hab
  exact ⟨c.map f g hpost⟩

/-- Functional projection equations induce relational kernel judgments. -/
theorem of_map_eq {pre : α → β → Prop} {k₁ : Kernel α γ}
    {k₂ : Kernel β δ} (f : δ → γ)
    (h : ∀ a b, pre a b → k₁ a = (k₂ b).map f) :
    Relates pre (fun c d => c = f d) k₁ k₂ := by
  intro a b hab
  rw [h a b hab]
  exact ⟨HasCoupling.ofProj (k₂ b)⟩

/-- A relational judgment along a functional projection gives the corresponding
pointwise pushforward equation. -/
theorem map_eq_of_proj {pre : α → β → Prop} {k₁ : Kernel α γ}
    {k₂ : Kernel β δ} (f : δ → γ)
    (h : Relates pre (fun c d => c = f d) k₁ k₂)
    {a : α} {b : β} (hab : pre a b) :
    k₁ a = (k₂ b).map f :=
  hasCoupling_proj_iff_map_eq.mp (h a b hab)

/-- Relating outputs by a functional projection is exactly pointwise
pushforward equality. -/
theorem relates_proj_iff {pre : α → β → Prop} {k₁ : Kernel α γ}
    {k₂ : Kernel β δ} (f : δ → γ) :
    Relates pre (fun c d => c = f d) k₁ k₂ ↔
      ∀ a b, pre a b → k₁ a = (k₂ b).map f := by
  constructor
  · intro h a b hab
    exact map_eq_of_proj f h hab
  · exact of_map_eq f

/-- Relational Kleisli composition. An intermediate coupling supplies related
states, and `h₂` supplies a post-coupling for every such pair. -/
theorem comp {pre : α → β → Prop} {mid : γ → δ → Prop}
    {post : ε → ζ → Prop}
    {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    {l₁ : Kernel γ ε} {l₂ : Kernel δ ζ}
    (h₁ : Relates pre mid k₁ k₂) (h₂ : Relates mid post l₁ l₂) :
    Relates pre post (Kernel.comp k₁ l₁) (Kernel.comp k₂ l₂) := by
  intro a b hab
  obtain ⟨c⟩ := h₁ a b hab
  refine ⟨c.bind fun x y hxy => Classical.choice (h₂ x y hxy)⟩

/-- Coupled input laws remain coupled after pushforward through related
kernels. This is the distribution-level form of relational sequencing. -/
theorem pushforward {pre : α → β → Prop} {post : γ → δ → Prop}
    {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    (h : Relates pre post k₁ k₂) {μ : PMF α} {ν : PMF β}
    (hμν : Nonempty (HasCoupling pre μ ν)) :
    Nonempty (HasCoupling post (Kernel.pushforward k₁ μ)
      (Kernel.pushforward k₂ ν)) := by
  obtain ⟨c⟩ := hμν
  exact ⟨c.bind fun a b hab => Classical.choice (h a b hab)⟩

/-- If related outputs have equal observations, related inputs induce equal
observed output laws. -/
theorem map_eq_of_rel {pre : α → β → Prop} {post : γ → δ → Prop}
    {k₁ : Kernel α γ} {k₂ : Kernel β δ}
    (h : Relates pre post k₁ k₂) {a : α} {b : β} (hab : pre a b)
    (f : γ → ε) (g : δ → ε)
    (hpost : ∀ c d, post c d → f c = g d) :
    (k₁ a).map f = (k₂ b).map g := by
  obtain ⟨c⟩ := h a b hab
  exact c.map_eq_of_rel f g hpost

end Relates
end Kernel
end Probability
end Math
