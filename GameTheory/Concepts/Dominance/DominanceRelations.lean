/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.PrefPreorderProperties
import Math.Probability

/-!
# GameTheory.Concepts.Dominance.DominanceRelations

Structural properties of dominance relations on `KernelGame`.

Provides:
- `WeaklyDominatesReflexive` -- the weak-dominance preorder (≥ everywhere)
- `WeaklyDominatesReflexive.refl` -- reflexivity
- `WeaklyDominatesReflexive.trans` -- transitivity
- `WeaklyDominatesReflexive.instIsPreorder` -- preorder instance
- `WeaklyDominatesWithStrictWitness` -- ≥ everywhere and > somewhere
- `WeaklyDominatesWithStrictWitness.instIsStrictOrder` -- weak dominance with a strict
  witness is a strict order
- `StrictlyDominates.toWeaklyDominatesReflexive` -- strict dominance implies
  reflexive weak dominance
- `StrictlyDominates.trans` -- strict dominance is transitive
- `StrictlyDominates.instIsStrictOrder` -- strong strict dominance is a strict
  order when profiles exist
- `IsDominant.weaklyDominatesReflexive` -- a dominant strategy reflexively
  weakly dominates every alternative
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- Weak dominance is reflexive: every strategy weakly dominates itself.
    Derives from `GameForm.WeaklyDominatesReflexiveFor.refl` via the EU bridge. -/
theorem WeaklyDominatesReflexive.refl (who : ι) (s : G.Strategy who) :
    G.WeaklyDominatesReflexive who s s := by
  intro σ
  exact le_refl _

/-- Weak dominance is transitive.
    Derives from `GameForm.WeaklyDominatesReflexiveFor.trans` via the EU bridge. -/
theorem WeaklyDominatesReflexive.trans {who : ι} {s t u : G.Strategy who}
    (h1 : G.WeaklyDominatesReflexive who s t)
    (h2 : G.WeaklyDominatesReflexive who t u) :
    G.WeaklyDominatesReflexive who s u := by
  intro σ
  exact ge_trans (h1 σ) (h2 σ)

/-- Weak dominance is a preorder on a player's strategies. Antisymmetry is not
available in general: payoff-equivalent strategies can weakly dominate each
other. -/
instance WeaklyDominatesReflexive.instIsPreorder (who : ι) :
    IsPreorder (G.Strategy who) (G.WeaklyDominatesReflexive who) where
  refl := WeaklyDominatesReflexive.refl who
  trans := fun _ _ _ => WeaklyDominatesReflexive.trans

/-- Weak dominance with at least one strict witness. This is the textbook
"weak dominance" relation used by Monderer--Tennenholtz for undominated-strategy
rationality. It is distinct from `WeaklyDominatesReflexive`, which is the reflexive
`≥`-everywhere preorder, and from `StrictlyDominates`, which is strict against
every opponent profile. -/
def WeaklyDominatesWithStrictWitness (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  G.WeaklyDominatesReflexive who s t ∧
    ∃ σ : Profile G,
      G.eu (Function.update σ who s) who >
        G.eu (Function.update σ who t) who

theorem WeaklyDominatesWithStrictWitness.toWeaklyDominatesReflexive
    {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyDominatesWithStrictWitness who s t) :
    G.WeaklyDominatesReflexive who s t :=
  h.1

theorem WeaklyDominatesWithStrictWitness.strict_witness
    {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyDominatesWithStrictWitness who s t) :
    ∃ σ : Profile G,
      G.eu (Function.update σ who s) who >
        G.eu (Function.update σ who t) who :=
  h.2

theorem WeaklyDominatesWithStrictWitness.irrefl
    {who : ι} (s : G.Strategy who) :
    ¬ G.WeaklyDominatesWithStrictWitness who s s := by
  rintro ⟨_, σ, hσ⟩
  exact lt_irrefl _ hσ

theorem WeaklyDominatesWithStrictWitness.ne {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyDominatesWithStrictWitness who s t) : s ≠ t := by
  intro hst
  subst hst
  exact WeaklyDominatesWithStrictWitness.irrefl s h

theorem WeaklyDominatesWithStrictWitness.trans
    {who : ι} {s t u : G.Strategy who}
    (hst : G.WeaklyDominatesWithStrictWitness who s t)
    (htu : G.WeaklyDominatesWithStrictWitness who t u) :
    G.WeaklyDominatesWithStrictWitness who s u := by
  refine ⟨WeaklyDominatesReflexive.trans hst.1 htu.1, ?_⟩
  obtain ⟨σ, hσ⟩ := hst.2
  refine ⟨σ, ?_⟩
  have htuσ := htu.1 σ
  linarith

theorem WeaklyDominatesWithStrictWitness.asymm
    {who : ι} {s t : G.Strategy who}
    (hst : G.WeaklyDominatesWithStrictWitness who s t) :
    ¬ G.WeaklyDominatesWithStrictWitness who t s := by
  intro hts
  exact WeaklyDominatesWithStrictWitness.irrefl s
    (WeaklyDominatesWithStrictWitness.trans hst hts)

/-- Weak dominance with a strict witness is a strict order. -/
instance WeaklyDominatesWithStrictWitness.instIsStrictOrder (who : ι) :
    IsStrictOrder (G.Strategy who) (G.WeaklyDominatesWithStrictWitness who) where
  irrefl := WeaklyDominatesWithStrictWitness.irrefl
  trans := fun _ _ _ => WeaklyDominatesWithStrictWitness.trans

/-- Strict dominance implies reflexive weak dominance.
    Derives from
    `GameForm.StrictlyDominatesFor.toWeaklyDominatesReflexiveFor` via the EU bridge. -/
theorem StrictlyDominates.toWeaklyDominatesReflexive
    {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) :
    G.WeaklyDominatesReflexive who s t := by
  intro σ
  exact le_of_lt (h σ)

/-- Strict dominance is transitive. -/
theorem StrictlyDominates.trans {who : ι} {s t u : G.Strategy who}
    (h1 : G.StrictlyDominates who s t) (h2 : G.StrictlyDominates who t u) :
    G.StrictlyDominates who s u := by
  intro σ
  have hs := h1 σ
  have ht := h2 σ
  linarith

/-- Strong strict dominance is irreflexive as soon as the game has at least one
profile. Without that hypothesis `∀ σ, _` is vacuous in an empty profile space. -/
theorem StrictlyDominates.irrefl_of_nonempty (hprof : Nonempty (Profile G))
    {who : ι} (s : G.Strategy who) :
    ¬ G.StrictlyDominates who s s := by
  rintro h
  obtain ⟨σ⟩ := hprof
  exact lt_irrefl _ (h σ)

/-- Strong strict dominance is asymmetric on nonempty profile spaces. -/
theorem StrictlyDominates.asymm_of_nonempty (hprof : Nonempty (Profile G))
    {who : ι} {s t : G.Strategy who} (hst : G.StrictlyDominates who s t) :
    ¬ G.StrictlyDominates who t s := by
  intro hts
  exact StrictlyDominates.irrefl_of_nonempty hprof s
    (StrictlyDominates.trans hst hts)

/-- Strong strict dominance implies weak dominance with a strict witness when
there is at least one profile to witness strictness. -/
theorem StrictlyDominates.toWeaklyDominatesWithStrictWitness
    (hprof : Nonempty (Profile G)) {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) :
    G.WeaklyDominatesWithStrictWitness who s t := by
  refine ⟨h.toWeaklyDominatesReflexive, ?_⟩
  obtain ⟨σ⟩ := hprof
  exact ⟨σ, h σ⟩

/-- Strong strict dominance is a strict order on nonempty profile spaces. -/
instance StrictlyDominates.instIsStrictOrder (who : ι) [hprof : Nonempty (Profile G)] :
    IsStrictOrder (G.Strategy who) (G.StrictlyDominates who) where
  irrefl := StrictlyDominates.irrefl_of_nonempty hprof
  trans := fun _ _ _ => StrictlyDominates.trans

/-- A dominant strategy weakly dominates every alternative. -/
theorem IsDominant.weaklyDominatesReflexive {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) (t : G.Strategy who) :
    G.WeaklyDominatesReflexive who s t := by
  intro σ
  exact hdom σ t

end KernelGame
end GameTheory
