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
- `WeaklyDominates.refl` -- weak dominance is reflexive
- `WeaklyDominates.trans` -- weak dominance is transitive
- `WeaklyDominates.instIsPreorder` -- weak dominance is a preorder
- `WeaklyStrictlyDominates` -- weak dominance with a strict witness
- `WeaklyStrictlyDominates.instIsStrictOrder` -- weak dominance with a strict
  witness is a strict order
- `StrictlyDominates.toWeaklyDominates` -- strict dominance implies weak dominance
- `StrictlyDominates.trans` -- strict dominance is transitive
- `StrictlyDominates.instIsStrictOrder` -- strong strict dominance is a strict
  order when profiles exist
- `IsDominant.weaklyDominates` -- a dominant strategy weakly dominates every alternative
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- Weak dominance is reflexive: every strategy weakly dominates itself.
    Derives from `GameForm.WeaklyDominatesFor.refl` via the EU bridge. -/
theorem WeaklyDominates.refl (who : ι) (s : G.Strategy who) :
    G.WeaklyDominates who s s := by
  intro σ
  exact le_refl _

/-- Weak dominance is transitive.
    Derives from `GameForm.WeaklyDominatesFor.trans` via the EU bridge. -/
theorem WeaklyDominates.trans {who : ι} {s t u : G.Strategy who}
    (h1 : G.WeaklyDominates who s t) (h2 : G.WeaklyDominates who t u) :
    G.WeaklyDominates who s u := by
  intro σ
  exact ge_trans (h1 σ) (h2 σ)

/-- Weak dominance is a preorder on a player's strategies. Antisymmetry is not
available in general: payoff-equivalent strategies can weakly dominate each
other. -/
instance WeaklyDominates.instIsPreorder (who : ι) :
    IsPreorder (G.Strategy who) (G.WeaklyDominates who) where
  refl := WeaklyDominates.refl who
  trans := fun _ _ _ => WeaklyDominates.trans

/-- Weak dominance with at least one strict witness. This is the textbook
"weak dominance" relation used by Monderer--Tennenholtz for undominated-strategy
rationality. It is distinct from `WeaklyDominates`, which is the reflexive
`≥`-everywhere preorder, and from `StrictlyDominates`, which is strict against
every opponent profile. -/
def WeaklyStrictlyDominates (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  G.WeaklyDominates who s t ∧
    ∃ σ : Profile G,
      G.eu (Function.update σ who s) who >
        G.eu (Function.update σ who t) who

theorem WeaklyStrictlyDominates.toWeaklyDominates {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyStrictlyDominates who s t) : G.WeaklyDominates who s t :=
  h.1

theorem WeaklyStrictlyDominates.strict_witness {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyStrictlyDominates who s t) :
    ∃ σ : Profile G,
      G.eu (Function.update σ who s) who >
        G.eu (Function.update σ who t) who :=
  h.2

theorem WeaklyStrictlyDominates.irrefl {who : ι} (s : G.Strategy who) :
    ¬ G.WeaklyStrictlyDominates who s s := by
  rintro ⟨_, σ, hσ⟩
  exact lt_irrefl _ hσ

theorem WeaklyStrictlyDominates.ne {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyStrictlyDominates who s t) : s ≠ t := by
  intro hst
  subst hst
  exact WeaklyStrictlyDominates.irrefl s h

theorem WeaklyStrictlyDominates.trans {who : ι} {s t u : G.Strategy who}
    (hst : G.WeaklyStrictlyDominates who s t)
    (htu : G.WeaklyStrictlyDominates who t u) :
    G.WeaklyStrictlyDominates who s u := by
  refine ⟨WeaklyDominates.trans hst.1 htu.1, ?_⟩
  obtain ⟨σ, hσ⟩ := hst.2
  refine ⟨σ, ?_⟩
  have htuσ := htu.1 σ
  linarith

theorem WeaklyStrictlyDominates.asymm {who : ι} {s t : G.Strategy who}
    (hst : G.WeaklyStrictlyDominates who s t) :
    ¬ G.WeaklyStrictlyDominates who t s := by
  intro hts
  exact WeaklyStrictlyDominates.irrefl s (WeaklyStrictlyDominates.trans hst hts)

/-- Weak dominance with a strict witness is a strict order. -/
instance WeaklyStrictlyDominates.instIsStrictOrder (who : ι) :
    IsStrictOrder (G.Strategy who) (G.WeaklyStrictlyDominates who) where
  irrefl := WeaklyStrictlyDominates.irrefl
  trans := fun _ _ _ => WeaklyStrictlyDominates.trans

/-- Strict dominance implies weak dominance.
    Derives from `GameForm.StrictlyDominatesFor.toWeaklyDominatesFor` via the EU bridge. -/
theorem StrictlyDominates.toWeaklyDominates {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) : G.WeaklyDominates who s t := by
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
theorem StrictlyDominates.toWeaklyStrictlyDominates
    (hprof : Nonempty (Profile G)) {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) :
    G.WeaklyStrictlyDominates who s t := by
  refine ⟨h.toWeaklyDominates, ?_⟩
  obtain ⟨σ⟩ := hprof
  exact ⟨σ, h σ⟩

/-- Strong strict dominance is a strict order on nonempty profile spaces. -/
instance StrictlyDominates.instIsStrictOrder (who : ι) [hprof : Nonempty (Profile G)] :
    IsStrictOrder (G.Strategy who) (G.StrictlyDominates who) where
  irrefl := StrictlyDominates.irrefl_of_nonempty hprof
  trans := fun _ _ _ => StrictlyDominates.trans

/-- A dominant strategy weakly dominates every alternative. -/
theorem IsDominant.weaklyDominates {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) (t : G.Strategy who) :
    G.WeaklyDominates who s t := by
  intro σ
  exact hdom σ t

end KernelGame
end GameTheory
