/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile

/-!
# Sequential Open-Game Theorems

Plain sequential composition checks a later decision only at its realized
history.  `ShapeS.conditioned` makes the stronger, subgame-conditioned
predicate explicit: the follower must be optimal after every possible first
move.  Its actual correspondence to EFG subgame perfection lives in
`Languages/Bridges/OpenGame_EFG.lean`.
-/

namespace OpenGames.ShapeS

/-- The subgame-conditioned two-stage shape.

It has the same strategies and play as `ShapeS`, but follower optimality is
required at every counterfactual history. -/
def conditioned (A B : Type) : OpenGame Unit Unit (A × B) (ℝ × ℝ) where
  Strategy := A × (A → B)
  play σ _ := (σ.1, σ.2 σ.1)
  coplay _ _ _ := ()
  IsEquilibriumIn _ k σ :=
    (∀ a, (k (a, σ.2 a)).1 ≤ (k (σ.1, σ.2 σ.1)).1) ∧
    (∀ a b, (k (a, b)).2 ≤ (k (a, σ.2 a)).2)

/-- The explicit pointwise inequalities carried by the conditioned shape.

This is a shape-local characterization, not the EFG definition of subgame
perfection.  See `conditioned_isEquilibriumIn_iff_efg_isSubgamePerfectEq` for
the substantive bridge theorem. -/
def IsConditionedEquilibrium {A B : Type} (k : A × B → ℝ × ℝ)
    (σ : A × (A → B)) : Prop :=
  (∀ a, (k (a, σ.2 a)).1 ≤ (k (σ.1, σ.2 σ.1)).1) ∧
  (∀ a b, (k (a, b)).2 ≤ (k (a, σ.2 a)).2)

/-- Unfolding the conditioning operator gives its pointwise inequalities. -/
theorem conditioned_isEquilibriumIn_iff_isConditionedEquilibrium {A B : Type}
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (conditioned A B).IsEquilibriumIn () k σ ↔
      IsConditionedEquilibrium k σ :=
  Iff.rfl

/-- Subgame-conditioned equilibrium implies equilibrium of plain sequential
composition. -/
theorem conditioned_implies_plain {A B : Type}
    (k : A × B → ℝ × ℝ) (σ : A × (A → B))
    (h : (conditioned A B).IsEquilibriumIn () k σ) :
    (ShapeS A B).IsEquilibriumIn () k σ := by
  exact ⟨h.1, h.2 σ.1⟩

/-- Exact gap theorem: upgrading a plain equilibrium requires precisely the
off-path follower inequalities omitted by sequential composition. -/
theorem conditioned_iff_plain_and_offPath {A B : Type}
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (conditioned A B).IsEquilibriumIn () k σ ↔
      (ShapeS A B).IsEquilibriumIn () k σ ∧
        ∀ a, a ≠ σ.1 → ∀ b, (k (a, b)).2 ≤ (k (a, σ.2 a)).2 := by
  constructor
  · intro h
    exact ⟨conditioned_implies_plain k σ h, fun a _ha => h.2 a⟩
  · rintro ⟨hplain, hoff⟩
    refine ⟨hplain.1, ?_⟩
    intro a b
    by_cases ha : a = σ.1
    · subst a
      exact hplain.2 b
    · exact hoff a ha b

end OpenGames.ShapeS
