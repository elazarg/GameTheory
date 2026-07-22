/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile
import GameTheory.Concepts.Classes.EvolutionaryStability

/-!
# Evolutionary Stability and Open Games

An ESS is stronger than equilibrium of the corresponding symmetric two-player
open-game shape: ordinary equilibrium captures the Nash/invasion condition,
while ESS additionally compares resident and mutant fitness after a tie.

This file gives the exact bridge and proves a bounded compositional result:
ESS is preserved by the independent additive product of two symmetric payoff
systems. It does not claim closure under arbitrary open-game sequential or
tensor composition.
-/

namespace OpenGames.Evolutionary

/-- The closed two-player simultaneous shape for a common strategy type. -/
abbrev SymmetricShape (S : Type) :=
  ShapeN (fun _ : Fin 2 => Unit) (fun _ => S)

/-- Both players use the same resident strategy. -/
def resident {S : Type} (s : S) : ∀ _ : Fin 2, Unit → S :=
  fun _ _ => s

/-- Symmetric fitness as the continuation of the two-player open shape. -/
abbrev symmetricContinuation {S : Type} (u : S → S → ℝ) :
    (Fin 2 → S) → Fin 2 → ℝ :=
  GameTheory.symmetricEU u

/-- Equilibrium of the symmetric open shape is exactly the Nash condition
appearing as the first clause of ESS. -/
theorem resident_isEquilibriumIn_iff_nashCondition {S : Type}
    (u : S → S → ℝ) (s : S) :
    (SymmetricShape S).IsEquilibriumIn (fun _ => ())
        (symmetricContinuation u) (resident s) ↔
      ∀ t, u s s ≥ u t s := by
  constructor
  · intro h t
    simpa [SymmetricShape, symmetricContinuation, resident, ShapeN,
      GameTheory.symmetricEU, Function.update] using h 0 t
  · intro h i t
    fin_cases i <;>
      simpa [SymmetricShape, symmetricContinuation, resident, ShapeN,
        GameTheory.symmetricEU, Function.update] using h t

/-- Every ESS selects an equilibrium of the corresponding symmetric open
shape. -/
theorem isEquilibriumIn_of_isESS {S : Type} {u : S → S → ℝ} {s : S}
    (h : GameTheory.IsESS u s) :
    (SymmetricShape S).IsEquilibriumIn (fun _ => ())
      (symmetricContinuation u) (resident s) :=
  (resident_isEquilibriumIn_iff_nashCondition u s).2 h.nash_condition

/-- Exact decomposition: ESS is open-game equilibrium plus the additional
tie-breaking invasion-stability clause. -/
theorem isESS_iff_isEquilibriumIn_and_stability {S : Type}
    (u : S → S → ℝ) (s : S) :
    GameTheory.IsESS u s ↔
      (SymmetricShape S).IsEquilibriumIn (fun _ => ())
          (symmetricContinuation u) (resident s) ∧
        ∀ t, u s s = u t s → s ≠ t → u s t > u t t := by
  rw [GameTheory.IsESS, resident_isEquilibriumIn_iff_nashCondition]

/-- Independent additive product of two symmetric fitness systems. -/
def productPayoff {S T : Type} (u : S → S → ℝ) (v : T → T → ℝ) :
    S × T → S × T → ℝ :=
  fun resident mutant =>
    u resident.1 mutant.1 + v resident.2 mutant.2

/-- ESS is closed under independent additive products. -/
theorem isESS_product {S T : Type} {u : S → S → ℝ}
    {v : T → T → ℝ} {s : S} {t : T}
    (hs : GameTheory.IsESS u s) (ht : GameTheory.IsESS v t) :
    GameTheory.IsESS (productPayoff u v) (s, t) := by
  constructor
  · rintro ⟨s', t'⟩
    have hsNash := hs.nash_condition s'
    have htNash := ht.nash_condition t'
    dsimp [productPayoff]
    linarith
  · rintro ⟨s', t'⟩ heq hne
    have hsNash := hs.nash_condition s'
    have htNash := ht.nash_condition t'
    have hsEq : u s s = u s' s := by
      dsimp [productPayoff] at heq
      linarith
    have htEq : v t t = v t' t := by
      dsimp [productPayoff] at heq
      linarith
    by_cases hss' : s = s'
    · have htt' : t ≠ t' := by
        intro h
        exact hne (Prod.ext hss' h)
      have htStable := ht.stability htEq htt'
      subst s'
      dsimp [productPayoff]
      linarith
    · have hsStable := hs.stability hsEq hss'
      by_cases htt' : t = t'
      · subst t'
        dsimp [productPayoff]
        linarith
      · have htStable := ht.stability htEq htt'
        dsimp [productPayoff]
        linarith

/-- The additive product ESS therefore selects equilibrium in the symmetric
open shape over product strategies. -/
theorem product_isEquilibriumIn_of_isESS {S T : Type}
    {u : S → S → ℝ} {v : T → T → ℝ} {s : S} {t : T}
    (hs : GameTheory.IsESS u s) (ht : GameTheory.IsESS v t) :
    (SymmetricShape (S × T)).IsEquilibriumIn (fun _ => ())
      (symmetricContinuation (productPayoff u v)) (resident (s, t)) :=
  isEquilibriumIn_of_isESS (isESS_product hs ht)

end OpenGames.Evolutionary
