/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.ApproximateCompatibility
import Mathlib.Data.Real.Basic

/-!
# Extracting a player-owned charge from a coupled Farkas balance

A genuinely mixed Farkas balance need not decompose into playerwise
balances.  It nevertheless has a direct constructive use.  At every point
satisfying the common constraints, its weighted certificate value is no
larger than the weighted sum of the player-constraint deficits.

After normalizing the total player multiplier mass to one, one fixed
player-constraint deficit is therefore at least the full certificate value.
In a Bellman system this constraint names an actual player and an actual
forward deviation; no formal reversal or mixed-owner stochastic flow is
needed.

This result does not assert simultaneous continuation compatibility and it
does not force the continuation point onto a proper face.  It supplies the
response branch when compatibility fails.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

noncomputable section

set_option autoImplicit false

variable {Facet Player : Type*}
  [Fintype Facet] [Fintype Player]
variable {Constraint : Player → Type*}
  [∀ i, Fintype (Constraint i)]
variable {n : ℕ}

/-- Violation of one player constraint at a candidate continuation point.
It is positive exactly when that constraint is not satisfied. -/
def playerConstraintDeficit
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (x : Fin n → ℝ) (edge : Σ i, Constraint i) : ℝ :=
  playerRhs edge.1 edge.2 -
    rowEval (playerNormal edge.1) edge.2 x

/-- At a point satisfying every common constraint, a coupled nonnegative
balance charges no more than the weighted sum of the player deficits. -/
theorem coupledWeightedRhs_le_sum_playerConstraintDeficit
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (u : CoupledRow Facet Player Constraint → ℝ)
    (hu :
      IsNonnegativeBalance
        (coupledNormal facetNormal playerNormal) u)
    (x : Fin n → ℝ)
    (hfacet :
      ∀ f, facetRhs f ≤ rowEval facetNormal f x) :
    (∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row) ≤
      ∑ edge : Σ i, Constraint i,
        u (Sum.inr edge) *
          playerConstraintDeficit playerNormal playerRhs x edge := by
  have hfacetWeighted :
      (∑ f, u (Sum.inl f) * facetRhs f) ≤
        ∑ f, u (Sum.inl f) * rowEval facetNormal f x := by
    apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_left (hfacet f) (hu.1 (Sum.inl f))
  have hbalanceEval :
      (∑ f, u (Sum.inl f) * rowEval facetNormal f x) +
          ∑ edge : Σ i, Constraint i,
            u (Sum.inr edge) *
              rowEval
                (playerNormal edge.1) edge.2 x =
        0 := by
    calc
      (∑ f, u (Sum.inl f) * rowEval facetNormal f x) +
          ∑ edge : Σ i, Constraint i,
            u (Sum.inr edge) *
              rowEval
                (playerNormal edge.1) edge.2 x =
          ∑ row, u row *
            rowEval
              (coupledNormal facetNormal playerNormal) row x := by
                rw [Fintype.sum_sum_type]
                congr 1
      _ = ∑ j,
          (∑ row,
            u row *
              coupledNormal facetNormal playerNormal row j) * x j := by
            simp only [rowEval, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro row _
            ring
      _ = 0 := by simp [hu.2]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [coupledRelaxedRhs, sub_zero]
  calc
    (∑ f, u (Sum.inl f) * facetRhs f) +
          ∑ i, ∑ a, u (Sum.inr ⟨i, a⟩) * playerRhs i a ≤
        (∑ f, u (Sum.inl f) * rowEval facetNormal f x) +
          ∑ i, ∑ a,
            u (Sum.inr ⟨i, a⟩) * playerRhs i a := by
              gcongr
    _ = ∑ edge : Σ i, Constraint i,
          u (Sum.inr edge) *
            playerConstraintDeficit playerNormal playerRhs x edge := by
          rw [Fintype.sum_sigma]
          simp only [playerConstraintDeficit]
          have hbalanceEval' :
              (∑ f, u (Sum.inl f) * rowEval facetNormal f x) =
                -∑ i, ∑ a,
                  u (Sum.inr ⟨i, a⟩) *
                    rowEval (playerNormal i) a x := by
            rw [Fintype.sum_sigma] at hbalanceEval
            linarith
          rw [hbalanceEval']
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          ring

/-- A normalized nonnegative weighted average is bounded above by one of
its entries. -/
theorem exists_ge_of_nonnegative_weights_sum_one
    {Edge : Type*} [Fintype Edge] [Nonempty Edge]
    (mass value : Edge → ℝ)
    (hmass : ∀ edge, 0 ≤ mass edge)
    (hsum : ∑ edge, mass edge = 1)
    (lower : ℝ)
    (hlower : lower ≤ ∑ edge, mass edge * value edge) :
    ∃ edge, lower ≤ value edge := by
  classical
  obtain ⟨edge, -, hedge⟩ :=
    Finset.exists_max_image Finset.univ value Finset.univ_nonempty
  refine ⟨edge, hlower.trans ?_⟩
  calc
    (∑ other, mass other * value other) ≤
        ∑ other, mass other * value edge := by
          apply Finset.sum_le_sum
          intro other _
          exact mul_le_mul_of_nonneg_left
            (hedge other (Finset.mem_univ other)) (hmass other)
    _ = value edge * ∑ other, mass other := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro other _
          ring
    _ = value edge := by rw [hsum, mul_one]

variable [Nonempty (Σ i, Constraint i)]

/-- **Mixed-circuit response extraction.**

Normalize the total multiplier mass on player constraints to one.  At every
candidate continuation satisfying the common facets, some actual
player-owned constraint has deficit at least the complete coupled
certificate value.  In particular, a positive mixed obstruction produces a
positive forward response rather than a mixed-owner occupation flow. -/
theorem exists_playerConstraintDeficit_ge_coupledWeightedRhs
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (u : CoupledRow Facet Player Constraint → ℝ)
    (hu :
      IsNonnegativeBalance
        (coupledNormal facetNormal playerNormal) u)
    (hnormalized : coupledRelaxedMultiplierMass u = 1)
    (x : Fin n → ℝ)
    (hfacet :
      ∀ f, facetRhs f ≤ rowEval facetNormal f x) :
    ∃ i, ∃ a,
      (∑ row, u row *
          coupledRelaxedRhs facetRhs playerRhs 0 row) ≤
        playerRhs i a -
          rowEval (playerNormal i) a x := by
  let mass : (Σ i, Constraint i) → ℝ :=
    fun edge => u (Sum.inr edge)
  let value : (Σ i, Constraint i) → ℝ :=
    playerConstraintDeficit playerNormal playerRhs x
  have hmass : ∀ edge, 0 ≤ mass edge :=
    fun edge => hu.1 (Sum.inr edge)
  have hsum : ∑ edge, mass edge = 1 := by
    simpa only [mass, coupledRelaxedMultiplierMass,
      Fintype.sum_sigma] using hnormalized
  obtain ⟨edge, hedge⟩ :=
    exists_ge_of_nonnegative_weights_sum_one
      mass value hmass hsum
      (∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row)
      (coupledWeightedRhs_le_sum_playerConstraintDeficit
        facetNormal facetRhs playerNormal playerRhs u hu x hfacet)
  exact ⟨edge.1, edge.2, hedge⟩

/-- Positive coupled certificate value yields a strictly violated
player-owned constraint. -/
theorem exists_positive_playerConstraintDeficit
    (facetNormal : Facet → Fin n → ℝ)
    (facetRhs : Facet → ℝ)
    (playerNormal : ∀ i, Constraint i → Fin n → ℝ)
    (playerRhs : ∀ i, Constraint i → ℝ)
    (u : CoupledRow Facet Player Constraint → ℝ)
    (hu :
      IsNonnegativeBalance
        (coupledNormal facetNormal playerNormal) u)
    (hnormalized : coupledRelaxedMultiplierMass u = 1)
    (hpositive :
      0 < ∑ row, u row *
        coupledRelaxedRhs facetRhs playerRhs 0 row)
    (x : Fin n → ℝ)
    (hfacet :
      ∀ f, facetRhs f ≤ rowEval facetNormal f x) :
    ∃ i, ∃ a,
      0 < playerRhs i a -
        rowEval (playerNormal i) a x := by
  obtain ⟨i, a, hdeficit⟩ :=
    exists_playerConstraintDeficit_ge_coupledWeightedRhs
      facetNormal facetRhs playerNormal playerRhs
      u hu hnormalized x hfacet
  exact ⟨i, a, hpositive.trans_le hdeficit⟩

end

end LinearAlgebra
end Math
