/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin

/-!
# Approximate compatibility from playerwise certificate decomposition

This file isolates the sharp constant-one consequence of decomposing every
global Farkas balance into playerwise balances.

There are common constraints, indexed by `Facet`, and constraints belonging
to player `i`, indexed by `Constraint i`.  A playerwise balance may use all
common constraints but only that player's own constraints.  The decomposition
hypothesis preserves every player multiplier and splits each common-constraint
multiplier among the players.

If each player's subsystem is feasible after relaxing only the player
constraints by `ε`, then the whole coupled system is feasible with the same
relaxation `ε`.  There is no multiplicative loss.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {Facet Player : Type*} [Fintype Facet] [Fintype Player]
variable {Constraint : Player → Type*} [∀ i, Fintype (Constraint i)]
variable {n : ℕ}

/-- Rows of the coupled system: common facets or a player-specific
constraint. -/
abbrev CoupledRow (Facet Player : Type*) (Constraint : Player → Type*) :=
  Facet ⊕ Σ i, Constraint i

/-- Rows visible in one player's subsystem. -/
abbrev PlayerRow (Facet : Type*) {Player : Type*}
    (Constraint : Player → Type*) (i : Player) :=
  Facet ⊕ Constraint i

/-- The normal matrix of the coupled system. -/
def coupledNormal
    (facetNormal : Facet → Fin n → 𝕜)
    (playerNormal : ∀ i, Constraint i → Fin n → 𝕜) :
    CoupledRow Facet Player Constraint → Fin n → 𝕜
  | Sum.inl f => facetNormal f
  | Sum.inr ⟨i, a⟩ => playerNormal i a

/-- The right-hand side of the coupled system when every player constraint
is relaxed by `ε`; common facets remain exact. -/
def coupledRelaxedRhs
    (facetRhs : Facet → 𝕜)
    (playerRhs : ∀ i, Constraint i → 𝕜)
    (ε : 𝕜) :
    CoupledRow Facet Player Constraint → 𝕜
  | Sum.inl f => facetRhs f
  | Sum.inr ⟨i, a⟩ => playerRhs i a - ε

/-- The normal matrix of player `i`'s subsystem. -/
def playerSubsystemNormal
    (facetNormal : Facet → Fin n → 𝕜)
    (playerNormal : ∀ i, Constraint i → Fin n → 𝕜)
    (i : Player) :
    PlayerRow Facet Constraint i → Fin n → 𝕜
  | Sum.inl f => facetNormal f
  | Sum.inr a => playerNormal i a

/-- The right-hand side of player `i`'s subsystem, relaxing only that
player's constraints by `ε`. -/
def playerSubsystemRelaxedRhs
    (facetRhs : Facet → 𝕜)
    (playerRhs : ∀ i, Constraint i → 𝕜)
    (ε : 𝕜) (i : Player) :
    PlayerRow Facet Constraint i → 𝕜
  | Sum.inl f => facetRhs f
  | Sum.inr a => playerRhs i a - ε

/-- A nonnegative multiplier whose weighted normal is zero. -/
def IsNonnegativeBalance {Row : Type*} [Fintype Row]
    (normal : Row → Fin n → 𝕜) (u : Row → 𝕜) : Prop :=
  (∀ r, 0 ≤ u r) ∧
  (∀ j, ∑ r, u r * normal r j = 0)

/-- Every global nonnegative normal balance decomposes into playerwise
balances.  Player-specific multiplier coordinates are preserved exactly,
while the playerwise common-facet multipliers sum to the global ones. -/
def HasPlayerwiseBalanceDecomposition
    (facetNormal : Facet → Fin n → 𝕜)
    (playerNormal : ∀ i, Constraint i → Fin n → 𝕜) : Prop :=
  ∀ u : CoupledRow Facet Player Constraint → 𝕜,
    IsNonnegativeBalance (coupledNormal facetNormal playerNormal) u →
    ∃ v : ∀ i, PlayerRow Facet Constraint i → 𝕜,
      (∀ i, IsNonnegativeBalance
        (playerSubsystemNormal facetNormal playerNormal i) (v i)) ∧
      (∀ i a, v i (Sum.inr a) = u (Sum.inr ⟨i, a⟩)) ∧
      (∀ f, ∑ i, v i (Sum.inl f) = u (Sum.inl f))

/-- A feasible weak inequality system evaluates every nonnegative normal
balance to a nonpositive weighted right-hand side. -/
theorem weightedRhs_nonpos_of_feasible_balance
    {Row : Type*} [Fintype Row]
    (normal : Row → Fin n → 𝕜) (rhs : Row → 𝕜)
    (hfeasible : IsFeasible normal rhs) (u : Row → 𝕜)
    (hu : IsNonnegativeBalance normal u) :
    ∑ r, u r * rhs r ≤ 0 := by
  obtain ⟨x, hx⟩ := hfeasible
  rcases hu with ⟨hu_nonneg, hu_balance⟩
  calc
    ∑ r, u r * rhs r ≤ ∑ r, u r * rowEval normal r x := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (hx r) (hu_nonneg r)
    _ = ∑ j, (∑ r, u r * normal r j) * x j := by
      simp only [rowEval, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by simp [hu_balance]

/-- Multiplier mass on the inequalities that receive the uniform
relaxation.  Common-facet multiplier mass is intentionally excluded. -/
def coupledRelaxedMultiplierMass
    (u : CoupledRow Facet Player Constraint → 𝕜) : 𝕜 :=
  ∑ i, ∑ a, u (Sum.inr ⟨i, a⟩)

/-- Total relaxed-inequality mass of a playerwise family of multipliers. -/
def playerwiseRelaxedMultiplierMass
    (v : ∀ i, PlayerRow Facet Constraint i → 𝕜) : 𝕜 :=
  ∑ i, ∑ a, v i (Sum.inr a)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype Facet] in
/-- Preserving the player coordinates makes relaxation mass additive with
exact constant one. -/
theorem coupledRelaxedMultiplierMass_eq_playerwise
    (u : CoupledRow Facet Player Constraint → 𝕜)
    (v : ∀ i, PlayerRow Facet Constraint i → 𝕜)
    (hplayer : ∀ i a, v i (Sum.inr a) = u (Sum.inr ⟨i, a⟩)) :
    coupledRelaxedMultiplierMass u =
      playerwiseRelaxedMultiplierMass v := by
  unfold coupledRelaxedMultiplierMass playerwiseRelaxedMultiplierMass
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [hplayer i a]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Exact multiplier bookkeeping: playerwise decomposition preserves the
weighted relaxed right-hand side, including its relaxation mass. -/
theorem coupledWeightedRhs_eq_sum_playerwise
    (facetRhs : Facet → 𝕜)
    (playerRhs : ∀ i, Constraint i → 𝕜)
    (ε : 𝕜)
    (u : CoupledRow Facet Player Constraint → 𝕜)
    (v : ∀ i, PlayerRow Facet Constraint i → 𝕜)
    (hplayer : ∀ i a, v i (Sum.inr a) = u (Sum.inr ⟨i, a⟩))
    (hfacet : ∀ f, ∑ i, v i (Sum.inl f) = u (Sum.inl f)) :
    (∑ r, u r * coupledRelaxedRhs facetRhs playerRhs ε r) =
      ∑ i, ∑ r, v i r * playerSubsystemRelaxedRhs
        facetRhs playerRhs ε i r := by
  rw [Fintype.sum_sum_type]
  simp only [coupledRelaxedRhs]
  rw [Fintype.sum_sigma]
  have hcommon :
      (∑ f, u (Sum.inl f) * facetRhs f) =
        ∑ i, ∑ f, v i (Sum.inl f) * facetRhs f := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [← Finset.sum_mul, hfacet f]
  have hplayers :
      (∑ i, ∑ a, u (Sum.inr ⟨i, a⟩) *
        (playerRhs i a - ε)) =
        ∑ i, ∑ a, v i (Sum.inr a) * (playerRhs i a - ε) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    rw [hplayer i a]
  calc
    (∑ f, u (Sum.inl f) * facetRhs f) +
        ∑ i, ∑ a, u (Sum.inr ⟨i, a⟩) *
          (playerRhs i a - ε) =
        (∑ i, ∑ f, v i (Sum.inl f) * facetRhs f) +
          ∑ i, ∑ a, v i (Sum.inr a) *
            (playerRhs i a - ε) := congrArg₂ (· + ·) hcommon hplayers
    _ = ∑ i, ((∑ f, v i (Sum.inl f) * facetRhs f) +
        ∑ a, v i (Sum.inr a) * (playerRhs i a - ε)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, ∑ r, v i r *
        playerSubsystemRelaxedRhs facetRhs playerRhs ε i r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sum_type]
      rfl

/-- **Sharp constant-one approximate compatibility.**  If every global
nonnegative normal balance decomposes playerwise, and every player's
subsystem is feasible with relaxation `ε`, then the coupled system is
feasible with exactly the same relaxation. -/
theorem coupledRelaxed_feasible_of_playerwise
    (facetNormal : Facet → Fin n → 𝕜)
    (facetRhs : Facet → 𝕜)
    (playerNormal : ∀ i, Constraint i → Fin n → 𝕜)
    (playerRhs : ∀ i, Constraint i → 𝕜)
    (ε : 𝕜)
    (hdecompose :
      HasPlayerwiseBalanceDecomposition facetNormal playerNormal)
    (hplayerFeasible : ∀ i, IsFeasible
      (playerSubsystemNormal facetNormal playerNormal i)
      (playerSubsystemRelaxedRhs facetRhs playerRhs ε i)) :
    IsFeasible
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs ε) := by
  by_contra hinfeasible
  obtain ⟨u, hu_nonneg, hu_balance, hu_positive⟩ :=
    (theorem_of_alternative
      (coupledNormal facetNormal playerNormal)
      (coupledRelaxedRhs facetRhs playerRhs ε)).mp hinfeasible
  obtain ⟨v, hv_balance, hv_player, hv_facet⟩ :=
    hdecompose u ⟨hu_nonneg, hu_balance⟩
  have hv_nonpos :
      ∀ i, ∑ r, v i r *
        playerSubsystemRelaxedRhs facetRhs playerRhs ε i r ≤ 0 := by
    intro i
    exact weightedRhs_nonpos_of_feasible_balance
      (playerSubsystemNormal facetNormal playerNormal i)
      (playerSubsystemRelaxedRhs facetRhs playerRhs ε i)
      (hplayerFeasible i) (v i) (hv_balance i)
  have hsum_nonpos :
      ∑ i, ∑ r, v i r *
        playerSubsystemRelaxedRhs facetRhs playerRhs ε i r ≤ 0 :=
    Finset.sum_nonpos fun i _ => hv_nonpos i
  rw [← coupledWeightedRhs_eq_sum_playerwise
    facetRhs playerRhs ε u v hv_player hv_facet] at hsum_nonpos
  exact (not_lt_of_ge hsum_nonpos) hu_positive

end LinearAlgebra
end Math
